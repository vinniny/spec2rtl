#!/usr/bin/env python3
"""Generate verification artifacts from docs/spec.md."""
from __future__ import annotations

import json
import pathlib
import re
from typing import Any, Dict, List, Tuple

try:
    import yaml
except ModuleNotFoundError as exc:  # pragma: no cover - explicit dependency hint
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc

SPEC_PATH = pathlib.Path("docs/spec.md")
OUT_DIR = pathlib.Path("verification")
REQS_PATH = OUT_DIR / "reqs.yml"
PLAN_PATH = OUT_DIR / "test_plan.md"
SVAS_PATH = OUT_DIR / "svas.sv"

LIBRARY_BY_TAG = {
    "reset": "lib/reset.svh",
    "handshake": "lib/handshake.svh",
    "onehot": "lib/onehot.svh",
    "gray": "lib/gray_counter.svh",
    "latency": "lib/latency.svh",
}

IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def load_existing_metadata() -> Dict[str, Dict[str, Any]]:
    if not REQS_PATH.exists():
        return {}
    try:
        data = yaml.safe_load(REQS_PATH.read_text(encoding="utf-8"))
    except yaml.YAMLError:
        return {}
    existing: Dict[str, Dict[str, Any]] = {}
    for entry in data.get("requirements", []):
        text = entry.get("text")
        if isinstance(text, str):
            existing[text] = entry
    return existing


def merge_metadata(
    generated: Dict[str, Any],
    existing: Dict[str, Any],
) -> Dict[str, Any]:
    merged = dict(generated)
    if not existing:
        return merged

    for key in ("map", "params", "notes"):
        if key in existing:
            current = merged.get(key)
            if isinstance(current, dict) and isinstance(existing[key], dict):
                combined = dict(current)
                combined.update(existing[key])
                merged[key] = combined
            else:
                merged[key] = existing[key]

    if "tags" in existing:
        generated_tags = set(map(str, merged.get("tags", [])))
        existing_tags = {str(tag) for tag in existing["tags"]}
        merged["tags"] = sorted(existing_tags | generated_tags)

    return merged


def map_entry_expr(entry: Any, default: str) -> str:
    if isinstance(entry, dict):
        expr = entry.get("expr")
        if isinstance(expr, str) and expr:
            return expr
        name = entry.get("name")
        if isinstance(name, str) and name:
            return name
    elif isinstance(entry, str) and entry:
        return entry
    return default


def map_entry_port(entry: Any) -> Tuple[str, str] | None:
    if isinstance(entry, dict):
        name = entry.get("name")
        if not isinstance(name, str) or not name:
            return None
        dtype = entry.get("type", "logic")
        if not isinstance(dtype, str) or not dtype:
            dtype = "logic"
        return name, dtype
    if isinstance(entry, str) and IDENT_RE.fullmatch(entry):
        return entry, "logic"
    return None


def parse_module_name(text: str) -> str:
    match = re.search(r"^-\s*Module:\s*(?P<name>[A-Za-z_][A-Za-z0-9_]*)", text, re.MULTILINE)
    return match.group("name") if match else "top"


def extract_requirements(text: str) -> List[str]:
    """Return unique requirement sentences that contain key verbs."""
    keyword_re = re.compile(r"\b(shall|must|should|corner)\b", re.IGNORECASE)
    requirements: List[str] = []
    seen: set[str] = set()
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if keyword_re.search(line):
            normalized = line.lstrip("-* ")
            if normalized not in seen:
                seen.add(normalized)
                requirements.append(normalized)
    return requirements


def classify_requirement(req_text: str) -> Dict[str, object]:
    lower = req_text.lower()
    tags: List[str] = []
    acceptance = {"check": req_text}
    stimuli: Dict[str, object] = {}
    map_signals: Dict[str, Any] = {}
    params: Dict[str, Any] = {}

    if any(word in lower for word in ("sum", "add", "plus")):
        tags.extend(["functional", "arithmetic"])
        acceptance["check"] = "y equals a + b (modulo width)"
        stimuli["directed"] = [
            {"a": 0, "b": 0},
            {"a": 255, "b": 1},
            {"a": 170, "b": 85},
        ]
        stimuli["random"] = {
            "count": 64,
            "constraints": {"a": [0, 255], "b": [0, 255]},
        }
        if any(word in lower for word in ("wrap", "overflow")):
            tags.append("overflow")
    if any(word in lower for word in ("reset", "rst")):
        if "reset" not in tags:
            tags.append("reset")
        acceptance["check"] = "y == 0 during and immediately after synchronous active-low reset"
        stimuli.setdefault("directed", []).append(
            {"sequence": "rst_n low for 2 cycles, release, observe y"}
        )
    handshake_hit = "handshake" in lower or ("ready" in lower and "valid" in lower)
    if handshake_hit and "handshake" not in tags:
        tags.append("handshake")
        map_signals.setdefault("req", "req_valid")
        map_signals.setdefault("ack", "req_ready")
        params.setdefault("min", 1)
        params.setdefault("max", 1)
    if any(word in lower for word in ("one-hot", "onehot", "one hot")) and "onehot" not in tags:
        tags.append("onehot")
        map_signals.setdefault("signal", "ctrl_state")
    if ("gray" in lower or "grey" in lower) and "gray" not in tags:
        if "counter" in lower or "code" in lower:
            tags.append("gray")
            map_signals.setdefault("signal", "gray_state")
    if "latency" in lower or ("within" in lower and "cycle" in lower):
        if "latency" not in tags:
            tags.append("latency")
        params.setdefault("min", 1)
        params.setdefault("max", 1)
    if not tags:
        tags.append("functional")

    entry: Dict[str, object] = {
        "text": req_text,
        "tags": tags,
        "acceptance": acceptance,
    }
    if map_signals:
        entry["map"] = map_signals
    if params:
        entry["params"] = params
    if "arithmetic" in tags:
        entry["cov_targets"] = {"line": 0.85, "toggle": 0.70}
    elif "reset" in tags:
        entry["cov_targets"] = {"line": 0.05, "toggle": 0.0}
    else:
        entry["cov_targets"] = {"line": 0.50, "toggle": 0.50}
    if stimuli:
        entry["stimuli"] = stimuli
    return entry


def write_reqs(
    module: str,
    requirements: List[str],
    existing_meta: Dict[str, Dict[str, Any]],
) -> List[Dict[str, object]]:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload: Dict[str, object] = {
        "version": 1,
        "dut": module,
        "requirements": [],
    }
    enriched: List[Dict[str, object]] = []
    for idx, requirement in enumerate(requirements, start=1):
        req_info = classify_requirement(requirement)
        prior = existing_meta.get(requirement, {})
        req_info = merge_metadata(req_info, prior)
        req_info["id"] = f"R{idx}"
        enriched.append(req_info)
        payload["requirements"].append(req_info)
    REQS_PATH.write_text(yaml.dump(payload, sort_keys=False), encoding="utf-8")
    return enriched


def write_plan(requirements: List[Dict[str, object]]) -> None:
    lines = ["# Test Plan", ""]
    for req in requirements:
        rid = req["id"]
        text = req["text"]
        lines.append(f"- **{rid}**: {text}")
        directed = req.get("stimuli", {}).get("directed", [])  # type: ignore[arg-type]
        if directed:
            lines.append(f"  - Directed stimulus: {json.dumps(directed)}")
        else:
            lines.append("  - Directed stimulus: TBD")
        random = req.get("stimuli", {}).get("random")  # type: ignore[arg-type]
        if random:
            lines.append(f"  - Random stimulus: {json.dumps(random)}")
        else:
            lines.append("  - Random stimulus: TBD")
        lines.append("")
    PLAN_PATH.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def format_literal(value: Any, default: int) -> str:
    if isinstance(value, (int, float)):
        return str(int(value))
    if isinstance(value, str):
        stripped = value.strip()
        if stripped:
            return stripped
    return str(default)


def build_property(req: Dict[str, object]) -> tuple[List[str], set[str]]:
    rid = req["id"]
    text = req["text"].lower()
    tags = {tag.lower() for tag in req.get("tags", [])}
    mapping = req.get("map") if isinstance(req.get("map"), dict) else {}
    params = req.get("params") if isinstance(req.get("params"), dict) else {}
    body: List[str] = []
    libraries: set[str] = set()

    if "reset" in tags:
        libraries.add(LIBRARY_BY_TAG["reset"])
        body.extend(
            [
                f"`ASSERT_RESET_CLEARS(p_{rid}_rst_hold, clk, rst_n, y);",
                f"`ASSERT_RESET_RELEASE(p_{rid}_rst_release, clk, rst_n, y);",
            ]
        )

    if "handshake" in tags:
        libraries.add(LIBRARY_BY_TAG["handshake"])
        req_expr = map_entry_expr(mapping.get("req"), "req_valid")
        ack_expr = map_entry_expr(mapping.get("ack"), "req_ready")
        min_literal = format_literal(params.get("min"), 1)
        try:
            min_default_for_max = int(min_literal, 0)
        except (ValueError, TypeError):
            min_default_for_max = 1
        max_literal = format_literal(params.get("max"), min_default_for_max)
        body.append(
            f"`SVA_REQ_ACK(p_{rid}_req_ack, {req_expr}, {ack_expr}, {min_literal}, {max_literal});"
        )

    if "onehot" in tags:
        libraries.add(LIBRARY_BY_TAG["onehot"])
        signal_expr = map_entry_expr(mapping.get("signal"), "ctrl_state")
        body.append(f"`SVA_ONEHOT(p_{rid}_onehot, {signal_expr});")

    if "gray" in tags:
        libraries.add(LIBRARY_BY_TAG["gray"])
        signal_expr = map_entry_expr(mapping.get("signal"), "gray_state")
        body.append(f"`SVA_GRAY(p_{rid}_gray, {signal_expr});")

    if "latency" in tags:
        libraries.add(LIBRARY_BY_TAG["latency"])
        trig_expr = map_entry_expr(mapping.get("trig"), "1'b1")
        cond_expr = map_entry_expr(mapping.get("cond"), "1'b1")
        min_literal = format_literal(params.get("min"), 1)
        try:
            min_default_for_max = int(min_literal, 0)
        except (ValueError, TypeError):
            min_default_for_max = 1
        max_literal = format_literal(params.get("max"), min_default_for_max)
        body.append(
            f"`SVA_LATENCY(p_{rid}_latency, {trig_expr}, {cond_expr}, {min_literal}, {max_literal});"
        )

    if any(word in text for word in ("sum", "add", "plus")):
        body.extend(
            [
                f"property p_{rid};",
                "  @(posedge clk) disable iff (!rst_n)",
                "    y == a + b;",
                "endproperty",
                f"a_{rid}: assert property (p_{rid}) else $error(\"[{rid}] y != a + b\");",
            ]
        )

    if not body:
        body.extend(
            [
                f"property p_{rid};",
                "  @(posedge clk) disable iff (!rst_n)",
                "    1'b1 |-> 1'b1;",
                "endproperty",
                f"// TODO: refine assertion for {rid}",
                f"a_{rid}: assert property (p_{rid});",
            ]
        )

    return body, libraries


def write_svas(requirements: List[Dict[str, object]]) -> None:
    include_files: set[str] = set()
    payload: List[tuple[Dict[str, object], List[str]]] = []

    for req in requirements:
        prop_lines, libs = build_property(req)
        include_files.update(libs)
        payload.append((req, prop_lines))

    ports: List[tuple[str, str]] = [
        ("clk", "logic"),
        ("rst_n", "logic"),
        ("a", "logic [WIDTH-1:0]"),
        ("b", "logic [WIDTH-1:0]"),
        ("y", "logic [WIDTH-1:0]"),
    ]
    seen_ports = {name for name, _ in ports}
    for req, _ in payload:
        mapping = req.get("map") if isinstance(req.get("map"), dict) else {}
        for value in mapping.values():
            port_spec = map_entry_port(value)
            if port_spec is None:
                continue
            name, dtype = port_spec
            if name not in seen_ports:
                ports.append((name, dtype))
                seen_ports.add(name)

    lines = [
        "// Starter SVA assertions generated from docs/spec.md",
        "`default_nettype none",
    ]
    for include in sorted(include_files):
        lines.append(f"`include \"{include}\"")
    if include_files:
        lines.append("")
    lines.append("/* verilator lint_off DECLFILENAME */")
    lines.append("module svas #(parameter int WIDTH = 8) (")
    for idx, (name, dtype) in enumerate(ports):
        suffix = "," if idx < len(ports) - 1 else ""
        lines.append(f"    input {dtype} {name}{suffix}")
    lines.append(");")
    lines.append("")
    for req, prop_lines in payload:
        lines.append(f"  // {req['id']}: {req['text']}")
        if prop_lines:
            lines.extend(f"  {line}" for line in prop_lines)
        else:
            lines.append(f"  // TODO: refine assertion for {req['id']}")
        lines.append("")
    lines.append("endmodule")
    lines.append("/* verilator lint_on DECLFILENAME */")
    lines.append("`default_nettype wire")
    SVAS_PATH.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def main() -> None:
    if not SPEC_PATH.exists():
        raise SystemExit(f"Spec file {SPEC_PATH} not found")
    text = SPEC_PATH.read_text(encoding="utf-8")
    module = parse_module_name(text)
    raw_requirements = extract_requirements(text)
    existing_meta = load_existing_metadata()
    enriched_requirements = write_reqs(module, raw_requirements, existing_meta)
    write_plan(enriched_requirements)
    write_svas(enriched_requirements)
    print("Generated:")
    print(f"  {REQS_PATH}")
    print(f"  {PLAN_PATH}")
    print(f"  {SVAS_PATH}")


if __name__ == "__main__":
    main()
