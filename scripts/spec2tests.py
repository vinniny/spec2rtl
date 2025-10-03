#!/usr/bin/env python3
"""Generate verification artifacts from docs/spec.md."""
from __future__ import annotations

import argparse
import json
import pathlib
import re
from dataclasses import dataclass
from typing import Any, Dict, List, Sequence, Tuple

try:
    import yaml
except ModuleNotFoundError as exc:  # pragma: no cover - explicit dependency hint
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc


@dataclass(frozen=True)
class Requirement:
    rid: str
    summary: str
    tags: Tuple[str, ...]
    priority: str


def _sv_ident(value: str, *, prefix_if_digit: str = "p_") -> str:
    """Return a SystemVerilog-safe identifier derived from *value*."""
    cleaned = re.sub(r"[^A-Za-z0-9_]", "_", str(value))
    cleaned = re.sub(r"__+", "_", cleaned).strip("_")
    if not cleaned:
        cleaned = f"{prefix_if_digit}id"
    if cleaned[0].isdigit():
        cleaned = f"{prefix_if_digit}{cleaned}"
    return cleaned


LIBRARY_BY_TAG = {
    "reset": "lib/reset.svh",
    "handshake": "lib/handshake.svh",
    "onehot": "lib/onehot.svh",
    "gray": "lib/gray_counter.svh",
    "latency": "lib/latency.svh",
}

IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
REQ_LINE_RE = re.compile(
    r"^[-*]\s*\[(?P<id>[A-Z0-9\-]+)]\s*(?:\((?P<meta>[^)]*)\))?\s*(?P<text>.+)$"
)
REQ_ID_RE = re.compile(r"^R-[A-Z0-9]+-\d{3}$")
ALLOWED_PRIORITIES = {"must", "should"}


def load_existing_metadata(reqs_path: pathlib.Path) -> Dict[str, Dict[str, Any]]:
    if not reqs_path.exists():
        return {}
    try:
        data = yaml.safe_load(reqs_path.read_text(encoding="utf-8"))
    except yaml.YAMLError:
        return {}
    existing: Dict[str, Dict[str, Any]] = {}
    for entry in data.get("requirements", []):
        rid = entry.get("id")
        if isinstance(rid, str):
            existing[rid] = entry
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
        generated_tags = {str(tag).lower() for tag in merged.get("tags", [])}
        existing_tags = {str(tag).lower() for tag in existing["tags"]}
        merged["tags"] = sorted(existing_tags | generated_tags)

    if "priority" in existing and "priority" not in merged:
        merged["priority"] = existing["priority"]

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


def parse_meta(meta: str) -> tuple[list[str], str]:
    if not meta:
        return [], ""

    tags: list[str] = []
    priority: str = ""

    for segment in (part.strip() for part in meta.split(";")):
        if not segment:
            continue
        if ":" not in segment:
            raise SystemExit(f"Requirement metadata must be key: value; got '{segment}'")
        key, value = (piece.strip().lower() for piece in segment.split(":", 1))
        if key == "tags":
            tags = [tag.strip().lower() for tag in value.split(",") if tag.strip()]
        elif key == "priority":
            priority = value.strip().lower()
        else:
            raise SystemExit(f"Unsupported requirement metadata key '{key}'")

    return tags, priority


def parse_requirement_line(raw_line: str) -> Requirement:
    match = REQ_LINE_RE.match(raw_line.strip())
    if not match:
        raise SystemExit(f"Requirement line is malformed: '{raw_line.strip()}'")

    rid = match.group("id").strip()
    if not REQ_ID_RE.fullmatch(rid):
        raise SystemExit(
            f"Requirement id '{rid}' must match pattern 'R-XXX-###' (letters/digits in XXX)"
        )

    tags, priority = parse_meta(match.group("meta") or "")
    if not tags:
        raise SystemExit(f"Requirement {rid} missing tags metadata")
    if not priority:
        raise SystemExit(f"Requirement {rid} missing priority metadata")
    if priority not in ALLOWED_PRIORITIES:
        allowed = ", ".join(sorted(ALLOWED_PRIORITIES))
        raise SystemExit(f"Requirement {rid} priority '{priority}' not in {{{allowed}}}")

    summary = match.group("text").strip()
    if not summary:
        raise SystemExit(f"Requirement {rid} missing descriptive text")

    if not re.search(r"\b(shall|must|should)\b", summary, re.IGNORECASE):
        raise SystemExit(f"Requirement {rid} text must include shall/must/should: '{summary}'")

    tag_tuple = tuple(dict.fromkeys(tags))
    return Requirement(rid=rid, summary=summary, tags=tag_tuple, priority=priority)


def extract_requirements(text: str) -> List[Requirement]:
    in_requirements = False
    parsed: list[Requirement] = []
    for raw_line in text.splitlines():
        stripped = raw_line.strip()
        lower = stripped.lower()
        if lower.startswith("## requirements"):
            in_requirements = True
            continue
        if in_requirements and lower.startswith("## "):
            break
        if not in_requirements:
            continue
        if not stripped or not stripped.startswith(('-','*')):
            continue
        requirement = parse_requirement_line(stripped)
        parsed.append(requirement)

    if not parsed:
        raise SystemExit("Spec contains no requirements in the expected format")

    seen_ids: set[str] = set()
    for req in parsed:
        if req.rid in seen_ids:
            raise SystemExit(f"Duplicate requirement id detected: {req.rid}")
        seen_ids.add(req.rid)

    return parsed


def build_stimuli_from_text(req: Requirement) -> dict[str, Any]:
    lower = req.summary.lower()
    stimuli: dict[str, Any] = {}
    directed: list[dict[str, Any]] = []

    if "reset" in req.tags:
        directed.append({"sequence": "drive rst_n low for 2 cycles, release, observe outputs"})

    if any(word in lower for word in ("sum", "add", "plus")):
        directed.extend(
            [
                {"a": 0, "b": 0},
                {"a": 255, "b": 1},
                {"a": 170, "b": 85},
            ]
        )
        stimuli["random"] = {
            "count": 128,
            "constraints": {"a": [0, 255], "b": [0, 255]},
        }

    if directed:
        stimuli["directed"] = directed

    return stimuli


def write_reqs(
    module: str,
    requirements: Sequence[Requirement],
    existing_meta: Dict[str, Dict[str, Any]],
    reqs_path: pathlib.Path,
) -> List[Dict[str, object]]:
    reqs_dir = reqs_path.parent
    reqs_dir.mkdir(parents=True, exist_ok=True)

    payload: Dict[str, Any] = {
        "version": 1,
        "dut": module,
        "requirements": [],
    }
    enriched: List[Dict[str, object]] = []

    for req in requirements:
        entry: Dict[str, Any] = {
            "id": req.rid,
            "text": req.summary,
            "tags": list(req.tags),
            "priority": req.priority,
            "acceptance": {"check": req.summary},
        }

        stimuli = build_stimuli_from_text(req)
        if stimuli:
            entry["stimuli"] = stimuli

        if "reset" in req.tags:
            entry.setdefault("cov_targets", {"line": 0.10, "toggle": 0.0})
        elif "handshake" in req.tags or "latency" in req.tags:
            entry.setdefault("cov_targets", {"line": 0.60, "toggle": 0.50})
        elif "arithmetic" in req.tags:
            entry.setdefault("cov_targets", {"line": 0.85, "toggle": 0.70})

        prior = existing_meta.get(req.rid, {})
        entry = merge_metadata(entry, prior)
        enriched.append(entry)
        payload["requirements"].append(entry)

    reqs_path.write_text(yaml.dump(payload, sort_keys=False), encoding="utf-8")
    return enriched


def write_plan(requirements: List[Dict[str, object]], plan_path: pathlib.Path) -> None:
    lines = ["# Test Plan", ""]
    for req in requirements:
        rid = req["id"]
        text = req["text"]
        tags = ", ".join(req.get("tags", [])) or "n/a"
        priority = req.get("priority", "n/a")
        lines.append(f"- **{rid}** ({priority}; tags: {tags}): {text}")
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
    plan_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def format_literal(value: Any, default: int) -> str:
    if isinstance(value, (int, float)):
        return str(int(value))
    if isinstance(value, str):
        stripped = value.strip()
        if stripped:
            return stripped
    return str(default)


def build_property(req: Dict[str, object]) -> tuple[List[str], set[str]]:
    rid_display = req["id"]
    rid_sanitized = _sv_ident(rid_display)
    text = req["text"].lower()
    tags = {tag.lower() for tag in req.get("tags", [])}
    mapping = req.get("map") if isinstance(req.get("map"), dict) else {}
    params = req.get("params") if isinstance(req.get("params"), dict) else {}
    body: List[str] = []
    libraries: set[str] = set()

    def name(*parts: str) -> str:
        return _sv_ident("_".join(str(part) for part in parts if part))

    if "reset" in tags:
        libraries.add(LIBRARY_BY_TAG["reset"])
        body.extend(
            [
                f"`ASSERT_RESET_CLEARS({name('p', rid_sanitized, 'rst_hold')}, clk, rst_n, y);",
                f"`ASSERT_RESET_RELEASE({name('p', rid_sanitized, 'rst_release')}, clk, rst_n, y);",
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
            f"`SVA_REQ_ACK({name('p', rid_sanitized, 'req_ack')}, {req_expr}, {ack_expr}, {min_literal}, {max_literal});"
        )

    if "onehot" in tags:
        libraries.add(LIBRARY_BY_TAG["onehot"])
        signal_expr = map_entry_expr(mapping.get("signal"), "ctrl_state")
        body.append(f"`SVA_ONEHOT({name('p', rid_sanitized, 'onehot')}, {signal_expr});")

    if "gray" in tags:
        libraries.add(LIBRARY_BY_TAG["gray"])
        signal_expr = map_entry_expr(mapping.get("signal"), "gray_state")
        body.append(f"`SVA_GRAY({name('p', rid_sanitized, 'gray')}, {signal_expr});")

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
            f"`SVA_LATENCY({name('p', rid_sanitized, 'latency')}, {trig_expr}, {cond_expr}, {min_literal}, {max_literal});"
        )

    if any(word in text for word in ("sum", "add", "plus")) or "arithmetic" in tags:
        prop_name = name('p', rid_sanitized)
        assert_label = name('a', rid_sanitized)
        body.extend(
            [
                f"property {prop_name};",
                "  @(posedge clk) disable iff (!rst_n)",
                "    y == a + b;",
                "endproperty",
                f"{assert_label}: assert property ({prop_name}) else $error(\"[{rid_display}] y != a + b\");",
            ]
        )

    if not body:
        prop_name = name('p', rid_sanitized)
        assert_label = name('a', rid_sanitized)
        body.extend(
            [
                f"property {prop_name};",
                "  @(posedge clk) disable iff (!rst_n)",
                "    1'b1 |-> 1'b1;",
                "endproperty",
                f"// TODO: refine assertion for {rid_display}",
                f"{assert_label}: assert property ({prop_name});",
            ]
        )

    return body, libraries


def write_svas(requirements: List[Dict[str, object]], svas_path: pathlib.Path) -> None:
    include_files: set[str] = {"lib/base.svh"}
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
    svas_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate verification artifacts from a spec")
    parser.add_argument("--spec", type=pathlib.Path, default=pathlib.Path("docs/spec.md"))
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("verification"))
    parser.add_argument("--svas", type=pathlib.Path)
    parser.add_argument("--plan", type=pathlib.Path)
    parser.add_argument("--reqs", type=pathlib.Path)
    args = parser.parse_args()

    out_dir = args.out
    if args.svas is None:
        args.svas = out_dir / "svas.sv"
    if args.plan is None:
        args.plan = out_dir / "test_plan.md"
    if args.reqs is None:
        args.reqs = out_dir / "reqs.yml"

    return args


def main() -> None:
    args = parse_args()
    spec_path: pathlib.Path = args.spec
    if not spec_path.exists():
        raise SystemExit(f"Spec file {spec_path} not found")
    text = spec_path.read_text(encoding="utf-8")
    module = parse_module_name(text)
    requirements = extract_requirements(text)
    existing_meta = load_existing_metadata(args.reqs)
    enriched_requirements = write_reqs(module, requirements, existing_meta, args.reqs)
    write_plan(enriched_requirements, args.plan)
    write_svas(enriched_requirements, args.svas)
    print("Generated:")
    print(f"  {args.reqs}")
    print(f"  {args.plan}")
    print(f"  {args.svas}")


if __name__ == "__main__":
    main()
