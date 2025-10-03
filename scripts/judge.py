#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
from typing import Any, Dict


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Triage simulation results")
    parser.add_argument("--reports", type=pathlib.Path, default=pathlib.Path("reports"))
    parser.add_argument("--sim", type=pathlib.Path)
    parser.add_argument("--out", type=pathlib.Path)
    return parser.parse_args()


def load_sim_report(path: pathlib.Path) -> Dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"Simulation report {path} not found. Run `make report` first.")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Simulation report {path} is not valid JSON: {exc}") from exc


def _failure_text(failure: dict[str, object]) -> str:
    fields = (
        failure.get("line", ""),
        failure.get("message", ""),
        failure.get("detail", ""),
        failure.get("hint", ""),
    )
    return " ".join(str(field) for field in fields if field)


def decide(data: dict[str, Any]) -> tuple[dict[str, Any], str]:
    status = data.get("status")
    failures = data.get("failures", [])

    if status == "pass":
        return {"action": "proceed", "reason": "All requirements satisfied", "triage": "ok"}, "ok"

    if not failures:
        return {"action": "investigate", "reason": "Unknown failure (no details)"}, "generic"

    failing_rids = sorted({entry.get("req", "unknown") for entry in failures})
    triage = "generic"

    signed_suspect = False
    reg_comb_suspect = False
    overflow_hit = False
    arith_width_hit = False

    for failure in failures:
        text = _failure_text(failure).lower()
        rid = failure.get("req")

        if isinstance(rid, str) and (rid.endswith("RESET-001") or "reset" in text):
            triage = "reset_path"
            break

        handshake_hit = (
            "handshake" in text
            or ("ready" in text and "valid" in text)
            or "protocol" in text
        )
        if handshake_hit:
            triage = "handshake"
            break

        if any(
            re.search(pattern, text)
            for pattern in (
                r"\bsigned\b",
                r"\bunsigned\b",
                r"sign-extend",
                r"sign extend",
                r"sign-extension",
                r"two's complement",
                r"twos complement",
            )
        ):
            signed_suspect = True

        if (
            "latch" in text
            or "combinational" in text
            or "registered" in text
            or ("always_ff" in text and "always_comb" in text)
            or "latency" in text
        ):
            reg_comb_suspect = True

        if isinstance(rid, str) and (rid.endswith("OVERFLOW-020") or "overflow" in text):
            overflow_hit = True

        if ("off" in text and "by" in text) or (
            "width" in text and "expected" in text
        ):
            arith_width_hit = True

    if triage == "generic":
        if signed_suspect:
            triage = "signedness"
        elif reg_comb_suspect:
            triage = "reg_vs_comb"
        elif overflow_hit:
            triage = "overflow"
        elif arith_width_hit:
            triage = "arith_width"

    if triage == "reset_path":
        decision = {"action": "fix_rtl", "reason": "Reset behaviour broken"}
    elif triage == "handshake":
        decision = {"action": "fix_rtl", "reason": "Protocol handshake violations detected"}
    elif triage == "signedness":
        decision = {"action": "fix_rtl", "reason": "Signed/unsigned intent appears inconsistent"}
    elif triage == "reg_vs_comb":
        decision = {
            "action": "fix_rtl",
            "reason": "Mismatch between registered and combinational behaviour",
        }
    elif triage == "overflow":
        decision = {"action": "fix_rtl", "reason": f"Overflow issues detected in {failing_rids}"}
    elif triage == "arith_width":
        decision = {"action": "fix_rtl", "reason": f"Width mismatches detected in {failing_rids}"}
    else:
        decision = {"action": "fix_rtl", "reason": f"Functional mismatches observed in {failing_rids}"}

    return decision, triage


def main() -> None:
    args = parse_args()
    reports_dir = args.reports
    sim_path = args.sim or (reports_dir / "sim_report.json")
    out_path = args.out or (reports_dir / "judge.json")

    sim_data = load_sim_report(sim_path)
    decision, triage = decide(sim_data)

    hints = {
        "reset_path": "RTL: verify always_ff reset branch drives y <= '0 when !rst_n; TB: confirm reset deassert timing matches spec.",
        "handshake": "Ensure ready/valid handshake holds VALID until READY and that response signaling meets the protocol; align assertions and scoreboards.",
        "signedness": "Check signed vs unsigned intent across ports, internal math, and TB checks; add $signed casts or declare logic signed where needed.",
        "reg_vs_comb": "Confirm spec'd latency: adjust always_ff/always_comb boundaries or TB expectations so registered vs combinational behaviour matches.",
        "overflow": "Check wrap logic: ensure addition is modulo WIDTH and assertions reflect acceptance.",
        "arith_width": "Review operand widths/casts; consider widening intermediate sums and tightening assertions.",
        "generic": "Review DUT vs acceptance checks in verification/reqs.yml and update tests/assertions as needed.",
        "ok": "",
    }

    if decision.get("action") == "proceed":
        decision.setdefault("triage", triage)
    else:
        decision["triage"] = triage
        decision["hint"] = hints.get(triage, hints["generic"])

    decision["schema"] = 1

    if sim_data.get("status") != "pass" and sim_data.get("failures"):
        first_failure = sim_data.get("failures", [{}])[0]
        label = str(first_failure.get("req", "failure"))
        wave_cmd = [
            "python3",
            "scripts/wave_slice.py",
            "--reports",
            str(reports_dir),
            "--log",
            str(reports_dir / "sim.log"),
            "--label",
            label,
        ]
        wave_run = subprocess.run(wave_cmd, capture_output=True, text=True)
        if wave_run.returncode == 0:
            note = wave_run.stdout.strip() or wave_run.stderr.strip()
            if note:
                decision.setdefault("artifacts", {})["wave_slice"] = note

    reports_dir.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(decision, indent=2), encoding="utf-8")
    print(json.dumps(decision, indent=2))


if __name__ == "__main__":
    main()
