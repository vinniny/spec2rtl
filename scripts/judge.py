#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import re

REPORTS_DIR = pathlib.Path("reports")
SIM_REPORT = REPORTS_DIR / "sim_report.json"
JUDGE_REPORT = REPORTS_DIR / "judge.json"

if not SIM_REPORT.exists():
    raise SystemExit(f"Simulation report {SIM_REPORT} not found. Run `make report` first.")

sim_data = json.loads(SIM_REPORT.read_text(encoding="utf-8"))


def _failure_text(failure: dict[str, object]) -> str:
    fields = (
        failure.get("line", ""),
        failure.get("message", ""),
        failure.get("detail", ""),
        failure.get("hint", ""),
    )
    return " ".join(str(field) for field in fields if field)


def decide(data: dict) -> tuple[dict, str]:
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

        if rid == "R2" or "reset" in text:
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

        if rid == "R3" or "wrap" in text or "overflow" in text:
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
        decision = {"action": "fix_rtl", "reason": "Reset behaviour broken (R2 fails)"}
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
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    JUDGE_REPORT.write_text(json.dumps(decision, indent=2), encoding="utf-8")
    print(json.dumps(decision, indent=2))


if __name__ == "__main__":
    main()
