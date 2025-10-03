#!/usr/bin/env python3
"""Execute mutation test campaigns using generated mutants."""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
from typing import Any, Dict, List

from json_schemas import SchemaError, validate_mutation_summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run mutation testing across generated mutants")
    parser.add_argument("--mutants", type=pathlib.Path, default=pathlib.Path("mutants"))
    parser.add_argument("--reports", type=pathlib.Path, default=pathlib.Path("reports/mutation"))
    parser.add_argument("--make", type=str, default="make")
    parser.add_argument("--target", type=str, default="mutant_report")
    parser.add_argument("--seed", type=int, default=None, help="Seed override when executing mutants")
    parser.add_argument("--cwd", type=pathlib.Path, default=pathlib.Path("."))
    return parser.parse_args()


def load_manifest(mutants_dir: pathlib.Path) -> List[Dict[str, Any]]:
    manifest_path = mutants_dir / "manifest.json"
    if not manifest_path.exists():
        return []
    try:
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Failed to parse mutant manifest {manifest_path}: {exc}") from exc
    return data.get("mutations", []) if isinstance(data, dict) else []


def run_mutant(mutant: Dict[str, Any], args: argparse.Namespace) -> Dict[str, Any]:
    mutant_id = mutant.get("id", pathlib.Path(mutant.get("path", "mutant.sv")).stem)
    out_dir = args.reports / mutant_id
    out_dir.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    env["MUTANT_RTL"] = mutant.get("path", "")
    env["MUTANT_OUT"] = str(out_dir)
    if mutant.get("source"):
        env["MUTANT_SOURCE"] = mutant.get("source")
    if args.seed is not None:
        env["SEED"] = str(args.seed)

    result = subprocess.run([args.make, args.target], cwd=args.cwd, env=env, check=False)
    status = "error" if result.returncode not in (0, 1) else None

    sim_report = out_dir / "sim_report.json"
    sim_status = "missing"
    if sim_report.exists():
        try:
            sim_data = json.loads(sim_report.read_text(encoding="utf-8"))
            sim_status = sim_data.get("status", "unknown")
        except json.JSONDecodeError:
            sim_status = "corrupt"

    if status is None:
        if sim_status == "fail":
            status = "killed"
        elif sim_status == "pass":
            status = "survived"
        else:
            status = "unknown"
    elif status == "error" and sim_status == "fail":
        status = "killed"

    return {
        "id": mutant_id,
        "status": status,
        "sim_status": sim_status,
        "reports": str(out_dir),
        "mutation": mutant.get("mutation"),
        "description": mutant.get("description"),
    }


def main() -> None:
    args = parse_args()
    mutants = load_manifest(args.mutants)
    if not mutants:
        print("No mutants to run")
        return

    results = [run_mutant(mutant, args) for mutant in mutants]
    killed = sum(1 for r in results if r["status"] == "killed")
    survived = sum(1 for r in results if r["status"] == "survived")
    kill_rate = (killed / len(results)) * 100 if results else 0.0

    summary = {
        "schema": 1,
        "total": len(results),
        "killed": killed,
        "survived": survived,
        "kill_rate_percent": round(kill_rate, 2),
        "results": results,
    }

    args.reports.mkdir(parents=True, exist_ok=True)
    summary_path = args.reports / "summary.json"
    try:
        validate_mutation_summary(summary)
    except SchemaError as exc:
        raise SystemExit(f"mutation summary schema validation failed: {exc}") from exc

    summary_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Wrote {summary_path}")

    if survived > 0:
        raise SystemExit(f"Mutation testing incomplete: {survived} survivors")


if __name__ == "__main__":
    main()
