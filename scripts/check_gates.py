#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
from typing import Any, Dict, Tuple

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Evaluate coverage gates against policies")
    parser.add_argument("--policies", type=pathlib.Path, default=pathlib.Path("policies.yml"))
    parser.add_argument("--reports", type=pathlib.Path, default=pathlib.Path("reports"))
    parser.add_argument("--reqs", type=pathlib.Path, default=pathlib.Path("verification/reqs.yml"))
    parser.add_argument("--coverage", type=pathlib.Path)
    parser.add_argument("--per-req", type=pathlib.Path)
    parser.add_argument("--stage", choices=["all", "sim", "synth", "formal"], default="all")
    return parser.parse_args()


def normalize_threshold(value: Any) -> float | None:
    if value is None:
        return None
    if isinstance(value, str):
        try:
            value = float(value)
        except ValueError:
            return None
    if isinstance(value, (int, float)):
        if value > 1:
            return round(float(value) / 100.0, 4)
        return round(float(value), 4)
    return None


def normalize_metric(value: Any) -> float | None:
    if value is None:
        return None
    try:
        numeric = float(value)
    except (TypeError, ValueError):
        return None
    # Round to one decimal percentage before converting back to fraction.
    rounded_percent = round(numeric * 100.0 + 1e-9, 1)
    return round(rounded_percent / 100.0, 4)


def load_json(path: pathlib.Path) -> Dict[str, Any]:
    if not path or not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def load_yaml(path: pathlib.Path) -> Dict[str, Any]:
    if not path.exists():
        return {}
    try:
        return yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        raise SystemExit(f"Failed to parse {path}: {exc}") from exc


def requirement_targets_satisfied(req: Dict[str, Any], summary: Dict[str, Any]) -> bool:
    targets = req.get("cov_targets", {}) or {}
    if not isinstance(targets, dict):
        return True
    line_target = normalize_threshold(targets.get("line"))
    toggle_target = normalize_threshold(targets.get("toggle"))
    line_val = normalize_metric(summary.get("line")) if isinstance(summary, dict) else None
    toggle_val = normalize_metric(summary.get("toggle")) if isinstance(summary, dict) else None

    if line_target is not None and not isinstance(line_val, (int, float)):
        return False
    if toggle_target is not None and not isinstance(toggle_val, (int, float)):
        return False

    if line_target is not None and float(line_val) < line_target:
        return False
    if toggle_target is not None and float(toggle_val) < toggle_target:
        return False

    bin_targets = targets.get("bins") if isinstance(targets, dict) else None
    if isinstance(bin_targets, dict):
        bins_summary = summary.get("bins", {}) if isinstance(summary, dict) else {}
        bin_counts = bins_summary.get("counts", {}) if isinstance(bins_summary, dict) else {}
        bin_coverage = bins_summary.get("coverage", {}) if isinstance(bins_summary, dict) else {}
        for bin_name, threshold in bin_targets.items():
            if isinstance(threshold, (int, float, str)):
                th_norm = normalize_threshold(threshold)
                value = bin_coverage.get(bin_name)
                if th_norm is None or value is None:
                    return False
                if float(value) < th_norm:
                    return False
            elif isinstance(threshold, list):
                for required_bin in threshold:
                    if isinstance(required_bin, str):
                        count = bin_counts
                        for part in required_bin.split('.'):
                            if isinstance(count, dict) and part in count:
                                count = count[part]
                            else:
                                count = 0
                                break
                        if not isinstance(count, int) or count <= 0:
                            return False
            else:
                return False
    return True


def main() -> None:
    args = parse_args()
    reports_dir = args.reports
    stage = getattr(args, "stage", "all")
    if stage not in ("all", "sim"):
        print(f"Coverage gates skipped for stage {stage}")
        return
    reports_dir.mkdir(parents=True, exist_ok=True)

    coverage_path = args.coverage or (reports_dir / "coverage.json")
    per_req_path = args.per_req or (reports_dir / "coverage_per_req.json")

    coverage = load_json(coverage_path)
    per_req = load_json(per_req_path)
    reqs = load_yaml(args.reqs)
    policies = load_yaml(args.policies)

    coverage_policy = policies.get("coverage", {}) if isinstance(policies, dict) else {}
    line_threshold = normalize_threshold(coverage_policy.get("line"))
    toggle_threshold = normalize_threshold(coverage_policy.get("toggle"))
    per_requirement_pct = coverage_policy.get("per_requirement")
    if isinstance(per_requirement_pct, str):
        try:
            per_requirement_pct = float(per_requirement_pct)
        except ValueError:
            per_requirement_pct = None
    if isinstance(per_requirement_pct, (int, float)):
        per_requirement_fraction = normalize_threshold(per_requirement_pct)
    else:
        per_requirement_fraction = None

    override_map: Dict[str, float] = {}
    overrides = coverage_policy.get("per_req_overrides", {})
    if isinstance(overrides, dict):
        for key, value in overrides.items():
            normalized = normalize_threshold(value)
            if normalized is not None:
                override_map[str(key).lower()] = normalized

    line_cov = normalize_metric(coverage.get("line")) if isinstance(coverage, dict) else None
    toggle_cov = normalize_metric(coverage.get("toggle")) if isinstance(coverage, dict) else None

    if line_threshold is not None and not isinstance(line_cov, (int, float)):
        raise SystemExit("Line coverage missing while policy expects it")
    if toggle_threshold is not None and not isinstance(toggle_cov, (int, float)):
        raise SystemExit("Toggle coverage missing while policy expects it")

    if line_threshold is not None and float(line_cov) < line_threshold:
        raise SystemExit(f"Line coverage below policy threshold: {line_cov} < {line_threshold}")
    if toggle_threshold is not None and float(toggle_cov) < toggle_threshold:
        raise SystemExit(f"Toggle coverage below policy threshold: {toggle_cov} < {toggle_threshold}")

    per_req_map = {entry.get("id"): entry for entry in per_req.get("requirements", []) if isinstance(entry, dict)}

    requirements = reqs.get("requirements", []) if isinstance(reqs, dict) else []
    total_reqs = len(requirements)
    satisfied_count = 0
    failures: list[Tuple[str, float, float]] = []
    internal_failures: list[str] = []

    for req in requirements:
        if not isinstance(req, dict):
            continue
        rid = req.get("id")
        if not isinstance(rid, str):
            continue
        summary = per_req_map.get(rid, {})
        if not isinstance(summary, dict):
            summary = {}

        priority = str(req.get("priority", "")).lower()
        priority_target = override_map.get(priority, per_requirement_fraction)
        line_metric = normalize_metric(summary.get("line"))

        meets_internal_targets = requirement_targets_satisfied(req, summary)
        meets_priority_target = True
        if priority_target is not None:
            metric = line_metric if isinstance(line_metric, (int, float)) else 0.0
            if metric < priority_target:
                meets_priority_target = False
                failures.append((rid, metric, priority_target))

        if not meets_internal_targets:
            internal_failures.append(rid)

        if meets_internal_targets and meets_priority_target:
            satisfied_count += 1

    if per_requirement_fraction is not None and total_reqs > 0:
        satisfied_fraction = satisfied_count / total_reqs
        if satisfied_fraction < per_requirement_fraction:
            print(
                f"[gate] per-requirement coverage failed: {satisfied_fraction:.2%} met, policy requires {per_requirement_fraction:.2%}"
            )
            raise SystemExit(3)
    if internal_failures:
        print(
            "[gate] requirement coverage thresholds not met for: "
            + ", ".join(sorted(internal_failures))
        )
        raise SystemExit(3)

    if failures:
        rid, observed, required = failures[0]
        print(
            f"[gate] per-requirement coverage failed: {rid} (got {observed*100:.1f}%, need {required*100:.1f}%)"
        )
        raise SystemExit(3)

    print("Coverage gates passed")


if __name__ == "__main__":
    main()
