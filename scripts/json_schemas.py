"""Lightweight schema guards for key JSON artifacts."""
from __future__ import annotations

from typing import Any, Callable, Dict, Iterable

Validator = Callable[[Dict[str, Any]], None]


class SchemaError(ValueError):
    pass


def _require_keys(payload: Dict[str, Any], required: Iterable[str]) -> None:
    missing = [key for key in required if key not in payload]
    if missing:
        raise SchemaError(f"Missing required keys: {', '.join(missing)}")


def _ensure_type(name: str, value: Any, expected: tuple[type, ...]) -> None:
    if not isinstance(value, expected):
        raise SchemaError(f"Key '{name}' expected {expected}, got {type(value)}")


def validate_sim_report(payload: Dict[str, Any]) -> None:
    _require_keys(payload, ["schema", "status", "pass_count", "fail_count", "failures", "coverage_samples"])
    _ensure_type("schema", payload["schema"], (int,))
    if payload["status"] not in {"pass", "fail"}:
        raise SchemaError("status must be 'pass' or 'fail'")
    for key in ("pass_count", "fail_count"):
        _ensure_type(key, payload[key], (int,))
    if not isinstance(payload["failures"], list):
        raise SchemaError("failures must be a list")
    if not isinstance(payload["coverage_samples"], dict):
        raise SchemaError("coverage_samples must be a dict")
    flaky = payload.get("flaky")
    if flaky is not None:
        if not isinstance(flaky, dict) or not {"retries", "max_attempts"}.issubset(flaky):
            raise SchemaError("flaky must contain retries and max_attempts")


def validate_coverage(payload: Dict[str, Any]) -> None:
    _require_keys(payload, ["schema", "line", "toggle"])
    _ensure_type("schema", payload["schema"], (int,))
    for key in ("line", "toggle"):
        if payload[key] is not None and not isinstance(payload[key], (int, float)):
            raise SchemaError(f"{key} must be float or null")


def validate_coverage_per_req(payload: Dict[str, Any]) -> None:
    _require_keys(payload, ["schema", "requirements"])
    if not isinstance(payload["requirements"], list):
        raise SchemaError("requirements must be a list")
    for entry in payload["requirements"]:
        if not isinstance(entry, dict):
            raise SchemaError("each requirement summary must be a dict")
        for field in ("id", "line", "toggle"):
            if field not in entry:
                raise SchemaError(f"per-requirement entry missing '{field}'")
        if not isinstance(entry["id"], str):
            raise SchemaError("requirement id must be a string")


def validate_synth(payload: Dict[str, Any]) -> None:
    _require_keys(payload, ["schema", "cells", "warnings", "has_latch"])
    _ensure_type("cells", payload["cells"], (dict,))
    _ensure_type("warnings", payload["warnings"], (list,))
    _ensure_type("has_latch", payload["has_latch"], (bool,))


def validate_formal_summary(payload: Dict[str, Any]) -> None:
    _require_keys(payload, ["schema", "tasks"])
    tasks = payload["tasks"]
    if not isinstance(tasks, list):
        raise SchemaError("tasks must be a list")
    for task in tasks:
        if not isinstance(task, dict):
            raise SchemaError("task entry must be a dict")
        _require_keys(task, ["name", "status", "log"])
        if task["status"] not in {"PASS", "FAIL"}:
            raise SchemaError("task status must be PASS or FAIL")


def validate_mutation_summary(payload: Dict[str, Any]) -> None:
    _require_keys(payload, ["schema", "total", "killed", "survived", "kill_rate_percent", "results"])
    for key in ("total", "killed", "survived"):
        _ensure_type(key, payload[key], (int,))
    if not isinstance(payload["kill_rate_percent"], (int, float)):
        raise SchemaError("kill_rate_percent must be numeric")
    if not isinstance(payload["results"], list):
        raise SchemaError("results must be a list")


SCHEMA_VALIDATORS: Dict[str, Validator] = {
    "sim_report": validate_sim_report,
    "coverage": validate_coverage,
    "coverage_per_req": validate_coverage_per_req,
    "synth_report": validate_synth,
    "formal_summary": validate_formal_summary,
    "mutation_summary": validate_mutation_summary,
}
