#!/usr/bin/env python3
"""Minimal HTTP surface for automation glue (LangGraph, n8n, etc.)."""
from __future__ import annotations

import argparse
import json
import os
import subprocess
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Dict, Optional

ROOT = Path(__file__).resolve().parents[2]


class APIServer(BaseHTTPRequestHandler):
    server_version = "spec2rtl-api/0.1"

    def do_POST(self) -> None:  # noqa: N802 (http.server style)
        payload = self._read_json_body()
        if payload is None:
            return

        if self.path == "/spec2tests":
            self._handle_spec2tests(payload)
        elif self.path == "/sim":
            self._handle_sim(payload)
        elif self.path == "/judge":
            self._handle_judge()
        elif self.path == "/synth":
            self._handle_synth()
        elif self.path == "/trace":
            self._handle_trace()
        else:
            self.respond_error(HTTPStatus.NOT_FOUND, f"Unknown endpoint: {self.path}")

    def do_GET(self) -> None:  # noqa: N802
        if self.path == "/healthz":
            self.respond_json(HTTPStatus.OK, {"schema": 1, "status": "ok", "ok": True})
            return
        if self.path == "/versions":
            self._handle_versions()
            return
        self.respond_error(HTTPStatus.METHOD_NOT_ALLOWED, "Unsupported method")

    def log_message(self, fmt: str, *args: object) -> None:  # noqa: D401
        message = fmt % args
        print(f"[api] {self.log_date_time_string()} {self.address_string()} {message}")

    def respond_json(self, status: HTTPStatus, payload: Dict[str, Any]) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def respond_error(
        self,
        status: HTTPStatus,
        message: str,
        extra: Optional[dict] = None,
    ) -> None:
        payload: Dict[str, Any] = {"schema": 1, "status": "error", "message": message}
        if extra:
            payload["details"] = extra
        self.respond_json(status, payload)

    def _read_json_body(self) -> Optional[Dict[str, Any]]:
        length = self.headers.get("Content-Length")
        if length is None:
            return {}
        try:
            size = int(length)
        except ValueError:
            self.respond_error(HTTPStatus.BAD_REQUEST, "Invalid Content-Length header")
            return None
        if size == 0:
            return {}
        raw = self.rfile.read(size)
        if not raw:
            return {}
        try:
            data = json.loads(raw.decode("utf-8"))
        except json.JSONDecodeError as exc:
            self.respond_error(HTTPStatus.BAD_REQUEST, f"Malformed JSON body: {exc.msg}")
            return None
        if not isinstance(data, dict):
            self.respond_error(HTTPStatus.BAD_REQUEST, "JSON body must be an object")
            return None
        return data

    def _run(self, command: list[str]) -> Optional[subprocess.CompletedProcess[str]]:
        try:
            return subprocess.run(
                command,
                cwd=ROOT,
                check=True,
                capture_output=True,
                text=True,
            )
        except subprocess.CalledProcessError as exc:
            detail = {
                "command": exc.cmd,
                "returncode": exc.returncode,
                "stdout": exc.stdout,
                "stderr": exc.stderr,
            }
            self.respond_error(HTTPStatus.INTERNAL_SERVER_ERROR, "Command failed", detail)
            return None

    def _artifact_text(self, relative: str) -> Optional[str]:
        path = ROOT / relative
        if not path.exists():
            self.respond_error(HTTPStatus.INTERNAL_SERVER_ERROR, f"Artifact not found: {relative}")
            return None
        try:
            return path.read_text(encoding="utf-8")
        except OSError as exc:
            self.respond_error(HTTPStatus.INTERNAL_SERVER_ERROR, f"Failed to read {relative}: {exc}")
            return None

    def _artifact_json(self, relative: str) -> Optional[Dict[str, Any]]:
        text = self._artifact_text(relative)
        if text is None:
            return None
        try:
            return json.loads(text)
        except json.JSONDecodeError as exc:
            self.respond_error(HTTPStatus.INTERNAL_SERVER_ERROR, f"Invalid JSON in {relative}: {exc.msg}")
            return None

    def _handle_spec2tests(self, _: Dict[str, Any]) -> None:
        result = self._run(["python3", "scripts/spec2tests.py"])
        if result is None:
            return
        reqs = self._artifact_text("verification/reqs.yml")
        svas = self._artifact_text("verification/svas.sv")
        plan = self._artifact_text("verification/test_plan.md")
        if None in (reqs, svas, plan):
            return
        payload = {
            "schema": 1,
            "status": "ok",
            "artifacts": {
                "reqs": {"path": "verification/reqs.yml", "content": reqs},
                "svas": {"path": "verification/svas.sv", "content": svas},
                "plan": {"path": "verification/test_plan.md", "content": plan},
            },
            "stdout": result.stdout,
        }
        if result.stderr:
            payload["stderr"] = result.stderr
        self.respond_json(HTTPStatus.OK, payload)

    def _handle_sim(self, body: Dict[str, Any]) -> None:
        seed = body.get("seed")
        command = ["make"]
        if seed is not None:
            command.append(f"SEED={seed}")
        command.append("report")
        result = self._run(command)
        if result is None:
            return
        sim_data = self._artifact_json("reports/sim_report.json")
        if sim_data is None:
            return
        payload = {
            "schema": 1,
            "status": "ok",
            "data": sim_data,
            "stdout": result.stdout,
        }
        if result.stderr:
            payload["stderr"] = result.stderr
        if seed is not None:
            payload["seed"] = seed
        self.respond_json(HTTPStatus.OK, payload)

    def _handle_judge(self) -> None:
        result = self._run(["python3", "scripts/judge.py"])
        if result is None:
            return
        data = self._artifact_json("reports/judge.json")
        if data is None:
            return
        payload = {
            "schema": 1,
            "status": "ok",
            "data": data,
            "stdout": result.stdout,
        }
        if result.stderr:
            payload["stderr"] = result.stderr
        self.respond_json(HTTPStatus.OK, payload)

    def _handle_synth(self) -> None:
        result = self._run(["make", "synth"])
        if result is None:
            return
        data = self._artifact_json("reports/synth_report.json")
        if data is None:
            return
        payload = {
            "schema": 1,
            "status": "ok",
            "data": data,
            "stdout": result.stdout,
        }
        if result.stderr:
            payload["stderr"] = result.stderr
        self.respond_json(HTTPStatus.OK, payload)

    def _handle_trace(self) -> None:
        result = self._run(["make", "trace"])
        if result is None:
            return
        data = self._artifact_json("reports/trace.json")
        if data is None:
            return
        payload = {
            "schema": 1,
            "status": "ok",
            "data": data,
            "stdout": result.stdout,
        }
        if result.stderr:
            payload["stderr"] = result.stderr
        self.respond_json(HTTPStatus.OK, payload)

    def _handle_versions(self) -> None:
        result = self._run(["python3", "scripts/env_report.py"])
        if result is None:
            return
        try:
            data = json.loads(result.stdout or "{}")
        except json.JSONDecodeError as exc:
            self.respond_error(HTTPStatus.INTERNAL_SERVER_ERROR, f"env_report parse error: {exc.msg}")
            return
        payload = {"schema": 1, "status": "ok", "versions": data}
        self.respond_json(HTTPStatus.OK, payload)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", default=os.environ.get("API_HOST", "0.0.0.0"))
    parser.add_argument("--port", type=int, default=int(os.environ.get("API_PORT", "8080")))
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    server = ThreadingHTTPServer((args.host, args.port), APIServer)
    print(f"Serving on http://{args.host}:{args.port}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("Shutting down")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
