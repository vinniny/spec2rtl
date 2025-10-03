#!/bin/bash
set -euo pipefail
if git diff --cached --name-only | grep -E '^(reports|build)/'; then
  echo "pre-commit: refusing to commit artifacts under reports/ or build/" >&2
  exit 1
fi
