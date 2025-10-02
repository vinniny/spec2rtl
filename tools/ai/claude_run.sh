#!/usr/bin/env bash
set -euo pipefail

STAGE="${1:?stage name (verify|synth|spec2rtl)}"; shift || true
OUT_DIR="reports/ai"; mkdir -p "$OUT_DIR"

# Inputs (json, logs, etc.) passed as subsequent args
INPUTS=("$@")

# Compose prompt = memory + task template + live artifacts
MEM_GLOBAL="memory/CLAUDE.md"
MEM_STAGE="memory/CLAUDE.${STAGE}.md"
TEMPLATE="tools/ai/templates/${STAGE}_task.md.tmpl"

assemble() {
  echo "### Memory.Global";     cat "$MEM_GLOBAL"
  echo; echo "### Memory.${STAGE}"; [ -f "$MEM_STAGE" ] && cat "$MEM_STAGE" || true
  echo; echo "### Task";           cat "$TEMPLATE"
  for f in "${INPUTS[@]}"; do
    echo; echo "### Artifact: ${f}"; echo '```'; cat "$f"; echo '```'
  done
}

PROMPT_FILE="$(mktemp)"
assemble > "$PROMPT_FILE"

# Transport: Anthropic API (default) or OpenRouter (if ANTHROPIC_API_KEY not set)
MODEL="${MODEL:-claude-3-5-sonnet-20241022}"   # adjust to Sonnet 4.5's model id once public id is known
MAXTOK="${MAXTOK:-4096}"

if [[ -n "${ANTHROPIC_API_KEY:-}" ]]; then
  curl -fsS https://api.anthropic.com/v1/messages \
    -H "x-api-key: $ANTHROPIC_API_KEY" \
    -H "anthropic-version: 2023-06-01" \
    -H "content-type: application/json" \
    -d @<(jq -n --arg m "$MODEL" --argjson mt "$MAXTOK" \
         --arg content "$(cat "$PROMPT_FILE")" \
         '{model:$m, max_tokens:$mt, messages:[{role:"user", content:$content}]}') \
    | tee "$OUT_DIR/${STAGE}.json" \
    | jq -r '.content[0].text' > "$OUT_DIR/${STAGE}.md"
elif [[ -n "${OPENROUTER_API_KEY:-}" ]]; then
  curl -fsS https://openrouter.ai/api/v1/chat/completions \
    -H "Authorization: Bearer $OPENROUTER_API_KEY" \
    -H "Content-Type: application/json" \
    -d @<(jq -n --arg m "anthropic/${MODEL}" \
         --arg content "$(cat "$PROMPT_FILE")" \
         '{model:$m, messages:[{role:"user", content:$content}]}') \
    | tee "$OUT_DIR/${STAGE}.json" \
    | jq -r '.choices[0].message.content' > "$OUT_DIR/${STAGE}.md"
else
  echo "No API key set (ANTHROPIC_API_KEY or OPENROUTER_API_KEY). Skipping." >&2
  exit 2
fi

echo "Wrote $OUT_DIR/${STAGE}.md"
