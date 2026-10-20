#!/usr/bin/env bash
set -euo pipefail

# Run the pinned official intake checks on a fresh private checkout.
# This does not register a submission or run the full mechanical execution.
: "${RUNNER_TEMP:?}"
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_SHA:?}"
: "${GITHUB_TOKEN:?}"
pipeline=.lake/palomar-pipeline
test "$(git -C "$pipeline" rev-parse HEAD)" = d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
export PALOMAR_EXECUTION_PROFILE=palomar-standard-v1
export BUNDLE_GEMFILE="$PWD/$pipeline/Gemfile"

python - <<'PY'
import hashlib
import json
import os
from pathlib import Path

identity = ":".join(os.environ.get(key, "") for key in (
    "GITHUB_REPOSITORY", "GITHUB_SHA", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"))
inputs = {
    "repository": os.environ["GITHUB_REPOSITORY"],
    "commit": os.environ["GITHUB_SHA"],
    "request_id": hashlib.sha256(identity.encode()).hexdigest()[:12],
    "mode": "preflight",
    "options": json.dumps({
        "comparator_config_path": "comparator.json",
        "authorization_relationship": "I have approval from a responsible author or maintainer",
    }),
}
Path(os.environ["RUNNER_TEMP"], "submission-inputs.json").write_text(
    json.dumps({"inputs": inputs}) + "\n", encoding="utf-8")
PY

# The short-lived token has read-only access to this repository. It is used
# only for the official fresh fetch and is removed before any proof build.
askpass=$(mktemp "$RUNNER_TEMP/palomar-read-askpass.XXXXXX")
trap 'rm -f "$askpass"' EXIT
cat > "$askpass" <<'SH'
#!/bin/sh
case "$1" in
  *Username*) printf '%s\n' 'x-access-token' ;;
  *) printf '%s\n' "$GITHUB_TOKEN" ;;
esac
SH
chmod 700 "$askpass"
GIT_ASKPASS="$askpass" GIT_TERMINAL_PROMPT=0 \
  python "$pipeline/scripts/verify_submission.py" prepare \
    --event "$RUNNER_TEMP/submission-inputs.json" \
    --work-dir "$RUNNER_TEMP/palomar-prepare" \
    --output "$RUNNER_TEMP/preparation-report.json" \
    --licensee "$(command -v bundle)"
rm -f "$askpass"
trap - EXIT
unset GITHUB_TOKEN

# The official CLI deliberately returns zero for a reported intake failure;
# require its successful preparation state and the exact requested source.
python - <<'PY'
import json
import os
from pathlib import Path

report = json.loads(Path(os.environ["RUNNER_TEMP"], "preparation-report.json")
                    .read_text(encoding="utf-8"))
source = report.get("source", {})
if (report.get("status") != "pending" or report.get("stage") != "prepared"
        or source.get("repository") != os.environ["GITHUB_REPOSITORY"]
        or source.get("commit") != os.environ["GITHUB_SHA"]):
    raise SystemExit("Official source preparation failed: " + json.dumps({
        "status": report.get("status"), "stage": report.get("stage"),
        "errors": report.get("errors", []),
    }, ensure_ascii=False))
print("Pinned official source preparation passed for the exact private commit.")
print("Full official execution and registry registration have not been performed.")
PY
