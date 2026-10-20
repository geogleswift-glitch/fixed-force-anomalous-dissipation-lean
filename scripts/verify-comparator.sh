#!/usr/bin/env bash
set -euo pipefail

# Use the protected Comparator and independent kernels bundled with the
# pinned supported Lean release, as in the official Palomar template.
grep -qx 'leanprover/lean4:v4.35.0-rc4' lean-toolchain
test -f lake-manifest.json
command -v bwrap >/dev/null
bwrap --version | grep -qx 'bubblewrap 0.12.0'
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool"
done

transcript_dir=${RUNNER_TEMP:-${TMPDIR:-/tmp}}
config=$(mktemp "$transcript_dir/palomar-comparator.XXXXXX.json")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if not isinstance(config, dict):
    raise SystemExit("comparator.json must be an object")
if "external_kernels" in config:
    raise SystemExit("external_kernels must not be supplied by the candidate configuration")
if set(config["permitted_axioms"]) != {"propext", "Quot.sound", "Classical.choice"}:
    raise SystemExit("unexpected permitted axioms")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron", "--jobs=2"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

# Rebuild the exact challenge from its reviewed source, even on a cache hit.
# Preserve the rest of the project and dependency artifacts.
for folder in (".lake/build/lib/lean", ".lake/build/ir"):
    for artifact in pathlib.Path(folder).glob("Challenge.*"):
        if artifact.is_file() or artifact.is_symlink():
            artifact.unlink()
PY

lake comparator --config "$config" 2>&1 | tee "$transcript_dir/comparator.log"
