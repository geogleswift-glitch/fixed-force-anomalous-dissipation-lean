"""Check the source layout and fixed submission metadata using Python 3.11+."""

import json
from pathlib import Path
import re
import subprocess
import tomllib


ROOT = Path(__file__).resolve().parent.parent
tracked = subprocess.check_output(
    ["git", "ls-files", "-z"], cwd=ROOT
).decode("utf-8").split("\0")
tracked = [name for name in tracked if name]
RELEASE_FILES = {
    ".gitattributes", ".gitignore", "Challenge.lean", "Solution.lean", "LICENSE",
    "README.md", "PALOMAR_READINESS.md", "comparator.json", "formalization.yaml",
    "lake-manifest.json", "lakefile.toml", "lean-toolchain",
    ".github/workflows/lean.yml", ".github/workflows/comparator.yml",
    "scripts/verify-comparator.sh", "scripts/check-palomar-preparation.sh",
    "verification/Audit.lean",
    "verification/Check-Axioms.ps1", "verification/UnconditionalStatement.lean",
    "verification/check-layout.py",
}


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def lean_code(source):
    """Ignore nested Lean comments and string literals in the source lint."""
    result, depth, i = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == "/-":
            if not depth:
                result.append(" ")
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            i += 1
            result.append(" ")
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


for name in tracked:
    project_module = (Path(name).parent == Path("RequestProject")
                      and Path(name).suffix == ".lean")
    require(name in RELEASE_FILES or project_module,
            f"Unreviewed file outside the release allowlist: {name}")
    require(not name.lower().endswith((".tex", ".pdf", ".olean", ".ilean")),
            f"Excluded manuscript/build artifact is tracked: {name}")
    if not name.endswith(".lean"):
        continue
    source = (ROOT / name).read_text(encoding="utf-8")
    require(re.match(r"\s*module\b", source), f"Missing module header: {name}")
    require(len(source.splitlines()) <= 10000, f"Lean module exceeds size cap: {name}")
    if name.startswith("RequestProject/") or name == "Solution.lean":
        forbidden = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b",
                              lean_code(source))
        require(forbidden is None, f"Review forbidden proof mechanism in {name}")

challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
require(len(challenge.splitlines()) <= 1000, "Challenge exceeds line cap")
require((ROOT / "Challenge.lean").stat().st_size <= 100 * 1024, "Challenge exceeds byte cap")
imports = re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", challenge, re.MULTILINE)
require(imports == ["Mathlib"], "Challenge must import only Mathlib")
require(len(re.findall(r"\bsorry\b", challenge)) == 1, "Challenge must have one protocol hole")

config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
require(config["challenge_module"] == "Challenge", "Unexpected challenge module")
require(config["solution_module"] == "Solution", "Unexpected solution module")
require(config["theorem_names"] == ["AnomDiss.fixed_force_anomalous_dissipation"],
        "Unexpected compared theorem")
require(config.get("definition_names") == [], "Mathematical definitions must not be holes")
require(set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"},
        "Unexpected permitted axioms")
require("external_kernels" not in config, "Kernel commands belong in the trusted CI wrapper")

require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc4",
        "Unexpected Lean toolchain")
lake = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
revision = "1f414401f69059aa7eead47b53ee40bd38455eeb"
require(lake["require"] == [{"name": "mathlib", "git":
        "https://github.com/leanprover-community/mathlib4.git", "rev": revision}],
        "Unexpected direct dependency or Mathlib revision")
manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
require(len(mathlib) == 1 and mathlib[0]["rev"] == revision, "Mathlib manifest mismatch")
require(all(p["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", p["rev"])
            for p in manifest["packages"]), "Dependencies must have immutable Git revisions")
print("Release allowlist, module layout, source exclusions, Comparator metadata and pins passed.")
