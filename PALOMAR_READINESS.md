# Palomar release checks

The complete project is verified locally on Lean `v4.35.0-rc4`, with the exact matching official Mathlib revision `1f414401f69059aa7eead47b53ee40bd38455eeb`. `AnomDiss.main_theorem_unconditional` has only the numerical tolerance and its two inequalities as parameters. Both analytic existence inputs are proved in the project; no unresolved analytic premise remains in that main theorem.

The requested GitHub owner is `geogleswift-glitch`, and the responsible maintainer is Haiqi Zhang. The present scope is private preparation; full official execution is deferred until a sufficiently provisioned Linux runner is available.

Completed locally on the supported toolchain:

- Whole-project build, including Challenge and Solution: 9258 tasks completed successfully.
- Public declaration checks and an exact unconditional statement check.
- Independent comparison with the source manuscript, including every Hölder exponent for the same witnesses.
- Independent transitive axiom audits of the final main theorem and closed NS/scalar existence results: only `propext`, `Classical.choice`, and `Quot.sound`.
- Actual velocity and real-pressure reconstruction, closed-interval pointwise momentum, all original velocity and pressure parabolic fields.
- A proof-axiom gate that correctly rejects an imported `sorry` negative control.

Hosted verification is recorded in the repository's GitHub Actions runs at their exact commits. The Lean workflow builds the project and repeats the statement and axiom gates. The protected Comparator workflow runs the pinned official source-preparation stage, then the standalone bundled Comparator under its Linux sandbox with Lean, NanoDa, and con-ron. Consult each run and its evidence artifact for the actual outcome; these checks are distinct from full official execution.

The Mathlib-only Challenge contains the single theorem placeholder required by the Comparator protocol. Solution does not import it. The protected comparison checks the statements and mathematical definition bodies, with no permitted definition holes.

Remaining before registry submission:

1. Run the complete official execution on a host meeting its resource profile. The pinned `palomar-standard-v1` profile requires at least 14 GiB RAM and 20 GiB free workspace. A standard private GitHub Linux runner has 8 GB RAM, so standalone protected Comparator replay there does not establish completion of the full official preflight.
2. Decide when to make the repository public, then select the final immutable commit and run the official submission process. No public release or registry submission has been performed.

The original conditional Aristotle declarations remain as intermediate results. An axiom audit by itself would not discharge their parameters; the new main theorem explicitly uses the closed existence proofs instead.

The original TeX manuscript is excluded from this repository. README records the human authors and the assistance of ChatGPT, Aristotle, and Codex.

The official policy was checked against [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission) and its [toolchain requirements](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json). A protected Linux replay is needed because the bundled Comparator uses `bwrap`; the current Windows host has no installed WSL distribution or Docker runtime.

The resource limits above come from the pinned official [verification profile](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/verification-profile.json). Full official execution, editorial review, and registry acceptance remain distinct from this project's local verification and hosted checks.
