# Palomar registration and verification record

This public project is registered in the [Palomar Registry as **PALOMAR-2026-10-22-000013, version 1**](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000013&version=1).

The GitHub owner is `geogleswift-glitch`, and the responsible maintainer is Haiqi Zhang. The human authors are Tao Tao, Baishu Zeng and Haiqi Zhang, in that order.

The complete project is verified locally on Lean `v4.35.0-rc4`, with the exact matching official Mathlib revision `1f414401f69059aa7eead47b53ee40bd38455eeb`. `AnomDiss.main_theorem_unconditional` has only the numerical tolerance and its two inequalities as parameters. Both analytic existence inputs are proved in the project; no unresolved analytic premise remains in that main theorem.

Completed locally on the supported toolchain:

- Whole-project build, including Challenge and Solution: 9258 tasks completed successfully.
- Public declaration checks and an exact unconditional statement check.
- Independent comparison with the source manuscript, including every Hölder exponent for the same witnesses.
- Independent transitive axiom audits of the final main theorem and closed NS/scalar existence results: only `propext`, `Classical.choice`, and `Quot.sound`.
- Actual velocity and real-pressure reconstruction, closed-interval pointwise momentum, all original velocity and pressure parabolic fields.
- A proof-axiom gate that correctly rejects an imported `sorry` negative control.

The initial repository proof snapshot, [`52985f1bb56a05c107523d2265445d0cd38f5619`](https://github.com/geogleswift-glitch/fixed-force-anomalous-dissipation-lean/tree/52985f1bb56a05c107523d2265445d0cd38f5619), passed both hosted checks:

- [Lean build and axiom audit](https://github.com/geogleswift-glitch/fixed-force-anomalous-dissipation-lean/actions/runs/39478317371): whole-project build, source layout, exact unconditional statement and transitive axiom audit.
- [Protected Comparator](https://github.com/geogleswift-glitch/fixed-force-anomalous-dissipation-lean/actions/runs/39478317172): pinned official source preparation and sandboxed comparison, with the proof accepted by Lean, NanoDa and con-ron.

The workflow badges in README link to current repository checks. Their reports identify the exact checked commits. The repository's source-preparation and standalone Comparator checks are distinct from the registry's versioned verification record.

The Mathlib-only Challenge contains the single theorem placeholder required by the Comparator protocol. Solution does not import it. The protected comparison checks the statements and mathematical definition bodies, with no permitted definition holes.

## Reproducing the registered version

Use the source revision linked by the [version 1 registry entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000013&version=1) to reproduce that registered result. The same entry is the reference for its registry verification details. A later documentation commit on `main` does not amend the registered version or identify a new proof version.

For development on `main`, run the checks documented in README and inspect the GitHub Actions results for the chosen commit. The source-preparation workflow checks a fresh checkout; it does not submit or register a new Palomar version.

The original conditional Aristotle declarations remain as intermediate results. An axiom audit by itself would not discharge their parameters; the new main theorem explicitly uses the closed existence proofs instead.

The original TeX manuscript is excluded from this repository. README records the human authors and the assistance of ChatGPT, Aristotle, and Codex.

The repository's preparation and sandbox tools are pinned to [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44). Consult the current official instructions when preparing a future registry version. Public registration, kernel verification and independent human review are separate claims; this document records the registry link and the repository checks without asserting an independent human review.
