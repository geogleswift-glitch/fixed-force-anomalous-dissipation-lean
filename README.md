# Fixed-force anomalous dissipation in Lean

**Authors: Tao Tao, Baishu Zeng and Haiqi Zhang**

Responsible maintainer: Haiqi Zhang.

Registered in the [Palomar Registry as **PALOMAR-2026-10-22-000013, version 1**](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000013&version=1).

[![Lean build and axiom audit](https://github.com/geogleswift-glitch/fixed-force-anomalous-dissipation-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/geogleswift-glitch/fixed-force-anomalous-dissipation-lean/actions/workflows/lean.yml)
[![Protected Comparator](https://github.com/geogleswift-glitch/fixed-force-anomalous-dissipation-lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/geogleswift-glitch/fixed-force-anomalous-dissipation-lean/actions/workflows/comparator.yml)

The complete project, exact unconditional statement check, and transitive axiom audit have passed locally on Lean `v4.35.0-rc4` with its pinned Mathlib revision. The badges link to hosted verification results for repository commits.

For every `0 < ε < 1`, this project proves the existence of:

- One smooth, periodic, divergence-free initial velocity on the unit three-dimensional torus, with normalized `L²` norm equal to one.
- One divergence-free force, independent of viscosity, compactly supported in time and smooth in time with values in every spatial Hölder class `C^α`, `0 < α < 1`.
- A positive, strictly decreasing viscosity sequence tending to zero, and classical Navier–Stokes solutions for that common initial datum and force.
- One uniform velocity bound and the viscous dissipation lower bound `(1 − ε) / 2` for every member of the sequence.

The same velocity and pressure witnesses satisfy the required parabolic Hölder regularity for every `0 < β < 1`, including the closed time interval `[0,1]`.

The principal declaration is [`AnomDiss.main_theorem_unconditional`](RequestProject/MainUnconditional.lean). Its only parameters are `ε`, `0 < ε`, and `ε < 1`. Both analytic existence inputs are proved within the project: the actual two-dimensional phase-force solution is constructed in [`NSPhaseGalerkinClassical.lean`](RequestProject/NSPhaseGalerkinClassical.lean), and the scalar theorem is proved in [`ScalarGlobalSpatialSchauder.lean`](RequestProject/ScalarGlobalSpatialSchauder.lean).

This is the conclusion of Question 2.1 in Elia Bruè and Camillo De Lellis, *Anomalous Dissipation for the Forced 3D Navier–Stokes Equations*, Communications in Mathematical Physics 400 (2023), 1507–1533, DOI [10.1007/s00220-022-04626-0](https://doi.org/10.1007/s00220-022-04626-0). That paper poses the question; the new non-formal proof is attributed to the authors listed above.

## Verification

The toolchain and Mathlib revision are pinned. From the repository root:

```powershell
lake build
python3 verification/check-layout.py
lake env lean verification/Audit.lean
lake env lean verification/UnconditionalStatement.lean
./verification/Check-Axioms.ps1
```

The statement check applies the final theorem to the complete unconditional conclusion. The axiom gate loads proof bodies in a non-module probe and traverses their transitive dependencies, permitting only `propext`, `Classical.choice`, and `Quot.sound`. A deliberate `sorry` negative control was rejected. The proved source under `RequestProject/` contains no `sorry`, custom axioms, or unsafe proof mechanism. CI builds the project and runs both gates.

The original Aristotle theorem remains available as a conditional intermediate result. Its `ExternalNS2D` and `ExternalScalar` parameters are not premises of `main_theorem_unconditional`.

## Statement conventions

The project uses periodic lifts on Euclidean space. The initial normalization `l2sqV u₀ = 1` is the squared normalized `L²` identity, equivalent to unit norm. The force predicate uses an explicit Hölder norm and time-derivative interface; [`HolderTimeContinuity.lean`](RequestProject/HolderTimeContinuity.lean) proves continuity of every derivative in that full norm. It also requires smooth individual spatial slices. The pressure class uses time exponent `β/2`; the stronger `(1+β)/2` occurs for first spatial derivatives in the velocity's `IsParabolicC12` class.

## Authorship

The human authors completed the original non-formal proof with assistance from ChatGPT. Aristotle and Codex developed and repaired the Lean formalization from that proof. The original TeX manuscript is intentionally excluded.

## Palomar registration

`Challenge.lean`, `Solution.lean`, and `comparator.json` provide the submission interface. The Challenge contains the expected theorem placeholder; the Solution uses the closed proved theorem and does not import the Challenge. The protected Comparator workflow runs the pinned official source-preparation stage and a standalone sandboxed comparison with Lean, NanoDa, and con-ron. Its reports record the result for the checked commit.

This repository is public and registered in Palomar as **PALOMAR-2026-10-22-000013, version 1**. The [versioned registry entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000013&version=1) is the reference for the registered source revision and registry verification record. Later documentation updates on `main` do not change that registry version. See [PALOMAR_READINESS.md](PALOMAR_READINESS.md) for the registration and repository verification history.

## License

Apache-2.0. Dependencies retain their own licenses.
