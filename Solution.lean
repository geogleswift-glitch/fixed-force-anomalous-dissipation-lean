module

public import RequestProject.MainUnconditional

/-!
# Proved fixed-force anomalous dissipation

Authors: Tao Tao, Baishu Zeng and Haiqi Zhang.

This module is intentionally independent of Challenge. Comparator loads the
two environments separately and checks the same theorem and every definition
used by its statement. The proof below applies the unconditional theorem;
there are no additional analytic existence or regularity premises.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace AnomDiss
/-- The fixed-force construction on the normalized three-dimensional torus.
The initial datum and force are independent of the viscosity index; all
parabolic Hölder exponents hold for the same velocity and pressure witnesses. -/
theorem fixed_force_anomalous_dissipation (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∀ m β, 0 < β → β < 1 →
          IsParabolicC12 1 β (u m) ∧ IsParabolicC01 1 β (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x := by
  exact main_theorem_unconditional ε hε0 hε1

end AnomDiss
