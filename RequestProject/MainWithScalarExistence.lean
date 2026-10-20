module

public import RequestProject.MainRegularity
public import RequestProject.MainExistence
public import RequestProject.ScalarGlobalSpatialSchauder

/-!
# Main construction after proving the scalar analytic input

The scalar existence, equation, uniqueness, and full parabolic regularity
are theorems in this development. The following statements discharge that
input explicitly. Navier--Stokes classical existence remains a premise.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- The full all-exponent construction with only the Navier--Stokes
analytic input left as an explicit hypothesis. -/
theorem main_theorem_all_beta_with_proved_scalar (hNS : ExternalNS2D)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∀ m β, 0 < β → β < 1 →
          IsParabolicC12 1 β (u m) ∧ IsParabolicC01 1 β (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x := by
  exact main_theorem_all_beta hNS externalScalar_proved ε hε0 hε1

/-- The fixed-exponent main construction needs only the concrete zero-data
horizontal Navier--Stokes existence problem, with scalar existence proved. -/
theorem main_theorem_zero_data_with_proved_scalar (hNS : HorizontalZeroDataExistence)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x := by
  exact main_theorem_from_zero_data_existence hNS scalarClassicalExistence_proved ε hε0 hε1

end AnomDiss
