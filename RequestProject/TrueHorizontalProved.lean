module

public import RequestProject.NSPhaseGalerkinClassical
public import RequestProject.ScalarGlobalSpatialSchauder
public import RequestProject.NSClassicalEnergy
public import RequestProject.TrueHorizontal

/-!
# The unconditional horizontal solutions used by the main construction

The actual zero-data phase-force Navier--Stokes solution is supplied by
the proved Galerkin and parabolic analysis. Scalar existence is supplied
by the proved global scalar theorem. Neither analytic interface is a
hypothesis of this result.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss

theorem true_horizontal_existence_proved (ν : ℝ) (hν : 0 < ν) (w : Phase) :
    ∃ (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
      IsClassicalNS 1 ν 0 (gForce w) v p ∧
      (∀ β, 0 < β → β < 1 → IsParabolicC12 1 β v ∧ IsParabolicC01 1 β p) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, l2sqV (v t) / 2 + ν * ∫ s in (0 : ℝ)..t, ∫ x in cell 2, gradSqV (v s) x
          = ∫ s in (0 : ℝ)..t, ∫ x in cell 2, dot (gForce w s x) (v s x)) ∧
      ∀ θ₀ : Pt 2 → ℝ, ContDiff ℝ ∞ θ₀ → IsPeriodic θ₀ →
        ∃ θ : ℝ → Pt 2 → ℝ, IsClassicalScalar 1 ν v θ₀ θ ∧
          (∀ θ', IsClassicalScalar 1 ν v θ₀ θ' → ∀ t ∈ Icc (0 : ℝ) 1, θ' t = θ t) ∧
          (∀ M, (∀ x, |θ₀ x| ≤ M) → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |θ t x| ≤ M) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, l2sq (θ t) / 2 + dissipation ν θ t = l2sq θ₀ / 2) := by
  obtain ⟨v,p,hns,hreg⟩ := exists_phase_classical_all_beta ν hν w
  refine ⟨v,p,hns,hreg,?_,?_⟩
  · intro t ht
    have he := hns.kinetic_energy_identity zero_le_one
      (fun s _ => (gForce_slice_props w s).2.1.continuous) t ht
    have hzero : l2sqV (0 : Pt 2 → Pt 2) = 0 := by simp [l2sqV]
    simpa only [hzero, zero_div, zero_add] using he
  · intro θ₀ hθ₀ hp
    have hvC01 : IsParabolicC01 1 (1/2) v :=
      (hreg (1/2) (by norm_num) (by norm_num)).1.toC01 zero_le_one (by norm_num) (by norm_num)
    obtain ⟨θ,_,hθ,huniq⟩ := externalScalar_proved 1 ν (1/2) one_pos hν
      (by norm_num) (by norm_num) v hns.periodic_u hvC01 hns.div_free θ₀ hp
      (holderC2_of_smooth_periodic θ₀ hθ₀ hp (by norm_num) (by norm_num))
    obtain ⟨hmax,hen⟩ := scalar_energy_max 1 ν (1/2) hν v hns.periodic_u hvC01 hns.div_free θ₀ θ hθ
    exact ⟨θ,hθ,huniq,hmax,hen⟩

end AnomDiss
