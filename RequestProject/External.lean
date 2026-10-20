module

public import RequestProject.ScalarEnergy

/-!
# Section 1: the two external results, the scalar maximum principle / energy identity

The two analytic existence/regularity results that the paper uses without proof
(External Results 1.5 and 1.6) are recorded as propositions `ExternalNS2D` and
`ExternalScalar`.  They are *not* assumed as axioms: every theorem that depends on them takes
them as explicit hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- **External Result 1.5** (global classical solutions of the forced 2D Navier–Stokes
equations, Temam + parabolic Schauder theory), in the form used by the paper: for smooth
mean-zero divergence-free initial data and a mean-zero force which is smooth in time with values
in every `C^α_σ(𝕋²)`, there is a solution `(v,p)` which is classical on `[0,T]`, lies in
`C^{1+β/2,2+β}` (velocity) and `C^{β/2,1+β}` (pressure) for every `0 < β < 1`, satisfies the
kinetic energy identity, and is unique among classical solutions. -/
def ExternalNS2D : Prop :=
  ∀ (T ν : ℝ), 0 < T → 0 < ν → ∀ (v₀ : Pt 2 → Pt 2) (g : ℝ → Pt 2 → Pt 2),
    ContDiff ℝ ∞ v₀ → IsPeriodic v₀ → (∀ x, divergence v₀ x = 0) →
    (∫ x in cell 2, v₀ x) = 0 → IsTimeSmoothForce g → (∀ t, (∫ x in cell 2, g t x) = 0) →
    ∃ (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
      (∀ β, 0 < β → β < 1 → IsParabolicC12 T β v ∧ IsParabolicC01 T β p) ∧
      IsClassicalNS T ν v₀ g v p ∧
      (∀ t ∈ Icc 0 T, l2sqV (v t) / 2 + ν * ∫ s in (0 : ℝ)..t, ∫ x in cell 2, gradSqV (v s) x
          = l2sqV v₀ / 2 + ∫ s in (0 : ℝ)..t, ∫ x in cell 2, dot (g s x) (v s x)) ∧
      ∀ v' p', IsClassicalNS T ν v₀ g v' p' → ∀ t ∈ Icc 0 T, v' t = v t

/-- **External Result 1.6** (linear parabolic theory, Ladyzhenskaya–Solonnikov–Ural'tseva):
for a divergence-free periodic drift in `C^{β/2,1+β}` and initial data in `C^{2+β}`, the
advection–diffusion equation has a unique classical solution, and it lies in
`C^{1+β/2,2+β}`. -/
def ExternalScalar : Prop :=
  ∀ (T ν β : ℝ), 0 < T → 0 < ν → 0 < β → β < 1 → ∀ (v : ℝ → Pt 2 → Pt 2),
    (∀ t ∈ Icc 0 T, IsPeriodic (v t)) → IsParabolicC01 T β v →
    (∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0) →
    ∀ θ₀ : Pt 2 → ℝ, IsPeriodic θ₀ → IsHolderC2 β θ₀ →
    ∃ θ : ℝ → Pt 2 → ℝ, IsParabolicC12 T β θ ∧ IsClassicalScalar T ν v θ₀ θ ∧
      ∀ θ', IsClassicalScalar T ν v θ₀ θ' → ∀ t ∈ Icc 0 T, θ' t = θ t

/-- **Lemma 1.7** (maximum principle and scalar energy identity).  For a periodic
divergence-free drift in `C^{β/2,1+β}` and a classical solution `θ` of the advection–diffusion
equation, `‖θ(t)‖_∞ ≤ ‖θ₀‖_∞` and `½‖θ(t)‖₂² + ν∫₀ᵗ‖∇θ‖₂² = ½‖θ₀‖₂²`.

The proof does not need the side conditions `0 < T` and `0 < β < 1` of the paper, so they
have been dropped; of the drift regularity only `v(t) ∈ C¹` is used. -/
theorem scalar_energy_max (T ν β : ℝ) (hν : 0 < ν)
    (v : ℝ → Pt 2 → Pt 2) (hvper : ∀ t ∈ Icc 0 T, IsPeriodic (v t))
    (hvreg : IsParabolicC01 T β v) (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (θ : ℝ → Pt 2 → ℝ) (hθ : IsClassicalScalar T ν v θ₀ θ) :
    (∀ M, (∀ x, |θ₀ x| ≤ M) → ∀ t ∈ Icc 0 T, ∀ x, |θ t x| ≤ M) ∧
    (∀ t ∈ Icc 0 T, l2sq (θ t) / 2 + dissipation ν θ t = l2sq θ₀ / 2) := by
  obtain ⟨β', -, -, reg⟩ := hθ.regular
  refine ⟨fun M hM => ?_, fun t ht =>
    energy_identity_core T ν v hvper hvreg.smooth_x hvdiv θ₀ θ hθ t ht⟩
  refine max_principle_abs T ν hν.le v θ reg.continuousOn hθ.periodic reg.smooth_x reg.diff_t
    hθ.eqn M ?_
  rw [hθ.init]; exact hM

end AnomDiss
