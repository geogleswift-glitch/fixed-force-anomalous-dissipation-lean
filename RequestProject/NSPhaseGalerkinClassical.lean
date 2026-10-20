module

public import RequestProject.HeatDuhamelVectorClassical
public import RequestProject.NSPhaseGalerkinPressureTime
public import RequestProject.NSPhaseGalerkinMomentumSource
public import RequestProject.ParabolicMomentumSource

/-!
# The actual Galerkin limit is a classical Navier–Stokes solution

Earned first-order velocity and pressure regularity supplies all analytic
data of the true pointwise momentum source. Its proved genuine heat
representation gives the full second-order parabolic velocity bundle
and the original momentum equation. The same constructed pair satisfies
these original regularity classes at every exponent in `(0,1)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1000000

/-- All original parabolic regularity fields and the true pointwise
momentum equation are earned by the same genuine strong Galerkin limit. -/
theorem phaseGalerkin_l2_limit_parabolic_and_momentum
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    IsParabolicC12 1 β (phaseL2VelocityExtension U) ∧
      IsParabolicC01 1 β (phaseL2PressureExtension U) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        dt 1 (phaseL2VelocityExtension U) t x +
          conv (phaseL2VelocityExtension U t) (phaseL2VelocityExtension U t) x +
          grad (phaseL2PressureExtension U t) x =
            ν • lap (phaseL2VelocityExtension U t) x + gForce phase t x := by
  let v : ℝ → Pt 2 → Pt 2 := phaseL2VelocityExtension U
  let p : ℝ → Pt 2 → ℝ := phaseL2PressureExtension U
  let F : ℝ → Pt 2 → Pt 2 := phaseL2MomentumSource phase U
  have hv : IsParabolicC01 1 β v :=
    phaseGalerkin_l2_limit_velocity_isParabolicC01 ν hν phase hφ hU hβ₀ hβ₁
  have hp : IsParabolicC01 1 β p :=
    phaseGalerkin_l2_limit_real_pressure_parabolic_C01 ν hν phase hφ hU hβ₀ hβ₁
  have hvc : ∀ t : ℝ, v (projIcc 0 1 (by norm_num) t) = v t := by
    intro t
    simp only [v, phaseL2VelocityExtension, projIcc_val]
  have hpc : ∀ t : ℝ, p (projIcc 0 1 (by norm_num) t) = p t := by
    intro t
    funext x
    simp only [p, phaseL2PressureExtension, projIcc_val]
  have hsource (i : Fin 2) :
      Continuous (Function.uncurry fun s x => (F s x i : ℂ)) ∧
        ParHolder 1 β (fun s x => (F s x i : ℂ)) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ s x, ‖(F s x i : ℂ)‖ ≤ C) ∧
        (∃ H : ℝ, 0 ≤ H ∧ ∀ s x y,
          ‖(F s x i : ℂ) - (F s y i : ℂ)‖ ≤ H * ‖x - y‖ ^ β) := by
    have hs := momentumSourceComponent_analytic_data hβ₀ hβ₁ hv hp hvc hpc phase i
    have heq : momentumSourceComponent phase v p i = fun s x => (F s x i : ℂ) := by
      funext s x
      simp only [momentumSourceComponent, phaseL2MomentumSource, Pi.sub_apply, grad, F, v, p]
    rw [heq] at hs
    exact hs
  have hperiodic (i : Fin 2) (s : ℝ) : IsPeriodic (fun x => (F s x i : ℂ)) := by
    intro x n
    change ((phaseL2MomentumSource phase U s (x + intVec n) i : ℝ) : ℂ) = _
    rw [isPeriodic_phaseL2MomentumSource phase U s x n]
  have hdata (i : Fin 2) : ∃ C H : ℝ, 0 ≤ H ∧
      (∀ s x, ‖(F s x i : ℂ)‖ ≤ C) ∧
      (∀ s x y, ‖(F s x i : ℂ) - (F s y i : ℂ)‖ ≤ H * ‖x - y‖ ^ β) := by
    obtain ⟨C, _, hC⟩ := (hsource i).2.2.1
    obtain ⟨H, hH, hholder⟩ := (hsource i).2.2.2
    exact ⟨C, H, hH, hC, hholder⟩
  have hrep (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (fun x => (v t x i : ℂ)) = heatDuhamel ν (fun s x => (F s x i : ℂ)) t := by
    obtain ⟨C, _, hC⟩ := (hsource i).2.2.1
    change (fun x => (phaseL2VelocityExtension U t x i : ℂ)) = _
    rw [phaseL2VelocityExtension_of_mem U ht]
    exact phaseGalerkin_l2_limit_continuousVelocity_eq_heatDuhamel
      ν hν phase hφ hU i (hsource i).1 hC ⟨t, ht⟩
  obtain ⟨hC12, heq⟩ := vector_heatDuhamel_parabolic_and_equation
    hν hβ₀ hβ₁ v F (fun i => (hsource i).1) hperiodic hdata (fun i => (hsource i).2.1) hrep
  refine ⟨hC12, hp, fun t ht x => ?_⟩
  have he := heq t ht x
  change dt 1 v t x + conv (v t) (v t) x + grad (p t) x = ν • lap (v t) x + gForce phase t x
  rw [he]
  dsimp only [F, phaseL2MomentumSource]
  change ν • lap (v t) x + (gForce phase t x - conv (v t) (v t) x - grad (p t) x) +
    conv (v t) (v t) x + grad (p t) x = _
  abel

/-- The same actual reconstructed velocity and pressure solve the
original classical NS definition and enjoy every admissible exponent. -/
theorem phaseGalerkin_l2_limit_classical_all_beta
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U)) :
    IsClassicalNS 1 ν 0 (gForce phase) (phaseL2VelocityExtension U) (phaseL2PressureExtension U) ∧
      ∀ β : ℝ, 0 < β → β < 1 →
        IsParabolicC12 1 β (phaseL2VelocityExtension U) ∧
          IsParabolicC01 1 β (phaseL2PressureExtension U) := by
  obtain ⟨hv, hp, heq⟩ := phaseGalerkin_l2_limit_parabolic_and_momentum
    ν hν phase hφ hU (β := 1 / 2) (by norm_num) (by norm_num)
  constructor
  · refine {
      periodic_u := ?_
      periodic_p := ?_
      regular := ⟨1 / 2, by norm_num, by norm_num, hv, hp⟩
      init := ?_
      div_free := ?_
      eqn := heq }
    · intro t ht
      rw [phaseL2VelocityExtension_of_mem U ht]
      exact isPeriodic_phaseL2ContinuousVelocity U ⟨t, ht⟩
    · intro t ht
      rw [phaseL2PressureExtension_of_mem U ht]
      exact isPeriodic_torusRealPressure (U ⟨t, ht⟩)
    · rw [phaseL2VelocityExtension_of_mem U (by constructor <;> norm_num)]
      exact phaseGalerkin_l2_limit_continuousVelocity_initial ν hν phase hU
    · intro t ht x
      rw [phaseL2VelocityExtension_of_mem U ht]
      exact phaseGalerkin_l2_limit_continuousVelocity_solenoidal ν hν phase hφ hU ⟨t, ht⟩ x
  · intro β hβ₀ hβ₁
    have h := phaseGalerkin_l2_limit_parabolic_and_momentum ν hν phase hφ hU hβ₀ hβ₁
    exact ⟨h.1, h.2.1⟩

/-- For every positive viscosity and phase, one actual velocity-pressure
pair is a classical zero-initial solution and satisfies all original
parabolic Hölder exponents. This existence theorem has no NS interface
or classical-existence assumption. -/
theorem exists_phase_classical_all_beta (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
      IsClassicalNS 1 ν 0 (gForce phase) v p ∧
        ∀ β : ℝ, 0 < β → β < 1 → IsParabolicC12 1 β v ∧ IsParabolicC01 1 β p := by
  obtain ⟨φ, U, hφ, hU, _, _⟩ := exists_phaseGalerkin_l2_limit_uniform_h2_energy ν hν phase
  exact ⟨phaseL2VelocityExtension U, phaseL2PressureExtension U,
    phaseGalerkin_l2_limit_classical_all_beta ν hν phase hφ hU⟩

end AnomDiss
