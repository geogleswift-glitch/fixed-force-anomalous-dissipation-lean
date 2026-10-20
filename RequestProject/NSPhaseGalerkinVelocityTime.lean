module

public import RequestProject.NSPhaseGalerkinVelocitySpatial
public import RequestProject.NSPhaseGalerkinTimeBelowOne
public import RequestProject.FourierSeriesTimeRegularity
public import RequestProject.ParabolicFirstOrderOperations

/-!
# Genuine parabolic first-order velocity regularity

The real continuous representative is extended by constant endpoint
values outside the unit time interval. Its earned coefficient increment
moduli give the actual value and first-derivative time Hölder estimates.
Together with the proved spatial estimates they give every original
`IsParabolicC01` field, without a classical NS existence premise.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction
noncomputable section
namespace AnomDiss

set_option maxHeartbeats 1000000

def phaseL2VelocityExtension (U : GalerkinTime →ᵇ TorusVelocityL2)
    (s : ℝ) : Pt 2 → Pt 2 :=
  phaseL2ContinuousVelocity U (projIcc 0 1 (by norm_num) s)

theorem phaseL2VelocityExtension_of_mem (U : GalerkinTime →ᵇ TorusVelocityL2)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    phaseL2VelocityExtension U s = phaseL2ContinuousVelocity U ⟨s, hs⟩ := by
  simp only [phaseL2VelocityExtension, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs]

theorem phaseGalerkin_l2_limit_velocity_value_and_partial_time_holder
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    TimeHolder 1 (β/2) (phaseL2VelocityExtension U) ∧
      ∀ j : Fin 2, TimeHolder 1 (β/2) (fun s => pd j (phaseL2VelocityExtension U s)) := by
  obtain ⟨C, hC, htime⟩ := phaseGalerkin_l2_limit_uniform_first_moment_time_holder
    ν hν phase hφ hU hβ0 hβ1
  obtain ⟨M, hM, hm⟩ := phaseGalerkin_l2_limit_spatial_holder_moment
    ν hν phase hφ hU (β := 0) (by norm_num) (by norm_num)
  have ha (i : Fin 2) (t : GalerkinTime) :=
    (summable_absolute_and_first_moment_of_holder_moment (by norm_num : (0 : ℝ) ≤ 0) (hm i t).1).1
  have hd (i : Fin 2) (t : GalerkinTime) :=
    (summable_absolute_and_first_moment_of_holder_moment (by norm_num : (0 : ℝ) ≤ 0) (hm i t).1).2
  have hcoeff := fun i t => (hm i t).1
  constructor
  · refine ⟨C, fun t ht s hs x => ?_⟩
    rw [phaseL2VelocityExtension_of_mem U ht, phaseL2VelocityExtension_of_mem U hs]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _))).mpr
    intro i
    change ‖(complexFourierSeries (fun k => l2FourierCoeff k i (U ⟨t,ht⟩)) x).re -
      (complexFourierSeries (fun k => l2FourierCoeff k i (U ⟨s,hs⟩)) x).re‖ ≤ _
    rw [Real.norm_eq_abs, ← Complex.sub_re]
    apply (Complex.abs_re_le_norm _).trans
    exact norm_complexFourierSeries_sub_le_first_moment (ha i ⟨t,ht⟩) (ha i ⟨s,hs⟩)
      (htime i ⟨s,hs⟩ ⟨t,ht⟩).1 (htime i ⟨s,hs⟩ ⟨t,ht⟩).2 x
  · intro j
    refine ⟨‖(2*π*Complex.I : ℂ)‖*C, fun t ht s hs x => ?_⟩
    change ‖pd j (phaseL2VelocityExtension U t) x-pd j (phaseL2VelocityExtension U s) x‖ ≤ _
    rw [phaseL2VelocityExtension_of_mem U ht, phaseL2VelocityExtension_of_mem U hs]
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg _) hC) (Real.rpow_nonneg (abs_nonneg _) _))).mpr
    intro i
    simp only [Pi.sub_apply,
      pd_phaseL2ContinuousVelocity_component_of_holder_moment (by norm_num : (0 : ℝ) ≤ 0) hcoeff]
    rw [Real.norm_eq_abs, ← Complex.sub_re]
    apply (Complex.abs_re_le_norm _).trans
    have h := norm_pd_complexFourierSeries_sub_le_first_moment
      (ha i ⟨t,ht⟩) (ha i ⟨s,hs⟩) (hd i ⟨t,ht⟩) (hd i ⟨s,hs⟩)
      (htime i ⟨s,hs⟩ ⟨t,ht⟩).1 (htime i ⟨s,hs⟩ ⟨t,ht⟩).2 j x
    exact h.trans_eq (by ring)

theorem phaseGalerkin_l2_limit_velocity_isParabolicC01
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsParabolicC01 1 β (phaseL2VelocityExtension U) := by
  obtain ⟨M, hM, hc, hb, hh⟩ := phaseGalerkin_l2_limit_spatial_C1_holder
    ν hν phase hφ hU hβ0.le hβ1
  obtain ⟨hvtime, hdtime⟩ := phaseGalerkin_l2_limit_velocity_value_and_partial_time_holder
    ν hν phase hφ hU hβ0 hβ1
  exact {
    smooth_x := fun t _ => hc (projIcc 0 1 (by norm_num) t)
    bdd := ⟨phaseL2VelocityAbsoluteBound ν phase, fun t _ x =>
      norm_phaseL2ContinuousVelocity_le ν hν phase hφ hU _ x⟩
    holder_time := hvtime
    bdd_d1 := fun j => ⟨‖(2*π*Complex.I : ℂ)‖*M, fun t _ x => hb _ j x⟩
    holder_d1 := fun j => parHolder_of_spatial_time
      ⟨fourierSeriesDerivativeHolderConstant β*M, fun t _ x y => hh _ j x y⟩ (hdtime j) }

theorem continuous_phaseL2VelocityExtension
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2} (hφ : StrictMono φ)
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U)) :
    Continuous (Function.uncurry (phaseL2VelocityExtension U)) := by
  have hv : IsParabolicC01 1 (1 / 2 : ℝ) (phaseL2VelocityExtension U) :=
    phaseGalerkin_l2_limit_velocity_isParabolicC01 ν hν phase hφ hU (by norm_num) (by norm_num)
  have hpar : ParHolder 1 (1 / 2 : ℝ) (phaseL2VelocityExtension U) :=
    hv.parHolder (by norm_num) (by norm_num)
  have hclamp : ∀ t : ℝ,
      phaseL2VelocityExtension U (projIcc 0 1 (by norm_num) t) = phaseL2VelocityExtension U t := by
    intro t
    simp only [phaseL2VelocityExtension, projIcc_val]
  exact continuous_of_parHolder_unit_clamped (by norm_num : (0 : ℝ) < 1 / 2) hpar hclamp

end AnomDiss
