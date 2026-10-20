module

public import RequestProject.ScalarMild
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Exponentially weighted Duhamel estimates on arbitrary finite time slabs -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The time exponential is an actual bounded continuous slab function. -/
def slabTimeWeight (a T : ℝ) : SlabScalar T :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (Real.exp (a * (p.1 : ℝ)) : ℂ))
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))
    (Real.exp (|a| * |T|)) (fun p => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      calc
        a * (p.1 : ℝ) ≤ |a * (p.1 : ℝ)| := le_abs_self _
        _ = |a| * |(p.1 : ℝ)| := abs_mul _ _
        _ ≤ |a| * |T| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg p.1.property.1]
          exact p.1.property.2.trans (le_abs_self T))

@[simp] lemma slabTimeWeight_apply (a T : ℝ) (p : ScalarTimeSlab T) :
    slabTimeWeight a T p = (Real.exp (a * (p.1 : ℝ)) : ℂ) := rfl

lemma slabTimeWeight_mul (a b T : ℝ) :
    slabTimeWeight a T * slabTimeWeight b T = slabTimeWeight (a + b) T := by
  apply BoundedContinuousFunction.ext
  intro p
  simp [Real.exp_add, add_mul]

@[simp] lemma slabTimeWeight_zero (T : ℝ) : slabTimeWeight 0 T = 1 := by
  apply BoundedContinuousFunction.ext
  intro p
  simp

@[simp] lemma slabTimeWeight_neg_mul (a T : ℝ) :
    slabTimeWeight (-a) T * slabTimeWeight a T = 1 := by
  rw [slabTimeWeight_mul]
  simp

@[simp] lemma slabTimeWeight_mul_neg (a T : ℝ) :
    slabTimeWeight a T * slabTimeWeight (-a) T = 1 := by
  rw [slabTimeWeight_mul]
  simp

lemma heatGradientKernel_const_mul (v : ℝ≥0) (c : ℂ) (f : Pt 2 → ℂ)
    (i : Fin 2) (x : Pt 2) : heatGradientKernel v (fun y => c * f y) i x =
      c * heatGradientKernel v f i x := by
  unfold heatGradientKernel
  have he : (fun ζ : Pt 2 => (ζ i : ℂ) * (c * f (x + Real.sqrt v • ζ))) =
      fun ζ => c * ((ζ i : ℂ) * f (x + Real.sqrt v • ζ)) := by
    funext ζ
    ring_nf
  rw [he, integral_const_mul]
  simp only [Complex.real_smul]
  ring_nf

lemma integrableOn_weighted_rpow {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * r))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ))
      (b := a) (by norm_num) (by norm_num) ha)

lemma integral_weighted_rpow_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ioi 0, r ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * r))) =
      Real.Gamma (1 / 2) / Real.sqrt a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 / 2 : ℝ))
    (r := a) (by norm_num) ha
  norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] at h
  rw [h, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), Real.sqrt_one]
  ring_nf

lemma integral_weighted_rpow_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, r ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * r))) ≤
      Real.Gamma (1 / 2) / Real.sqrt a := by
  rw [intervalIntegral.integral_of_le ht]
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun r : ℝ => r ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * r))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
  exact (setIntegral_mono_set (integrableOn_weighted_rpow ha) hn
    (Eventually.of_forall fun r hr => hr.1)).trans_eq (integral_weighted_rpow_Ioi ha)

/-- The weighted operator uses the previously constructed, continuous actual Duhamel operator. -/
def weightedSlabDuhamel {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (a : ℝ) (i : Fin 2) (F : SlabScalar T) : SlabScalar T :=
  slabTimeWeight (-a) T * slabDuhamel hν hT i (slabTimeWeight a T * F)

lemma weightedLaggedDuhamel_eq {ν T : ℝ} (hT : 0 ≤ T) (a : ℝ) (F : SlabScalar T)
    (i : Fin 2) (p : ScalarTimeSlab T) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) p.1) :
    (Real.exp (-a * (p.1 : ℝ)) : ℂ) *
        laggedDuhamelKernel ν (extendSlabScalar hT (slabTimeWeight a T * F)) i
          ((p.1 : ℝ), p.2) r =
      (Real.exp (-(a * r)) : ℂ) *
        laggedDuhamelKernel ν (extendSlabScalar hT F) i ((p.1 : ℝ), p.2) r := by
  have hs : (p.1 : ℝ) - r ∈ Icc (0 : ℝ) T := by
    constructor
    · linarith [hr.2]
    · linarith [hr.1, p.1.property.2]
  have he : extendSlabScalar hT (slabTimeWeight a T * F) ((p.1 : ℝ) - r) =
      fun y => (Real.exp (a * ((p.1 : ℝ) - r)) : ℂ) *
        extendSlabScalar hT F ((p.1 : ℝ) - r) y := by
    funext y
    rw [extendSlabScalar_of_mem hT _ hs, extendSlabScalar_of_mem hT _ hs]
    rfl
  unfold laggedDuhamelKernel
  rw [he, heatGradientKernel_const_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring_nf

/-- Exponential weighting gives a time-independent operator bound proportional to `a⁻¹/²`. -/
theorem norm_weightedSlabDuhamel_le {ν T a : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (ha : 0 < a) (i : Fin 2) (F : SlabScalar T) :
    ‖weightedSlabDuhamel hν hT a i F‖ ≤
      duhamelScale ν ‖F‖ * (Real.Gamma (1 / 2) / Real.sqrt a) := by
  have hscale : 0 ≤ duhamelScale ν ‖F‖ := duhamelScale_nonneg (norm_nonneg _)
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p => ?_
  change ‖(Real.exp (-a * (p.1 : ℝ)) : ℂ) *
    duhamelComponent ν (extendSlabScalar hT (slabTimeWeight a T * F)) i p.1 p.2‖ ≤ _
  rw [duhamelComponent_eq_lagged, ← intervalIntegral.integral_const_mul]
  have hi : IntervalIntegrable
      (fun r : ℝ => duhamelScale ν ‖F‖ * (r ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * r))))
      volume 0 p.1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le p.1.property.1]
    exact ((integrableOn_weighted_rpow ha).mono_set (fun _ hr => hr.1)).const_mul _
  calc
    ‖∫ r in (0 : ℝ)..(p.1 : ℝ), (Real.exp (-a * (p.1 : ℝ)) : ℂ) *
        laggedDuhamelKernel ν (extendSlabScalar hT (slabTimeWeight a T * F)) i
          ((p.1 : ℝ), p.2) r‖
        ≤ ∫ r in (0 : ℝ)..(p.1 : ℝ), duhamelScale ν ‖F‖ *
            (r ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * r))) := by
      refine intervalIntegral.norm_integral_le_of_norm_le p.1.property.1
        (Eventually.of_forall fun r hr => ?_) hi
      rw [weightedLaggedDuhamel_eq hT a F i p ⟨hr.1.le, hr.2⟩,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h := norm_laggedDuhamelKernel_le hν (continuous_extendSlabScalar hT F)
        (norm_extendSlabScalar_le hT F) i ((p.1 : ℝ), p.2) hr.1
      apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
      ring_nf
    _ ≤ duhamelScale ν ‖F‖ * (Real.Gamma (1 / 2) / Real.sqrt a) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_weighted_rpow_le ha p.1.property.1) hscale

lemma slabDuhamel_sub {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (i : Fin 2) (F G : SlabScalar T) :
    slabDuhamel hν hT i F - slabDuhamel hν hT i G = slabDuhamel hν hT i (F - G) := by
  apply BoundedContinuousFunction.ext
  intro p
  simp only [BoundedContinuousFunction.sub_apply, slabDuhamel_apply]
  unfold duhamelComponent
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_duhamelComponent hν (continuous_extendSlabScalar hT F)
      (norm_extendSlabScalar_le hT F) i p.1.property.1 p.2)
    (intervalIntegrable_duhamelComponent hν (continuous_extendSlabScalar hT G)
      (norm_extendSlabScalar_le hT G) i p.1.property.1 p.2)]
  apply intervalIntegral.integral_congr
  intro s _
  exact (heatGradientKernel_sub
    ((continuous_extendSlabScalar hT F).comp (continuous_const.prodMk continuous_id))
    ((continuous_extendSlabScalar hT G).comp (continuous_const.prodMk continuous_id))
    (norm_extendSlabScalar_le hT F s) (norm_extendSlabScalar_le hT G s) _ i p.2).symm

lemma weightedSlabDuhamel_sub {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (a : ℝ) (i : Fin 2) (F G : SlabScalar T) :
    weightedSlabDuhamel hν hT a i F - weightedSlabDuhamel hν hT a i G =
      weightedSlabDuhamel hν hT a i (F - G) := by
  unfold weightedSlabDuhamel
  rw [← mul_sub, slabDuhamel_sub, ← mul_sub]

theorem weightedSlabDuhamel_uniform_distance {ν T a : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (ha : 0 < a) (i : Fin 2) (F G : SlabScalar T) :
    ‖weightedSlabDuhamel hν hT a i F - weightedSlabDuhamel hν hT a i G‖ ≤
      duhamelScale ν ‖F - G‖ * (Real.Gamma (1 / 2) / Real.sqrt a) := by
  rw [weightedSlabDuhamel_sub]
  exact norm_weightedSlabDuhamel_le hν hT ha i (F - G)

end AnomDiss
