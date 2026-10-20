module

public import RequestProject.ScalarWeightedDuhamel
public import RequestProject.ScalarMildSymmetry

/-!
# Scalar mild existence on every finite time slab

Exponential weighting makes the true Volterra operator contract on an arbitrary
finite slab. The inverse weighting gives the original, unweighted Gaussian
integral equation. No parabolic existence theorem is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

def weightedScalarMildMap {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (a : ℝ) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ) (u : SlabScalar T) : SlabScalar T :=
  slabTimeWeight (-a) T * slabHeatInitial ν T f -
    ∑ i : Fin 2, weightedSlabDuhamel hν hT a i (b i * u)

def weightedScalarMildRate (ν B a : ℝ) : ℝ :=
  2 * duhamelScale ν B * (Real.Gamma (1 / 2) / Real.sqrt a)

lemma weightedScalarMildRate_nonneg {ν B a : ℝ} (hB : 0 ≤ B) :
    0 ≤ weightedScalarMildRate ν B a := by
  unfold weightedScalarMildRate
  exact mul_nonneg (mul_nonneg (by norm_num) (duhamelScale_nonneg hB)) (by positivity)

theorem weightedScalarMildMap_uniform_distance {ν T a B : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (ha : 0 < a)
    (b : Fin 2 → SlabScalar T) (hb : ∀ i, ‖b i‖ ≤ B)
    (f : Pt 2 →ᵇ ℂ) (u w : SlabScalar T) :
    ‖weightedScalarMildMap hν hT a b f u - weightedScalarMildMap hν hT a b f w‖ ≤
      weightedScalarMildRate ν B a * ‖u - w‖ := by
  have hg : 0 ≤ Real.Gamma (1 / 2) / Real.sqrt a := by positivity
  have hd : ∀ i : Fin 2,
      ‖weightedSlabDuhamel hν hT a i (b i * u) - weightedSlabDuhamel hν hT a i (b i * w)‖ ≤
        duhamelScale ν B * (Real.Gamma (1 / 2) / Real.sqrt a) * ‖u - w‖ := by
    intro i
    have hs : ‖b i * u - b i * w‖ ≤ B * ‖u - w‖ := by
      rw [← mul_sub]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
    calc
      ‖weightedSlabDuhamel hν hT a i (b i * u) - weightedSlabDuhamel hν hT a i (b i * w)‖
          ≤ duhamelScale ν ‖b i * u - b i * w‖ * (Real.Gamma (1 / 2) / Real.sqrt a) :=
        weightedSlabDuhamel_uniform_distance hν hT ha i _ _
      _ ≤ duhamelScale ν (B * ‖u - w‖) * (Real.Gamma (1 / 2) / Real.sqrt a) :=
        mul_le_mul_of_nonneg_right (duhamelScale_mono hs) hg
      _ = duhamelScale ν B * (Real.Gamma (1 / 2) / Real.sqrt a) * ‖u - w‖ := by
        rw [duhamelScale_mul]
        ring
  calc
    ‖weightedScalarMildMap hν hT a b f u - weightedScalarMildMap hν hT a b f w‖
        = ‖∑ i : Fin 2, (weightedSlabDuhamel hν hT a i (b i * u) -
            weightedSlabDuhamel hν hT a i (b i * w))‖ := by
      unfold weightedScalarMildMap
      rw [sub_sub_sub_cancel_left, norm_sub_rev, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin 2, ‖weightedSlabDuhamel hν hT a i (b i * u) -
          weightedSlabDuhamel hν hT a i (b i * w)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, duhamelScale ν B * (Real.Gamma (1 / 2) / Real.sqrt a) * ‖u - w‖ :=
      Finset.sum_le_sum fun i _ => hd i
    _ = weightedScalarMildRate ν B a * ‖u - w‖ := by
      simp [weightedScalarMildRate]
      ring

lemma scalarMildMap_weight_transform {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (a : ℝ) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ) (w : SlabScalar T) :
    slabTimeWeight (-a) T * scalarMildMap hν hT b f (slabTimeWeight a T * w) =
      weightedScalarMildMap hν hT a b f w := by
  unfold scalarMildMap weightedScalarMildMap weightedSlabDuhamel
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ring

lemma weightedScalarMildMap_unweight {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (a : ℝ) (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ) (u : SlabScalar T) :
    weightedScalarMildMap hν hT a b f (slabTimeWeight (-a) T * u) =
      slabTimeWeight (-a) T * scalarMildMap hν hT b f u := by
  have h := scalarMildMap_weight_transform hν hT a b f (slabTimeWeight (-a) T * u)
  simpa only [← mul_assoc, slabTimeWeight_mul_neg, one_mul] using h.symm

/-- An explicit exponential weight always makes the full finite slab map contract. -/
def scalarGlobalWeight (ν B : ℝ) : ℝ :=
  (1 + 4 * duhamelScale ν B * Real.Gamma (1 / 2)) ^ 2

lemma scalarGlobalWeight_pos {ν B : ℝ} (hB : 0 ≤ B) : 0 < scalarGlobalWeight ν B := by
  have hs := duhamelScale_nonneg (ν := ν) hB
  unfold scalarGlobalWeight
  exact sq_pos_of_pos (by positivity)

lemma weightedScalarMildRate_scalarGlobalWeight_lt_one {ν B : ℝ} (hB : 0 ≤ B) :
    weightedScalarMildRate ν B (scalarGlobalWeight ν B) < 1 := by
  have hs := duhamelScale_nonneg (ν := ν) hB
  have hg : 0 ≤ Real.Gamma (1 / 2) := by positivity
  have hden : 0 < 1 + 4 * duhamelScale ν B * Real.Gamma (1 / 2) := by positivity
  unfold weightedScalarMildRate scalarGlobalWeight
  rw [Real.sqrt_sq hden.le, ← mul_div_assoc, div_lt_one hden]
  nlinarith [mul_nonneg hs hg]

/-- Every finite slab has one bounded continuous solution of the original scalar
mild equation, constructed by an exponentially weighted contraction. -/
theorem exists_unique_global_scalar_mild {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ) :
    ∃! u : SlabScalar T, scalarMildMap hν hT b f u = u := by
  let B := ‖b 0‖ + ‖b 1‖
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb : ∀ i : Fin 2, ‖b i‖ ≤ B := by
    intro i
    fin_cases i
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  let a := scalarGlobalWeight ν B
  have ha : 0 < a := scalarGlobalWeight_pos hB
  let K : ℝ≥0 := ⟨weightedScalarMildRate ν B a, weightedScalarMildRate_nonneg hB⟩
  have hc : ContractingWith K (weightedScalarMildMap hν hT a b f) := by
    refine ⟨weightedScalarMildRate_scalarGlobalWeight_lt_one hB,
      LipschitzWith.of_dist_le_mul fun u w => ?_⟩
    simp only [dist_eq_norm]
    change ‖weightedScalarMildMap hν hT a b f u - weightedScalarMildMap hν hT a b f w‖ ≤
      weightedScalarMildRate ν B a * ‖u - w‖
    exact weightedScalarMildMap_uniform_distance hν hT ha b hb f u w
  let w := hc.fixedPoint (weightedScalarMildMap hν hT a b f)
  have hw : weightedScalarMildMap hν hT a b f w = w := hc.fixedPoint_isFixedPt
  let u := slabTimeWeight a T * w
  have hu : scalarMildMap hν hT b f u = u := by
    have hh := scalarMildMap_weight_transform hν hT a b f w
    rw [hw] at hh
    have hh' := congrArg (fun z : SlabScalar T => slabTimeWeight a T * z) hh
    simpa only [← mul_assoc, slabTimeWeight_mul_neg, one_mul] using hh'
  refine ⟨u, hu, fun z hz => ?_⟩
  have hzw : weightedScalarMildMap hν hT a b f (slabTimeWeight (-a) T * z) =
      slabTimeWeight (-a) T * z := by
    rw [weightedScalarMildMap_unweight, hz]
  have he : slabTimeWeight (-a) T * z = w := hc.fixedPoint_unique hzw
  have he' := congrArg (fun y : SlabScalar T => slabTimeWeight a T * y) he
  simpa only [← mul_assoc, slabTimeWeight_mul_neg, one_mul] using he'

/-- The full-slab constructed solution inherits periodicity from the actual data. -/
theorem global_scalar_mild_fixedPoint_periodic {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∀ t, IsPeriodic (fun x => u (t, x)) := by
  obtain ⟨w, hw, huniq⟩ := exists_unique_global_scalar_mild hν hT b f
  intro t x m
  have ht : scalarMildMap hν hT b f (translateSlabScalar (intVec m) u) =
      translateSlabScalar (intVec m) u := by
    rw [scalarMildMap_translate hν hT b f hbper hfper, hu]
  have he : translateSlabScalar (intVec m) u = u :=
    (huniq _ ht).trans (huniq u hu).symm
  exact congrArg (fun v : SlabScalar T => v (t, x)) he

/-- Real data produce real values on the full finite slab. -/
theorem global_scalar_mild_fixedPoint_real {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbReal : ∀ i, star (b i) = b i) (hfReal : star f = f)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) : star u = u := by
  obtain ⟨w, hw, huniq⟩ := exists_unique_global_scalar_mild hν hT b f
  have hbs : (fun i => star (b i)) = b := funext hbReal
  have hs := scalarMildMap_star hν hT b f u
  rw [hbs, hfReal, hu] at hs
  exact (huniq _ hs).trans (huniq u hu).symm

end AnomDiss
