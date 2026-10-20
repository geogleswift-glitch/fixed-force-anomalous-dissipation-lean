module

public import RequestProject.ScalarMild
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-! # Spatial periodicity and real values for constructed scalar mild solutions -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- Translation in space leaves the bounded continuous slab function space invariant. -/
def translateSlabScalar {T : ℝ} (m : Pt 2) (u : SlabScalar T) : SlabScalar T :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => u (p.1, p.2 + m))
    (u.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))
    ‖u‖ (fun _ => u.norm_coe_le_norm _)

@[simp] lemma translateSlabScalar_apply {T : ℝ} (m : Pt 2) (u : SlabScalar T)
    (p : ScalarTimeSlab T) : translateSlabScalar m u p = u (p.1, p.2 + m) := rfl

lemma heatGradientKernel_translate (v : ℝ≥0) (f : Pt 2 → ℂ) (i : Fin 2)
    (m x : Pt 2) : heatGradientKernel v (fun y => f (y + m)) i x =
      heatGradientKernel v f i (x + m) := by
  unfold heatGradientKernel
  congr 2
  funext ζ
  dsimp only
  rw [show x + Real.sqrt v • ζ + m = x + m + Real.sqrt v • ζ by abel]

lemma duhamelComponent_translate (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2)
    (m x : Pt 2) (t : ℝ) : duhamelComponent ν (fun s y => F s (y + m)) i t x =
      duhamelComponent ν F i t (x + m) := by
  unfold duhamelComponent
  simp_rw [heatGradientKernel_translate]

lemma scalarMildMap_translate {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hb : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hf : IsPeriodic f)
    (m : Fin 2 → ℤ) (u : SlabScalar T) :
    scalarMildMap hν hT b f (translateSlabScalar (intVec m) u) =
      translateSlabScalar (intVec m) (scalarMildMap hν hT b f u) := by
  apply BoundedContinuousFunction.ext
  intro p
  simp only [scalarMildMap, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.sum_apply, slabHeatInitial_apply,
    slabDuhamel_apply, translateSlabScalar_apply]
  have hheat := (isQP_zero_iff.1 (heatOp_isQP (isQP_zero_iff.2 hf)
    (Real.toNNReal (2 * ν * (p.1 : ℝ))))) p.2 m
  rw [hheat]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : extendSlabScalar hT (b i * translateSlabScalar (intVec m) u) =
      fun s y => extendSlabScalar hT (b i * u) s (y + intVec m) := by
    funext s y
    simp only [extendSlabScalar, BoundedContinuousFunction.mul_apply, translateSlabScalar_apply]
    have hbp : b i (projIcc 0 T hT s, y + intVec m) = b i (projIcc 0 T hT s, y) :=
      hb i (projIcc 0 T hT s) y m
    rw [hbp]
  rw [he, duhamelComponent_translate]

/-- Periodicity follows from uniqueness of the constructed fixed point, by translation. -/
theorem scalar_mild_fixedPoint_periodic {ν T B : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hB : 0 ≤ B) (b : Fin 2 → SlabScalar T) (hb : ∀ i, ‖b i‖ ≤ B)
    (f : Pt 2 →ᵇ ℂ) (hsmall : scalarMildRate ν B T < 1)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∀ t, IsPeriodic (fun x => u (t, x)) := by
  obtain ⟨w, hw, huniq⟩ := exists_unique_scalar_mild_fixedPoint hν hT hB b hb f hsmall
  intro t x m
  have ht : scalarMildMap hν hT b f (translateSlabScalar (intVec m) u) =
      translateSlabScalar (intVec m) u := by
    rw [scalarMildMap_translate hν hT b f hbper hfper, hu]
  have he : translateSlabScalar (intVec m) u = u :=
    (huniq _ ht).trans (huniq u hu).symm
  exact congrArg (fun v : SlabScalar T => v (t, x)) he

lemma heatOp_star (v : ℝ≥0) (f : Pt 2 → ℂ) (x : Pt 2) :
    heatOp v (fun y => star (f y)) x = star (heatOp v f x) := by
  unfold heatOp
  simpa only [Complex.star_def] using (integral_conj (f := fun ζ => f (x + ζ)))

lemma heatGradientKernel_star (v : ℝ≥0) (f : Pt 2 → ℂ) (i : Fin 2) (x : Pt 2) :
    heatGradientKernel v (fun y => star (f y)) i x =
      star (heatGradientKernel v f i x) := by
  unfold heatGradientKernel
  rw [star_smul]
  simp only [star_trivial]
  congr 1
  simp only [Complex.star_def]
  rw [← integral_conj]
  congr 1
  funext ζ
  simp

lemma duhamelComponent_star (ν : ℝ) (F : ℝ → Pt 2 → ℂ) (i : Fin 2) (t : ℝ) (x : Pt 2) :
    duhamelComponent ν (fun s y => star (F s y)) i t x =
      star (duhamelComponent ν F i t x) := by
  unfold duhamelComponent
  simp_rw [heatGradientKernel_star]
  unfold intervalIntegral
  simp only [star_sub, Complex.star_def, integral_conj]

lemma scalarMildMap_star {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ) (u : SlabScalar T) :
    scalarMildMap hν hT (fun i => star (b i)) (star f) (star u) =
      star (scalarMildMap hν hT b f u) := by
  apply BoundedContinuousFunction.ext
  intro p
  simp only [scalarMildMap, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.sum_apply, slabHeatInitial_apply,
    slabDuhamel_apply, BoundedContinuousFunction.star_apply, star_sub, star_sum]
  rw [show (⇑(star f) : Pt 2 → ℂ) = (fun y => star (f y)) from rfl, heatOp_star]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : extendSlabScalar hT (star (b i) * star u) =
      fun s y => star (extendSlabScalar hT (b i * u) s y) := by
    funext s y
    simp [extendSlabScalar, mul_comm]
  rw [he, duhamelComponent_star]

/-- A real drift and real initial data produce real values, by conjugation and uniqueness. -/
theorem scalar_mild_fixedPoint_real {ν T B : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hB : 0 ≤ B) (b : Fin 2 → SlabScalar T) (hb : ∀ i, ‖b i‖ ≤ B)
    (f : Pt 2 →ᵇ ℂ) (hsmall : scalarMildRate ν B T < 1)
    (hbReal : ∀ i, star (b i) = b i) (hfReal : star f = f)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) : star u = u := by
  obtain ⟨w, hw, huniq⟩ := exists_unique_scalar_mild_fixedPoint hν hT hB b hb f hsmall
  have hbs : (fun i => star (b i)) = b := funext hbReal
  have hs := scalarMildMap_star hν hT b f u
  rw [hbs, hfReal, hu] at hs
  exact (huniq _ hs).trans (huniq u hu).symm

end AnomDiss
