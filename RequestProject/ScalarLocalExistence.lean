module

public import RequestProject.ScalarMildSymmetry
public import RequestProject.ScalarStages

/-!
# Local scalar mild existence for the actual parabolic drift data

This specializes the fixed-point construction to the real, periodic data in
`ExternalScalar`. The conclusion is an actual Gaussian integral equation on a
positive interval. It does not yet assert the required classical Hölder regularity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

lemma IsParabolicC01.continuousOn {T β : ℝ} (hβ : 0 < β)
    {v : ℝ → Pt 2 → Pt 2} (hv : IsParabolicC01 T β v) :
    ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ) :=
  continuousOn_of_timeHolder (by positivity) (fun t ht => (hv.smooth_x t ht).continuous)
    hv.holder_time

/-- A component of the supplied real drift, as a complex bounded continuous slab function. -/
def slabDriftComponent {T : ℝ} (v : ℝ → Pt 2 → Pt 2)
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (i : Fin 2) : SlabScalar T :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (v p.1 p.2 i : ℂ))
    ((Complex.continuous_ofReal.comp ((continuous_apply i).comp
      (hc.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p => ⟨p.1.property, mem_univ _⟩)))))
    C (fun p => by
      simpa only [Complex.norm_real] using
        (norm_le_pi_norm (v p.1 p.2) i).trans (hC p.1 p.1.property p.2))

@[simp] lemma slabDriftComponent_apply {T : ℝ} (v : ℝ → Pt 2 → Pt 2)
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (i : Fin 2) (p : ScalarTimeSlab T) : slabDriftComponent v hc C hC i p =
      (v p.1 p.2 i : ℂ) := rfl

lemma slabDriftComponent_real {T : ℝ} (v : ℝ → Pt 2 → Pt 2)
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (i : Fin 2) : star (slabDriftComponent v hc C hC i) = slabDriftComponent v hc C hC i := by
  apply BoundedContinuousFunction.ext
  intro p
  simp

lemma slabDriftComponent_periodic {T : ℝ} (v : ℝ → Pt 2 → Pt 2)
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (i : Fin 2) (t : Icc (0 : ℝ) T) :
    IsPeriodic (fun x => slabDriftComponent v hc C hC i (t, x)) := by
  intro x m
  simp only [slabDriftComponent_apply]
  rw [hp t t.property x m]

/-- A real bounded continuous mild solution is constructed for the actual drift
and initial data on an explicitly positive shorter interval. -/
theorem exists_real_periodic_local_scalar_mild {T ν β : ℝ}
    (hT : 0 < T) (hν : 0 < ν) (hβ : 0 < β)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθcont : Continuous θ₀) (hθper : IsPeriodic θ₀) :
    ∃ (S : ℝ) (θ : ℝ → Pt 2 → ℝ), 0 < S ∧ S ≤ T ∧
      Continuous (Function.uncurry θ) ∧
      (∃ C, ∀ t x, |θ t x| ≤ C) ∧
      (∀ t, IsPeriodic (θ t)) ∧ θ 0 = θ₀ ∧
      ∀ t ∈ Icc (0 : ℝ) S, ∀ x,
        (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
          ∑ i : Fin 2, duhamelComponent ν
            (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x := by
  have hvc := hv.continuousOn hβ
  obtain ⟨C, hC⟩ := hv.bdd
  let b : Fin 2 → SlabScalar T := slabDriftComponent v hvc C hC
  have hfcont : Continuous (fun x => (θ₀ x : ℂ)) := Complex.continuous_ofReal.comp hθcont
  have hfper : IsPeriodic (fun x => (θ₀ x : ℂ)) := fun x m => by
    dsimp only
    rw [hθper x m]
  obtain ⟨C₀, hC₀⟩ := (isQP_zero_iff.2 hfper).bdd hfcont
  let f : Pt 2 →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (θ₀ x : ℂ)) hfcont C₀ hC₀
  let B := ‖b 0‖ + ‖b 1‖
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let S := scalarLocalTime ν B T
  have hS : 0 < S := scalarLocalTime_pos hT hB
  have hST : S ≤ T := scalarLocalTime_le ν B T
  let bs : Fin 2 → SlabScalar S := fun i => restrictSlabScalar hST (b i)
  have hbs : ∀ i : Fin 2, ‖bs i‖ ≤ B := by
    intro i
    apply (norm_restrictSlabScalar_le hST (b i)).trans
    fin_cases i
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hsmall : scalarMildRate ν B S < 1 := scalarMildRate_scalarLocalTime_lt_one hB
  obtain ⟨u, hu, _⟩ := exists_unique_scalar_mild_fixedPoint hν hS.le hB bs hbs f hsmall
  have hbsper : ∀ i t, IsPeriodic (fun x => bs i (t, x)) := by
    intro i t x m
    change (v (t : ℝ) (x + intVec m) i : ℂ) = (v (t : ℝ) x i : ℂ)
    rw [hvper t ⟨t.property.1, t.property.2.trans hST⟩ x m]
  have hbReal : ∀ i, star (bs i) = bs i := by
    intro i
    apply BoundedContinuousFunction.ext
    intro p
    change star (v (p.1 : ℝ) p.2 i : ℂ) = (v (p.1 : ℝ) p.2 i : ℂ)
    simp
  have hfReal : star f = f := by
    apply BoundedContinuousFunction.ext
    intro x
    change star (θ₀ x : ℂ) = (θ₀ x : ℂ)
    simp
  have hureal := scalar_mild_fixedPoint_real hν hS.le hB bs hbs f hsmall hbReal hfReal hu
  have huper := scalar_mild_fixedPoint_periodic hν hS.le hB bs hbs f hsmall hbsper
    (show IsPeriodic f from hfper) hu
  have huim : ∀ p, (u p).im = 0 := by
    intro p
    have hh := congrArg (fun w : SlabScalar S => (w p).im) hureal
    simp only [BoundedContinuousFunction.star_apply, Complex.star_def, Complex.conj_im] at hh
    linarith
  let θ : ℝ → Pt 2 → ℝ := fun s x => (extendSlabScalar hS.le u s x).re
  have hθcomplex : ∀ s x, (θ s x : ℂ) = extendSlabScalar hS.le u s x := by
    intro s x
    apply Complex.ext
    · rfl
    · simpa [θ, extendSlabScalar] using (huim (projIcc 0 S hS.le s, x)).symm
  have he : ∀ p : ScalarTimeSlab S, u p =
      heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f p.2 -
        ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hS.le (bs i * u)) i p.1 p.2 := by
    intro p
    have hh := congrArg (fun w : SlabScalar S => w p) hu
    simpa [scalarMildMap] using hh.symm
  refine ⟨S, θ, hS, hST, Complex.continuous_re.comp (continuous_extendSlabScalar hS.le u),
    ⟨‖u‖, fun t x => (Complex.abs_re_le_norm _).trans (norm_extendSlabScalar_le hS.le u t x)⟩,
    ?_, ?_, ?_⟩
  · intro t x m
    exact congrArg Complex.re (huper (projIcc 0 S hS.le t) x m)
  · funext x
    have hh := he (⟨0, ⟨le_rfl, hS.le⟩⟩, x)
    simp only [mul_zero, Real.toNNReal_zero, duhamelComponent_zero, Finset.sum_const_zero,
      sub_zero, heatOp_zero f.continuous] at hh
    have hext := extendSlabScalar_of_mem hS.le u (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl, hS.le⟩) x
    change (extendSlabScalar hS.le u 0 x).re = θ₀ x
    rw [hext, hh]
    rfl
  · intro t ht x
    rw [hθcomplex, extendSlabScalar_of_mem hS.le u ht, he (⟨t, ht⟩, x)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold duhamelComponent
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) S := by
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    dsimp only
    congr 1
    funext y
    rw [extendSlabScalar_of_mem hS.le (bs i * u) hs', hθcomplex,
      extendSlabScalar_of_mem hS.le u hs']
    rfl

end AnomDiss
