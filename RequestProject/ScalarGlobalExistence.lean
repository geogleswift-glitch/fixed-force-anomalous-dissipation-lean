module

public import RequestProject.ScalarGlobalMild
public import RequestProject.ScalarLocalExistence

/-!
# Full finite-slab scalar mild existence for the original real periodic data

The constructed solution satisfies the genuine unweighted Gaussian integral
equation on `[0,T]`. Classical differentiability and parabolic Hölder estimates
are still further regularity theorems, and are not assumed here.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The actual real periodic drift data admit a bounded continuous mild solution
on the entire supplied finite interval, constructed by exponential weighting. -/
theorem exists_real_periodic_global_scalar_mild {T ν β : ℝ}
    (hT : 0 ≤ T) (hν : 0 < ν) (hβ : 0 < β)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθcont : Continuous θ₀) (hθper : IsPeriodic θ₀) :
    ∃ θ : ℝ → Pt 2 → ℝ,
      Continuous (Function.uncurry θ) ∧
      (∃ C, ∀ t x, |θ t x| ≤ C) ∧
      (∀ t, IsPeriodic (θ t)) ∧ θ 0 = θ₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
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
  obtain ⟨u, hu, _⟩ := exists_unique_global_scalar_mild hν hT b f
  have hbper : ∀ i t, IsPeriodic (fun x => b i (t, x)) :=
    slabDriftComponent_periodic v hvc C hC hvper
  have hbReal : ∀ i, star (b i) = b i := slabDriftComponent_real v hvc C hC
  have hfReal : star f = f := by
    apply BoundedContinuousFunction.ext
    intro x
    change star (θ₀ x : ℂ) = (θ₀ x : ℂ)
    simp
  have hureal := global_scalar_mild_fixedPoint_real hν hT b f hbReal hfReal hu
  have huper := global_scalar_mild_fixedPoint_periodic hν hT b f hbper
    (show IsPeriodic f from hfper) hu
  have huim : ∀ p, (u p).im = 0 := by
    intro p
    have hh := congrArg (fun w : SlabScalar T => (w p).im) hureal
    simp only [BoundedContinuousFunction.star_apply, Complex.star_def, Complex.conj_im] at hh
    linarith
  let θ : ℝ → Pt 2 → ℝ := fun s x => (extendSlabScalar hT u s x).re
  have hθcomplex : ∀ s x, (θ s x : ℂ) = extendSlabScalar hT u s x := by
    intro s x
    apply Complex.ext
    · rfl
    · simpa [θ, extendSlabScalar] using (huim (projIcc 0 T hT s, x)).symm
  have he : ∀ p : ScalarTimeSlab T, u p =
      heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f p.2 -
        ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hT (b i * u)) i p.1 p.2 := by
    intro p
    have hh := congrArg (fun w : SlabScalar T => w p) hu
    simpa [scalarMildMap] using hh.symm
  refine ⟨θ, Complex.continuous_re.comp (continuous_extendSlabScalar hT u),
    ⟨‖u‖, fun t x => (Complex.abs_re_le_norm _).trans (norm_extendSlabScalar_le hT u t x)⟩,
    ?_, ?_, ?_⟩
  · intro t x m
    exact congrArg Complex.re (huper (projIcc 0 T hT t) x m)
  · funext x
    have hh := he (⟨0, ⟨le_rfl, hT⟩⟩, x)
    simp only [mul_zero, Real.toNNReal_zero, duhamelComponent_zero, Finset.sum_const_zero,
      sub_zero, heatOp_zero f.continuous] at hh
    have hext := extendSlabScalar_of_mem hT u (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) x
    change (extendSlabScalar hT u 0 x).re = θ₀ x
    rw [hext, hh]
    rfl
  · intro t ht x
    rw [hθcomplex, extendSlabScalar_of_mem hT u ht, he (⟨t, ht⟩, x)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold duhamelComponent
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) T := by
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    dsimp only
    congr 1
    funext y
    rw [extendSlabScalar_of_mem hT (b i * u) hs', hθcomplex,
      extendSlabScalar_of_mem hT u hs']
    rfl

end AnomDiss
