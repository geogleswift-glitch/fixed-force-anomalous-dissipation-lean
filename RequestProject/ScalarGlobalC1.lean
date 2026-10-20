module

public import RequestProject.ScalarMildC1
public import RequestProject.ScalarGlobalExistence

/-! # First spatial regularity for the actual original scalar drift data -/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

lemma slabDriftComponent_spatial_holder {T β : ℝ}
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C) (i : Fin 2) :
    ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖slabDriftComponent v hc C hC i (t, x) - slabDriftComponent v hc C hC i (t, y)‖ ≤
        H * ‖x - y‖ ^ β := by
  obtain ⟨D₀, hD₀⟩ := hv.bdd_d1 0
  obtain ⟨D₁, hD₁⟩ := hv.bdd_d1 1
  let L := max (D₀ + D₁) 0
  have hL : 0 ≤ L := le_max_right _ _
  refine ⟨(2 * C) ^ (1 - β) * L ^ β, fun t x y => ?_⟩
  let A : Pt 2 →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
  have hfc : ContDiff ℝ 1 (fun z => (v t z i : ℂ)) :=
    A.contDiff.comp (hv.smooth_x t t.property)
  have hpderiv : ∀ j z, pd j (fun y => (v t y i : ℂ)) z = (pd j (v t) z i : ℂ) := by
    intro j z
    change pd j (fun y => A (v t y)) z = A (pd j (v t) z)
    rw [pd_clm_fun A (v t) j ((hv.smooth_x t t.property).differentiable one_ne_zero)]
  have hfd : ∀ z, ‖fderiv ℝ (fun y => (v t y i : ℂ)) z‖ ≤ L := by
    intro z
    have h := norm_clm_pt2_le (fderiv ℝ (fun y => (v t y i : ℂ)) z)
    change ‖fderiv ℝ (fun y => (v t y i : ℂ)) z‖ ≤
      ‖pd 0 (fun y => (v t y i : ℂ)) z‖ + ‖pd 1 (fun y => (v t y i : ℂ)) z‖ at h
    rw [hpderiv, hpderiv, Complex.norm_real, Complex.norm_real] at h
    exact (h.trans (add_le_add
      ((norm_le_pi_norm (pd 0 (v t) z) i).trans (hD₀ t t.property z))
      ((norm_le_pi_norm (pd 1 (v t) z) i).trans (hD₁ t t.property z)))).trans (le_max_left _ _)
  exact bounded_C1_holder hfc hL (fun z => by
    simpa only [Complex.norm_real] using (norm_le_pi_norm (v t z) i).trans (hC t t.property z))
    hfd hβ₀ hβ₁ x y

/-- Every bounded continuous real mild solution for the original regular drift
has true first spatial derivatives; the proof identifies its slab fixed point. -/
theorem real_scalar_mild_contDiff_one {T ν β : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 1 θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 1 (θ t) := by
  have hvc := hv.continuousOn hβ₀
  obtain ⟨C, hC⟩ := hv.bdd
  let b : Fin 2 → SlabScalar T := slabDriftComponent v hvc C hC
  have hfcont : Continuous (fun x => (θ₀ x : ℂ)) := Complex.continuous_ofReal.comp hθc.continuous
  have hfper : IsPeriodic (fun x => (θ₀ x : ℂ)) := fun x m => by dsimp only; rw [hθper x m]
  obtain ⟨C₀, hC₀⟩ := (isQP_zero_iff.2 hfper).bdd hfcont
  let f : Pt 2 →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (θ₀ x : ℂ)) hfcont C₀ hC₀
  let u : SlabScalar T := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => (θ p.1 p.2 : ℂ))
    (Complex.continuous_ofReal.comp (hθjoint.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)))
    Cθ (fun p => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hθbound p.1 p.2)
  have he : ∀ (t : Icc (0 : ℝ) T) x i,
      duhamelComponent ν (extendSlabScalar hT (b i * u)) i t x =
        duhamelComponent ν (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x := by
    intro t x i
    unfold duhamelComponent
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) T := by
      rw [uIcc_of_le t.property.1] at hs
      exact ⟨hs.1, hs.2.trans t.property.2⟩
    dsimp only
    congr 1
    funext y
    rw [extendSlabScalar_of_mem hT (b i * u) hs']
    rfl
  have hu : scalarMildMap hν hT b f u = u := by
    apply BoundedContinuousFunction.ext
    intro p
    simp only [scalarMildMap, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.sum_apply, slabHeatInitial_apply, slabDuhamel_apply]
    simp_rw [he]
    exact (hmild p.1 p.1.property p.2).symm
  have hbper : ∀ i t, IsPeriodic (fun x => b i (t, x)) :=
    slabDriftComponent_periodic v hvc C hC hvper
  have hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β :=
    slabDriftComponent_spatial_holder hβ₀.le hβ₁.le v hv hvc C hC
  have hfc : ContDiff ℝ 1 (f : Pt 2 → ℂ) := Complex.ofRealCLM.contDiff.comp hθc
  have hc₁ := scalar_mild_fixedPoint_contDiff_one hν hT hβ₀ hβ₁ b f hbper
    (show IsPeriodic f from hfper) hfc hbholder hu
  intro t ht
  exact Complex.reCLM.contDiff.comp (hc₁ ⟨t, ht⟩)

/-- The original real periodic data now have a constructed mild solution with
actual `C¹` spatial slices throughout the entire finite interval. -/
theorem exists_real_periodic_global_scalar_mild_C1 {T ν β : ℝ}
    (hT : 0 ≤ T) (hν : 0 < ν) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 1 θ₀) (hθper : IsPeriodic θ₀) :
    ∃ θ : ℝ → Pt 2 → ℝ,
      Continuous (Function.uncurry θ) ∧ (∃ C, ∀ t x, |θ t x| ≤ C) ∧
      (∀ t, IsPeriodic (θ t)) ∧ θ 0 = θ₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 1 (θ t)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
          ∑ i : Fin 2, duhamelComponent ν
            (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x := by
  obtain ⟨θ, hc, ⟨C, hC⟩, hp, hinit, hm⟩ :=
    exists_real_periodic_global_scalar_mild hT hν hβ₀ v hv hvper θ₀ hθc.continuous hθper
  exact ⟨θ, hc, ⟨C, hC⟩, hp, hinit,
    real_scalar_mild_contDiff_one hT hν hβ₀ hβ₁ v hv hvper θ₀ hθc hθper θ hc hC hm, hm⟩

end AnomDiss
