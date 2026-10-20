module

public import RequestProject.ScalarGlobalC2Bridge
public import RequestProject.ScalarGlobalC1
public import RequestProject.ScalarMildGradientHolderLoss
public import RequestProject.ScalarMildGradientSchauder
public import RequestProject.ScalarHolderOperations

/-! # Spatial derivatives of the actual scalar flux

The existing first-derivative estimates imply the hypotheses of the spatial
`C²` Duhamel bridge for the original parabolic drift. No existence or
regularity hypothesis on the scalar is added: it is the constructed fixed point.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

theorem scalar_mild_fixedPoint_flux_derivative_regular
    {ν T β α : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (hα₀ : 0 ≤ α) (hαβ : α ≤ β)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u) :
    ∀ i : Fin 2,
      let G := extendSlabScalar hT (slabDriftComponent v hc C hC i * u)
      Continuous (Function.uncurry (fun s x => pd i (G s) x)) ∧
      (∀ s, ContDiff ℝ 1 (G s)) ∧ (∀ s, IsPeriodic (G s)) ∧
      (∃ D, ∀ s x, ‖pd i (G s) x‖ ≤ D) ∧
      (∃ H, 0 ≤ H ∧ ∀ s x y,
        ‖pd i (G s) x - pd i (G s) y‖ ≤ H * ‖x - y‖ ^ α) := by
  let b := slabDriftComponent v hc C hC
  have hbper : ∀ i t, IsPeriodic (fun x => b i (t, x)) :=
    slabDriftComponent_periodic v hc C hC hvper
  have hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β :=
    slabDriftComponent_spatial_holder hβ₀.le hβ₁.le v hv hc C hC
  have hf₁ : ContDiff ℝ 1 (f : Pt 2 → ℂ) := hfc.of_le (by norm_num)
  have huC1 := scalar_mild_fixedPoint_contDiff_one hν hT hβ₀ hβ₁ b f hbper hfper hf₁ hbholder hu
  have huper := global_scalar_mild_fixedPoint_periodic hν hT b f hbper hfper hu
  have huc := scalar_mild_fixedPoint_fderiv_continuous hν hT hβ₀ hβ₁ b f hbper hfper hf₁ hbholder hu
  obtain ⟨Du, hDu⟩ := scalar_mild_fixedPoint_fderiv_bdd hν hT hβ₀ hβ₁ b f hbper hfper hf₁ hbholder hu
  obtain ⟨Hu, hHu₀, hHu⟩ : ∃ H, 0 ≤ H ∧ ∀ (t : Icc (0 : ℝ) T) x y,
      ‖fderiv ℝ (fun z => u (t, z)) x - fderiv ℝ (fun z => u (t, z)) y‖ ≤
        H * ‖x - y‖ ^ α := by
    rcases hαβ.eq_or_lt with he | hl
    · subst α
      exact scalar_mild_fixedPoint_fderiv_spatial_holder
        hν hT hβ₀ hβ₁ b f hbper hfper hfc hbholder hu
    · exact scalar_mild_fixedPoint_fderiv_spatial_holder_loss
        hν hT hβ₀ hβ₁ hα₀ hl b f hbper hfper hfc hbholder hu
  have hDu₀ : 0 ≤ Du := (norm_nonneg _).trans (hDu ⟨0, ⟨le_rfl, hT⟩⟩ 0)
  have hα₁ : α ≤ 1 := hαβ.trans hβ₁.le
  have huHolder : ∀ (t : Icc (0 : ℝ) T) x y,
      ‖u (t, x) - u (t, y)‖ ≤ ((2 * ‖u‖) ^ (1 - α) * Du ^ α) * ‖x - y‖ ^ α := by
    intro t x y
    exact bounded_C1_holder (huC1 t) hDu₀ (fun z => u.norm_coe_le_norm (t, z))
      (hDu t) hα₀ hα₁ x y
  intro i
  let A : Pt 2 →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
  have hbC1 : ∀ t : Icc (0 : ℝ) T, ContDiff ℝ 1 (fun x => b i (t, x)) := by
    intro t
    exact A.contDiff.comp (hv.smooth_x t t.property)
  have hpd : ∀ (t : Icc (0 : ℝ) T) x,
      pd i (fun y => b i (t, y)) x = (pd i (v t) x i : ℂ) := by
    intro t x
    change pd i (fun y => A (v t y)) x = A (pd i (v t) x)
    rw [pd_clm_fun A (v t) i ((hv.smooth_x t t.property).differentiable one_ne_zero)]
  obtain ⟨Db, hDb⟩ := hv.bdd_d1 i
  have hDb₀ : 0 ≤ Db := (norm_nonneg _).trans (hDb 0 ⟨le_rfl, hT⟩ 0)
  have hbpdB : ∀ (t : Icc (0 : ℝ) T) x, ‖pd i (fun y => b i (t, y)) x‖ ≤ Db := by
    intro t x
    rw [hpd, Complex.norm_real]
    exact (norm_le_pi_norm (pd i (v t) x) i).trans (hDb t t.property x)
  have hbpdC : Continuous (fun p : ScalarTimeSlab T => pd i (fun y => b i (p.1, y)) p.2) := by
    simp_rw [hpd]
    change Continuous (fun p : ScalarTimeSlab T => A (pd i (v p.1) p.2))
    apply A.continuous.comp
    exact ((hv.holder_d1 i).continuousOn hβ₀).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.property, mem_univ _⟩)
  obtain ⟨Hb, hHb⟩ := hv.holder_d1 i
  have hbpdH : ∀ (t : Icc (0 : ℝ) T) x y,
      ‖pd i (fun z => b i (t, z)) x - pd i (fun z => b i (t, z)) y‖ ≤
        max Hb 0 * ‖x - y‖ ^ β := by
    intro t x y
    rw [hpd, hpd, ← Complex.ofReal_sub, Complex.norm_real]
    have hh := (norm_le_pi_norm (pd i (v t) x - pd i (v t) y) i).trans
      (hHb t t.property t t.property x y)
    simp only [sub_self, abs_zero, Real.zero_rpow (by positivity : β / 2 ≠ (0 : ℝ)), add_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left Hb 0) (Real.rpow_nonneg (norm_nonneg _) _))
  let Hdb := (2 * Db) ^ (1 - α / β) * (max Hb 0) ^ (α / β)
  have hbpdHa : ∀ (t : Icc (0 : ℝ) T) x y,
      ‖pd i (fun z => b i (t, z)) x - pd i (fun z => b i (t, z)) y‖ ≤ Hdb * ‖x - y‖ ^ α := by
    intro t x y
    exact bounded_holder_lower (le_max_right _ _) (hbpdB t) (hbpdH t) hβ₀ hα₀ hαβ x y
  obtain ⟨Hbc, hHbc⟩ := hbholder i
  let Hb0 := (2 * ‖b i‖) ^ (1 - α / β) * (max Hbc 0) ^ (α / β)
  have hbHa : ∀ (t : Icc (0 : ℝ) T) x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ Hb0 * ‖x - y‖ ^ α := by
    intro t x y
    apply bounded_holder_lower (le_max_right Hbc 0) (fun z => (b i).norm_coe_le_norm (t, z))
      (fun z w => (hHbc t z w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (norm_nonneg _) _))) hβ₀ hα₀ hαβ x y
  let U := (2 * ‖u‖) ^ (1 - α) * Du ^ α
  let H := Db * U + ‖u‖ * Hdb + ‖b i‖ * Hu + Du * Hb0
  have hH₀ : 0 ≤ H := by dsimp [H, U, Hdb, Hb0]; positivity
  have hproduct : ∀ (t : Icc (0 : ℝ) T) x,
      pd i (fun y => b i (t, y) * u (t, y)) x =
        pd i (fun y => b i (t, y)) x * u (t, x) + b i (t, x) * pd i (fun y => u (t, y)) x := by
    intro t x
    unfold pd
    rw [fderiv_fun_mul ((hbC1 t).differentiable one_ne_zero x) ((huC1 t).differentiable one_ne_zero x)]
    simp
    ring
  have hupdC : Continuous (fun p : ScalarTimeSlab T => pd i (fun y => u (p.1, y)) p.2) := by
    simpa only [pd] using huc.clm_apply
      (continuous_const : Continuous (fun _ : ScalarTimeSlab T => (Pi.single i (1 : ℝ) : Pt 2)))
  have hprodC : Continuous (fun p : ScalarTimeSlab T => pd i (fun y => b i (p.1, y) * u (p.1, y)) p.2) := by
    simp_rw [hproduct]
    exact (hbpdC.mul u.continuous).add ((b i).continuous.mul hupdC)
  refine ⟨?_, ?_, ?_, ⟨Db * ‖u‖ + ‖b i‖ * Du, ?_⟩, ⟨H, hH₀, ?_⟩⟩
  · exact hprodC.comp (((continuous_projIcc.comp continuous_fst).prodMk continuous_snd) :
      Continuous (fun p : ℝ × Pt 2 => (projIcc 0 T hT p.1, p.2)))
  · intro s
    exact (hbC1 (projIcc 0 T hT s)).mul (huC1 (projIcc 0 T hT s))
  · intro s x m
    change b i (projIcc 0 T hT s, x + intVec m) * u (projIcc 0 T hT s, x + intVec m) =
      b i (projIcc 0 T hT s, x) * u (projIcc 0 T hT s, x)
    exact congrArg₂ (· * ·) (hbper i (projIcc 0 T hT s) x m) (huper (projIcc 0 T hT s) x m)
  · intro s x
    change ‖pd i (fun y => b i (projIcc 0 T hT s, y) * u (projIcc 0 T hT s, y)) x‖ ≤ _
    rw [hproduct]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    exact add_le_add
      (mul_le_mul (hbpdB _ x) (u.norm_coe_le_norm _) (norm_nonneg _) hDb₀)
      (mul_le_mul ((b i).norm_coe_le_norm _) (pd_bound_of_fderiv (hDu _) i x)
        (norm_nonneg _) (norm_nonneg _))
  · intro s x y
    let t := projIcc 0 T hT s
    change ‖pd i (fun z => b i (t, z) * u (t, z)) x - pd i (fun z => b i (t, z) * u (t, z)) y‖ ≤ _
    rw [hproduct, hproduct]
    have h₁ := bounded_holder_product (hbpdB t) (fun z => u.norm_coe_le_norm (t, z))
      (hbpdHa t) (huHolder t) x y
    have h₂ := bounded_holder_product (fun z => (b i).norm_coe_le_norm (t, z))
      (fun z => pd_bound_of_fderiv (hDu t) i z) (hbHa t)
      (fun x y => partial_holder_of_fderiv_holder (hHu t) i x y) x y
    calc
      ‖(pd i (fun z => b i (t, z)) x * u (t, x) + b i (t, x) * pd i (fun z => u (t, z)) x) -
          (pd i (fun z => b i (t, z)) y * u (t, y) + b i (t, y) * pd i (fun z => u (t, z)) y)‖
          ≤ ‖pd i (fun z => b i (t, z)) x * u (t, x) - pd i (fun z => b i (t, z)) y * u (t, y)‖ +
            ‖b i (t, x) * pd i (fun z => u (t, z)) x - b i (t, y) * pd i (fun z => u (t, z)) y‖ := by
        have he : ∀ a b c d : ℂ, a + b - (c + d) = (a - c) + (b - d) := by intros; ring
        rw [he]
        exact norm_add_le _ _
      _ ≤ (Db * U + ‖u‖ * Hdb) * ‖x - y‖ ^ α + (‖b i‖ * Hu + Du * Hb0) * ‖x - y‖ ^ α := add_le_add h₁ h₂
      _ = _ := by dsimp [H]; ring

/-- The constructed scalar fixed point for the original parabolic drift has
actual `C²` spatial slices, including at the initial time. -/
theorem scalar_mild_fixedPoint_contDiff_two_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u) :
    ∀ t : Icc (0 : ℝ) T, ContDiff ℝ 2 (fun x => u (t, x)) := by
  apply scalar_mild_fixedPoint_contDiff_two_of_flux_derivative_holder hν hT
    (show 0 < β / 2 by linarith) (slabDriftComponent v hc C hC) f hu hfc hfper
  exact scalar_mild_fixedPoint_flux_derivative_regular hν hT hβ₀ hβ₁
    (show 0 ≤ β / 2 by linarith) (show β / 2 ≤ β by linarith)
    v hv hvper hc C hC f hfper hfc hu

/-- Every bounded continuous real solution of the genuine mild equation for
the original drift has true second spatial derivatives. -/
theorem real_scalar_mild_contDiff_two {T ν β : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (θ t) := by
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
  have hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ) := Complex.ofRealCLM.contDiff.comp hθc
  have hc₂ := scalar_mild_fixedPoint_contDiff_two_regular_drift hν hT hβ₀ hβ₁
    v hv hvper hvc C hC f (show IsPeriodic f from hfper) hfc hu
  intro t ht
  exact Complex.reCLM.contDiff.comp (hc₂ ⟨t, ht⟩)

/-- Original periodic `C²` data admit a globally defined bounded continuous
real mild solution with actual `C²` spatial slices on the full finite slab. -/
theorem exists_real_periodic_global_scalar_mild_C2 {T ν β : ℝ}
    (hT : 0 ≤ T) (hν : 0 < ν) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀) :
    ∃ θ : ℝ → Pt 2 → ℝ,
      Continuous (Function.uncurry θ) ∧ (∃ C, ∀ t x, |θ t x| ≤ C) ∧
      (∀ t, IsPeriodic (θ t)) ∧ θ 0 = θ₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (θ t)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
          ∑ i : Fin 2, duhamelComponent ν
            (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x := by
  obtain ⟨θ, hc, ⟨C, hC⟩, hp, hinit, hm⟩ :=
    exists_real_periodic_global_scalar_mild hT hν hβ₀ v hv hvper θ₀ hθc.continuous hθper
  exact ⟨θ, hc, ⟨C, hC⟩, hp, hinit,
    real_scalar_mild_contDiff_two hT hν hβ₀ hβ₁ v hv hvper θ₀ hθc hθper θ hc hC hm, hm⟩

end AnomDiss
