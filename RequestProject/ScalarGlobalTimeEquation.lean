module

public import RequestProject.ScalarFluxDerivativeRegularity
public import RequestProject.ScalarMildTimeEquation

/-!
# The actual scalar advection–diffusion equation on the whole closed slab

The spatial flux regularity is proved for the original parabolic drift and
then used to differentiate the constructed mild equation. No PDE assumption
or classical existence interface is used in this file.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- Time differentiability of the genuine fixed point for the original drift,
including one-sided derivatives at both endpoints. -/
theorem scalar_mild_fixedPoint_hasDerivWithinAt_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Pt 2) :
    HasDerivWithinAt (fun s => extendSlabScalar hT u s x)
      (ν • lap (extendSlabScalar hT u t) x -
        ∑ i : Fin 2, pd i (extendSlabScalar hT
          (slabDriftComponent v hc C hC i * u) t) x) (Icc 0 T) t := by
  apply scalar_mild_fixedPoint_hasDerivWithinAt_of_flux_derivative_holder hν hT
    (show 0 < β / 2 by linarith) (slabDriftComponent v hc C hC) f hu hfc hfper
  exact scalar_mild_fixedPoint_flux_derivative_regular hν hT hβ₀ hβ₁
    (show 0 ≤ β / 2 by linarith) (show β / 2 ≤ β by linarith)
    v hv hvper hc C hC f hfper hfc hu
  exact ht

/-- The Laplacian commutes with real-to-complex inclusion on actual `C²` maps. -/
lemma lap_complex_ofReal_C2 (f : Pt 2 → ℝ) (hf : ContDiff ℝ 2 f) (x : Pt 2) :
    lap (fun y => (f y : ℂ)) x = ((lap (E := ℝ) f x : ℝ) : ℂ) := by
  have hp : ∀ i, pd i (fun y => (f y : ℂ)) = fun y => ((pd (E := ℝ) i f y : ℝ) : ℂ) :=
    fun i => pd_clm_fun Complex.ofRealCLM f i (hf.differentiable (by norm_num))
  unfold lap
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp i]
  exact congrFun (pd_clm_fun Complex.ofRealCLM (pd (E := ℝ) i f) i
    (differentiable_pd hf i)) x
/-- Scalar transport agrees with divergence of the actual product flux for a
spatially differentiable divergence-free drift. -/
lemma conv_eq_scalar_flux_divergence (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, divergence v x = 0) (θ : Pt 2 → ℝ) (hθ : ContDiff ℝ 1 θ)
    (x : Pt 2) :
    conv v θ x = ∑ i : Fin 2, pd i (fun y => v y i * θ y) x := by
  have hprod (i : Fin 2) : pd i (fun y => v y i * θ y) x =
      pd i v x i * θ x + v x i * pd i θ x := by
    rw [pd_mul' _ _ x ((contDiff_pi.1 hv i).differentiable one_ne_zero x)
      (hθ.differentiable one_ne_zero x)]
    rw [pd_component v x (hv.differentiable one_ne_zero x)]
  have hd : (∑ i : Fin 2, pd i v x i) = 0 := hdiv x
  simp only [hprod, Finset.sum_add_distrib, ← Finset.sum_mul, hd,
    zero_mul, zero_add, conv, smul_eq_mul]

/-- Every bounded continuous real solution of the genuine mild equation has
actual time derivatives and solves its divergence-form parabolic equation. -/
theorem real_scalar_mild_hasDerivWithinAt {T ν β : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Pt 2) :
    HasDerivWithinAt (fun s => θ s x)
      (ν * lap (θ t) x - ∑ i : Fin 2, pd i (fun y => v t y i * θ t y) x)
      (Icc 0 T) t := by
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
  have he : ∀ (s : Icc (0 : ℝ) T) y i,
      duhamelComponent ν (extendSlabScalar hT (b i * u)) i s y =
        duhamelComponent ν (fun r z => (v r z i : ℂ) * (θ r z : ℂ)) i s y := by
    intro s y i
    unfold duhamelComponent
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) T := by
      rw [uIcc_of_le s.property.1] at hr
      exact ⟨hr.1, hr.2.trans s.property.2⟩
    dsimp only
    congr 1
    funext z
    rw [extendSlabScalar_of_mem hT (b i * u) hr']
    rfl
  have hu : scalarMildMap hν hT b f u = u := by
    apply BoundedContinuousFunction.ext
    intro p
    simp only [scalarMildMap, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.sum_apply, slabHeatInitial_apply, slabDuhamel_apply]
    simp_rw [he]
    exact (hmild p.1 p.1.property p.2).symm
  have hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ) := Complex.ofRealCLM.contDiff.comp hθc
  have hθ₂ := real_scalar_mild_contDiff_two hT hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc hθper θ hθjoint hθbound hmild t ht
  have hslice : ∀ s ∈ Icc (0 : ℝ) T,
      extendSlabScalar hT u s = fun y => (θ s y : ℂ) := by
    intro s hs
    funext y
    rw [extendSlabScalar_of_mem hT u hs]
    rfl
  have hflux : ∀ i, extendSlabScalar hT (b i * u) t =
      fun y => ((v t y i * θ t y : ℝ) : ℂ) := by
    intro i
    funext y
    rw [extendSlabScalar_of_mem hT (b i * u) ht]
    change (v t y i : ℂ) * (θ t y : ℂ) = _
    rw [Complex.ofReal_mul]
  have hpd : ∀ i, pd i (extendSlabScalar hT (b i * u) t) x =
      ((pd (E := ℝ) i (fun y => v t y i * θ t y) x : ℝ) : ℂ) := by
    intro i
    rw [hflux]
    exact congrFun (pd_clm_fun Complex.ofRealCLM _ i
      (((contDiff_pi.1 (hv.smooth_x t ht) i).mul
        (hθ₂.of_le (by norm_num))).differentiable one_ne_zero)) x
  have hd := scalar_mild_fixedPoint_hasDerivWithinAt_regular_drift hν hT hβ₀ hβ₁
    v hv hvper hvc C hC f (show IsPeriodic f from hfper) hfc hu ht x
  rw [hslice t ht, lap_complex_ofReal_C2 _ hθ₂] at hd
  dsimp only [b] at hpd
  simp only [hpd, ← Complex.ofReal_sum, Complex.real_smul, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub] at hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  simpa only [Complex.reCLM_apply, Complex.ofReal_re, Function.comp_apply] using
    hr.congr_of_mem (f₁ := fun s => θ s x) (fun s hs => by
      change θ s x = (extendSlabScalar hT u s x).re
      rw [hslice s hs]
      rfl) ht

/-- The genuine real mild solution satisfies the advection–diffusion equation
for the original divergence-free drift at every time of the closed slab. -/
theorem real_scalar_mild_equation {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hvdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      dt T θ t x + conv (v t) (θ t) x = ν • lap (θ t) x := by
  intro t ht x
  have hd := real_scalar_mild_hasDerivWithinAt hT.le hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc hθper θ hθjoint hθbound hmild ht x
  have hθ₂ := real_scalar_mild_contDiff_two hT.le hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc hθper θ hθjoint hθbound hmild t ht
  rw [dt, hd.derivWithin (uniqueDiffOn_Icc hT t ht),
    conv_eq_scalar_flux_divergence _ (hv.smooth_x t ht) (hvdiv t ht) _
      (hθ₂.of_le (by norm_num)), smul_eq_mul]
  ring

/-- Original periodic `C²` data admit a bounded continuous solution of the
actual advection–diffusion equation, with spatial `C²` slices and time
within-derivatives on the full closed interval. -/
theorem exists_real_periodic_global_scalar_C2_equation {T ν β : ℝ}
    (hT : 0 < T) (hν : 0 < ν) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hvdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀) :
    ∃ θ : ℝ → Pt 2 → ℝ,
      Continuous (Function.uncurry θ) ∧ (∃ C, ∀ t x, |θ t x| ≤ C) ∧
      (∀ t, IsPeriodic (θ t)) ∧ θ 0 = θ₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (θ t)) ∧
      (∀ x, ∀ t ∈ Icc (0 : ℝ) T, DifferentiableWithinAt ℝ
        (fun s => θ s x) (Icc 0 T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        dt T θ t x + conv (v t) (θ t) x = ν • lap (θ t) x) := by
  obtain ⟨θ, hc, ⟨C, hC⟩, hp, hinit, hC2, hm⟩ :=
    exists_real_periodic_global_scalar_mild_C2 hT.le hν hβ₀ hβ₁ v hv hvper θ₀ hθc hθper
  refine ⟨θ, hc, ⟨C, hC⟩, hp, hinit, hC2, ?_, ?_⟩
  · intro x t ht
    exact (real_scalar_mild_hasDerivWithinAt hT.le hν hβ₀ hβ₁ v hv hvper
      θ₀ hθc hθper θ hc hC hm ht x).differentiableWithinAt
  · exact real_scalar_mild_equation hT hν hβ₀ hβ₁ v hv hvper hvdiv
      θ₀ hθc hθper θ hc hC hm


/-- The actual second derivatives of the homogeneous heat term are jointly
continuous through zero variance. -/
lemma continuous_pd2_heat_initial_C2 (ν : ℝ) {f : Pt 2 → ℂ}
    (hf : ContDiff ℝ 2 f) (hp : IsPeriodic f) (i j : Fin 2) :
    Continuous (fun p : ℝ × Pt 2 =>
      pd i (pd j (heatOp (Real.toNNReal (2 * ν * p.1)) f)) p.2) := by
  have hqp : IsQP 0 f := isQP_zero_iff.2 hp
  have hc := continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf j) i
  obtain ⟨C, hC⟩ := (isQP_pd2 hqp hf i j).bdd hc
  simp_rw [pd2_heatOp hqp hf]
  exact (continuous_heatOp_variance_space hc hC).comp
    (by fun_prop : Continuous (fun p : ℝ × Pt 2 =>
      (Real.toNNReal (2 * ν * p.1), p.2)))

lemma pd2_sub_C2 (f g : Pt 2 → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (i j : Fin 2) (x : Pt 2) :
    pd i (pd j (fun y => f y - g y)) x =
      pd i (pd j f) x - pd i (pd j g) x := by
  rw [pd_sub_fun f g (hf.differentiable (by norm_num))
    (hg.differentiable (by norm_num)) j]
  rw [pd_sub_fun _ _ (differentiable_pd hf j) (differentiable_pd hg j) i]

/-- Joint continuity of the actual spatial Hessian on the entire finite slab.
The source regularity is derived from the original drift data. -/
theorem scalar_mild_fixedPoint_pd2_continuous_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u) (i j : Fin 2) :
    Continuous (fun p : ScalarTimeSlab T => pd i (pd j (fun y => u (p.1, y))) p.2) := by
  let b := slabDriftComponent v hc C hC
  let A : ℝ → Pt 2 → ℂ := fun s => heatOp (Real.toNNReal (2 * ν * s)) f
  let D : Fin 2 → ℝ → Pt 2 → ℂ := fun k =>
    duhamelComponent ν (extendSlabScalar hT (b k * u)) k
  have hflux := scalar_mild_fixedPoint_flux_derivative_regular hν hT hβ₀ hβ₁
    (show 0 ≤ β / 2 by linarith) (show β / 2 ≤ β by linarith)
    v hv hvper hc C hC f hfper hfc hu
  have hDs : ∀ k (t : Icc (0 : ℝ) T), ContDiff ℝ 2 (D k t) := by
    intro k t
    obtain ⟨hGc, hGs, hGp, ⟨B, hB⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    exact contDiff_two_duhamelComponent_of_flux_derivative_holder hν k hGc hGs hGp
      hB hH (show 0 < β / 2 by linarith) hholder t.property.1
  have hAs : ∀ t, ContDiff ℝ 2 (A t) := fun t =>
    contDiff_heatOp (isQP_zero_iff.2 hfper) hfc _
  have hDcont : ∀ k, Continuous (fun p : ScalarTimeSlab T =>
      pd i (pd j (D k p.1)) p.2) := by
    intro k
    obtain ⟨hGc, hGs, hGp, ⟨B, hB⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    have hsource : ∀ s, IsPeriodic (pd k (extendSlabScalar hT (b k * u) s)) :=
      fun s => isPeriodic_pd _ (hGp s) k
    have hcc := (continuousOn_pd2_heatDuhamel_holder hν hGc hsource hB hH
      (show 0 < β / 2 by linarith) hholder i j hT).comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p : ScalarTimeSlab T => p.1.property)
    apply hcc.congr
    intro p
    have he : D k p.1 = heatDuhamel ν
        (fun s => pd k (extendSlabScalar hT (b k * u) s)) p.1 := by
      funext y
      exact duhamelComponent_eq_heatDuhamel_pd hν hGs hGp p.1.property.1 k y
    simpa only [Function.comp_apply] using
      congrArg (fun F => pd i (pd j F) p.2) he.symm
  have hAc : Continuous (fun p : ScalarTimeSlab T => pd i (pd j (A p.1)) p.2) :=
    (continuous_pd2_heat_initial_C2 ν hfc hfper i j).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  apply ((hAc.fun_sub (hDcont 0)).fun_sub (hDcont 1)).congr
  intro p
  have he : (fun y => u (p.1, y)) = fun y =>
      A p.1 y - D 0 p.1 y - D 1 p.1 y := by
    funext y
    have hh := congrArg (fun w : SlabScalar T => w (p.1, y)) hu
    simpa [scalarMildMap, A, D, b, Fin.sum_univ_two, sub_add_eq_sub_sub] using hh.symm
  rw [he, pd2_sub_C2 _ _ ((hAs p.1).sub (hDs 0 p.1)) (hDs 1 p.1),
    pd2_sub_C2 _ _ (hAs p.1) (hDs 0 p.1)]

/-- Joint continuity and spatial periodicity give an actual uniform bound on
the full time slab and all of the covering space. -/
lemma bounded_periodic_slab {E : Type*} [NormedAddCommGroup E] {T : ℝ}
    (g : ℝ → Pt 2 → E)
    (hc : Continuous (fun p : ScalarTimeSlab T => g p.1 p.2))
    (hp : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (g t)) : BddOn T g := by
  have hcompact : IsCompact ((univ : Set (Icc (0 : ℝ) T)) ×ˢ (cell 2)) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun t ht y => ?_⟩
  let n : Fin 2 → ℤ := fun k => ⌊y k⌋
  have hz : y - intVec n ∈ cell 2 := by
    constructor <;> intro k <;> simp only [Pi.sub_apply, intVec, Pi.zero_apply, Pi.one_apply, n]
    · exact sub_nonneg.2 (Int.floor_le _)
    · linarith [Int.lt_floor_add_one (y k)]
  have he := hp t ht (y - intVec n) n
  rw [sub_add_cancel] at he
  rw [he]
  exact hC (⟨t, ht⟩, y - intVec n) ⟨mem_univ _, hz⟩

/-- Every actual second spatial partial of the constructed fixed point is
uniformly bounded on the full finite slab. -/
theorem scalar_mild_fixedPoint_pd2_bdd_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u) (i j : Fin 2) :
    BddOn T (fun t => pd i (pd j (extendSlabScalar hT u t))) := by
  let b := slabDriftComponent v hc C hC
  have hbper := slabDriftComponent_periodic v hc C hC hvper
  have huper := global_scalar_mild_fixedPoint_periodic hν hT b f hbper hfper hu
  have hc₂ := scalar_mild_fixedPoint_pd2_continuous_regular_drift hν hT hβ₀ hβ₁
    v hv hvper hc C hC f hfper hfc hu i j
  have he : ∀ (t : Icc (0 : ℝ) T), extendSlabScalar hT u t = fun y => u (t, y) := by
    intro t
    funext y
    rw [extendSlabScalar_of_mem hT u t.property]
  apply bounded_periodic_slab
  · simpa only [he] using hc₂
  · intro t ht
    rw [show extendSlabScalar hT u t = fun y => u (⟨t, ht⟩, y) by
      funext y; rw [extendSlabScalar_of_mem hT u ht]]
    exact isPeriodic_pd _ (isPeriodic_pd _ (huper ⟨t, ht⟩) j) i


/-- The time derivative of the actual fixed point is uniformly bounded. This
uses the proved PDE and the actual bounded spatial Hessian, rather than a
regularity assumption on the unknown. -/
theorem scalar_mild_fixedPoint_dt_bdd_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT.le (slabDriftComponent v hc C hC) f u = u) :
    BddOn T (dt T (extendSlabScalar hT.le u)) := by
  let b := slabDriftComponent v hc C hC
  obtain ⟨R₀, hR₀⟩ := scalar_mild_fixedPoint_pd2_bdd_regular_drift hν hT.le hβ₀ hβ₁
    v hv hvper hc C hC f hfper hfc hu 0 0
  obtain ⟨R₁, hR₁⟩ := scalar_mild_fixedPoint_pd2_bdd_regular_drift hν hT.le hβ₀ hβ₁
    v hv hvper hc C hC f hfper hfc hu 1 1
  have hflux := scalar_mild_fixedPoint_flux_derivative_regular hν hT.le hβ₀ hβ₁
    (show 0 ≤ β / 2 by linarith) (show β / 2 ≤ β by linarith)
    v hv hvper hc C hC f hfper hfc hu
  obtain ⟨_, _, _, ⟨D₀, hD₀⟩, _⟩ := hflux 0
  obtain ⟨_, _, _, ⟨D₁, hD₁⟩, _⟩ := hflux 1
  refine ⟨|ν| * (R₀ + R₁) + (D₀ + D₁), fun t ht x => ?_⟩
  have hd := scalar_mild_fixedPoint_hasDerivWithinAt_regular_drift hν hT.le hβ₀ hβ₁
    v hv hvper hc C hC f hfper hfc hu ht x
  rw [dt, hd.derivWithin (uniqueDiffOn_Icc hT t ht)]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [norm_smul, Real.norm_eq_abs, lap, Fin.sum_univ_two]
    exact mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (hR₀ t ht x) (hR₁ t ht x))) (abs_nonneg _)
  · rw [Fin.sum_univ_two]
    exact (norm_add_le _ _).trans (add_le_add (hD₀ t x) (hD₁ t x))


/-- All first and second spatial partials and the actual time derivative of
the real mild solution are uniformly bounded on the whole closed slab. -/
theorem real_scalar_mild_bdd_derivatives {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    (∀ i : Fin 2, BddOn T (fun t => pd i (θ t))) ∧
    (∀ i j : Fin 2, BddOn T (fun t => pd i (pd j (θ t)))) ∧ BddOn T (dt T θ) := by
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
  have he : ∀ (s : Icc (0 : ℝ) T) y i,
      duhamelComponent ν (extendSlabScalar hT.le (b i * u)) i s y =
        duhamelComponent ν (fun r z => (v r z i : ℂ) * (θ r z : ℂ)) i s y := by
    intro s y i
    unfold duhamelComponent
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) T := by
      rw [uIcc_of_le s.property.1] at hr
      exact ⟨hr.1, hr.2.trans s.property.2⟩
    dsimp only
    congr 1
    funext z
    rw [extendSlabScalar_of_mem hT.le (b i * u) hr']
    rfl
  have hu : scalarMildMap hν hT.le b f u = u := by
    apply BoundedContinuousFunction.ext
    intro p
    simp only [scalarMildMap, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.sum_apply, slabHeatInitial_apply, slabDuhamel_apply]
    simp_rw [he]
    exact (hmild p.1 p.1.property p.2).symm
  have hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ) := Complex.ofRealCLM.contDiff.comp hθc
  have hθ₂ := real_scalar_mild_contDiff_two hT.le hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc hθper θ hθjoint hθbound hmild
  have hslice : ∀ s ∈ Icc (0 : ℝ) T,
      extendSlabScalar hT.le u s = fun y => (θ s y : ℂ) := by
    intro s hs
    funext y
    rw [extendSlabScalar_of_mem hT.le u hs]
    rfl
  have hp₁ : ∀ i s (hs : s ∈ Icc (0 : ℝ) T),
      pd i (extendSlabScalar hT.le u s) =
        fun y => ((pd (E := ℝ) i (θ s) y : ℝ) : ℂ) := by
    intro i s hs
    rw [hslice s hs]
    exact pd_clm_fun Complex.ofRealCLM _ i ((hθ₂ s hs).differentiable (by norm_num))
  have hp₂ : ∀ i j s (hs : s ∈ Icc (0 : ℝ) T),
      pd i (pd j (extendSlabScalar hT.le u s)) =
        fun y => ((pd (E := ℝ) i (pd (E := ℝ) j (θ s)) y : ℝ) : ℂ) := by
    intro i j s hs
    rw [hp₁ j s hs]
    exact pd_clm_fun Complex.ofRealCLM _ i (differentiable_pd (hθ₂ s hs) j)
  have hbper := slabDriftComponent_periodic v hvc C hC hvper
  have hbholder := slabDriftComponent_spatial_holder hβ₀.le hβ₁.le v hv hvc C hC
  obtain ⟨R, hR⟩ := scalar_mild_fixedPoint_fderiv_bdd hν hT.le hβ₀ hβ₁ b f
    hbper (show IsPeriodic f from hfper) (hfc.of_le (by norm_num)) hbholder hu
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨R, fun t ht x => ?_⟩
    have hh : ‖pd i (extendSlabScalar hT.le u t) x‖ ≤ R := by
      rw [show extendSlabScalar hT.le u t = fun y => u (⟨t, ht⟩, y) by
        funext y; rw [extendSlabScalar_of_mem hT.le u ht]]
      exact pd_bound_of_fderiv (hR ⟨t, ht⟩) i x
    simpa only [hp₁ i t ht, Complex.norm_real] using hh
  · intro i j
    obtain ⟨R₂, hR₂⟩ := scalar_mild_fixedPoint_pd2_bdd_regular_drift hν hT.le hβ₀ hβ₁
      v hv hvper hvc C hC f (show IsPeriodic f from hfper) hfc hu i j
    refine ⟨R₂, fun t ht x => ?_⟩
    simpa only [hp₂ i j t ht, Complex.norm_real] using hR₂ t ht x
  · obtain ⟨Rt, hRt⟩ := scalar_mild_fixedPoint_dt_bdd_regular_drift hν hT hβ₀ hβ₁
      v hv hvper hvc C hC f (show IsPeriodic f from hfper) hfc hu
    refine ⟨Rt, fun t ht x => ?_⟩
    have hdt : dt T (extendSlabScalar hT.le u) t x = ((dt T θ t x : ℝ) : ℂ) := by
      calc
        _ = dt T (fun s y => (θ s y : ℂ)) t x :=
          derivWithin_congr (fun s hs => congrFun (hslice s hs) x)
            (congrFun (hslice t ht) x)
        _ = _ := dt_clm hT Complex.ofRealCLM θ x ht
          (real_scalar_mild_hasDerivWithinAt hT.le hν hβ₀ hβ₁ v hv hvper
            θ₀ hθc hθper θ hθjoint hθbound hmild ht x).differentiableWithinAt
    simpa only [hdt, Complex.norm_real] using hRt t ht x

/-- A real solution of the actual equation with all bounded derivative
fields required by `IsParabolicC12`. The three Hölder fields of that
predicate remain separate estimates. -/
theorem exists_real_periodic_global_scalar_bounded_derivatives_equation {T ν β : ℝ}
    (hT : 0 < T) (hν : 0 < ν) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hvdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀) :
    ∃ θ : ℝ → Pt 2 → ℝ,
      Continuous (Function.uncurry θ) ∧ (∀ t, IsPeriodic (θ t)) ∧ θ 0 = θ₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (θ t)) ∧
      (∀ x, ∀ t ∈ Icc (0 : ℝ) T, DifferentiableWithinAt ℝ
        (fun s => θ s x) (Icc 0 T) t) ∧
      BddOn T θ ∧ BddOn T (dt T θ) ∧
      (∀ i : Fin 2, BddOn T (fun t => pd i (θ t))) ∧
      (∀ i j : Fin 2, BddOn T (fun t => pd i (pd j (θ t)))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        dt T θ t x + conv (v t) (θ t) x = ν • lap (θ t) x) := by
  obtain ⟨θ, hc, ⟨C, hC⟩, hp, hinit, hC2, hm⟩ :=
    exists_real_periodic_global_scalar_mild_C2 hT.le hν hβ₀ hβ₁ v hv hvper θ₀ hθc hθper
  obtain ⟨hD1, hD2, hDt⟩ := real_scalar_mild_bdd_derivatives hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc hθper θ hc hC hm
  refine ⟨θ, hc, hp, hinit, hC2, ?_, ⟨C, ?_⟩, hDt, hD1, hD2, ?_⟩
  · intro x t ht
    exact (real_scalar_mild_hasDerivWithinAt hT.le hν hβ₀ hβ₁ v hv hvper
      θ₀ hθc hθper θ hc hC hm ht x).differentiableWithinAt
  · intro t ht x
    simpa only [Real.norm_eq_abs] using hC t x
  · exact real_scalar_mild_equation hT hν hβ₀ hβ₁ v hv hvper hvdiv
      θ₀ hθc hθper θ hc hC hm

end AnomDiss
