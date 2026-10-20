module

public import RequestProject.ScalarGlobalTimeEquation
public import RequestProject.ScalarHessianSchauder
public import RequestProject.HeatDuhamelTimeHolder
public import RequestProject.ScalarHeatTimeSchauder
public import RequestProject.ParabolicHolderOperations
public import RequestProject.ExistenceInterfaces

/-!
# Spatial Schauder estimates for the original scalar drift

The full drift exponent is retained in the actual flux derivatives. It
therefore gives spatial Hölder estimates of the constructed Hessian and,
through the proved time equation, of the actual time derivative.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- Hölder `C²` data remain Hölder `C²` under a continuous linear map. -/
lemma IsHolderC2.clm {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {β : ℝ} {f : Pt d → E} (hf : IsHolderC2 β f) (L : E →L[ℝ] F) :
    IsHolderC2 β (fun y => L (f y)) := by
  obtain ⟨hfc, H, hH⟩ := hf
  have hp₁ : ∀ j, pd j (fun y => L (f y)) = fun y => L (pd j f y) :=
    fun j => pd_clm_fun L f j (hfc.differentiable (by norm_num))
  have hp₂ : ∀ i j, pd i (pd j (fun y => L (f y))) =
      fun y => L (pd i (pd j f) y) := by
    intro i j
    rw [hp₁ j]
    exact pd_clm_fun L _ i (differentiable_pd hfc j)
  refine ⟨L.contDiff.comp hfc, ‖L‖ * H, fun i j x y => ?_⟩
  rw [hp₂, ← map_sub]
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hH i j x y)
    (norm_nonneg _)).trans_eq (by ring))

lemma pd2_complex_ofReal_C2 (f : Pt 2 → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin 2) :
    pd i (pd j (fun y => (f y : ℂ))) =
      fun y => ((pd (E := ℝ) i (pd (E := ℝ) j f) y : ℝ) : ℂ) := by
  change pd i (pd j (fun y => Complex.ofRealCLM (f y))) = _
  rw [pd_clm_fun Complex.ofRealCLM f j (hf.differentiable (by norm_num))]
  exact pd_clm_fun Complex.ofRealCLM _ i (differentiable_pd hf j)

/-- The constructed fixed point for the original drift has uniformly
spatially `β`-Hölder Hessian entries at the original exponent. -/
theorem scalar_mild_fixedPoint_hessian_spatial_holder_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : IsHolderC2 β (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u) :
    ∃ H, 0 ≤ H ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ i j x y,
      ‖pd i (pd j (extendSlabScalar hT u t)) x -
        pd i (pd j (extendSlabScalar hT u t)) y‖ ≤ H * ‖x - y‖ ^ β := by
  apply scalar_mild_fixedPoint_hessian_spatial_holder hν hT hβ₀ hβ₁
    (slabDriftComponent v hc C hC) f hu hfc hfper
  exact scalar_mild_fixedPoint_flux_derivative_regular hν hT hβ₀ hβ₁ hβ₀.le le_rfl
    v hv hvper hc C hC f hfper hfc.1 hu

/-- The actual time derivative has the original spatial Hölder exponent,
derived from the genuine PDE, the Hessian estimate, and flux regularity. -/
theorem scalar_mild_fixedPoint_dt_spatial_holder_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : IsHolderC2 β (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT.le (slabDriftComponent v hc C hC) f u = u) :
    ∃ H, 0 ≤ H ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      ‖dt T (extendSlabScalar hT.le u) t x - dt T (extendSlabScalar hT.le u) t y‖ ≤
        H * ‖x - y‖ ^ β := by
  let b := slabDriftComponent v hc C hC
  obtain ⟨R, hR₀, hR⟩ := scalar_mild_fixedPoint_hessian_spatial_holder_regular_drift
    hν hT.le hβ₀ hβ₁ v hv hvper hc C hC f hfper hfc hu
  have hflux := scalar_mild_fixedPoint_flux_derivative_regular hν hT.le hβ₀ hβ₁
    hβ₀.le le_rfl v hv hvper hc C hC f hfper hfc.1 hu
  obtain ⟨_, _, _, _, ⟨H₀, hH₀, hHH₀⟩⟩ := hflux 0
  obtain ⟨_, _, _, _, ⟨H₁, hH₁, hHH₁⟩⟩ := hflux 1
  refine ⟨|ν| * (R + R) + (H₀ + H₁), by positivity, fun t ht x y => ?_⟩
  let U := extendSlabScalar hT.le u
  let P : Fin 2 → Pt 2 → ℂ := fun i => pd i (extendSlabScalar hT.le (b i * u) t)
  have hdt : ∀ z, dt T U t z = ν • lap (U t) z - (P 0 z + P 1 z) := by
    intro z
    have hd := scalar_mild_fixedPoint_hasDerivWithinAt_regular_drift hν hT.le hβ₀ hβ₁
      v hv hvper hc C hC f hfper hfc.1 hu ht z
    simpa only [dt, U, P, b, Fin.sum_univ_two] using
      hd.derivWithin (uniqueDiffOn_Icc hT t ht)
  have hlap : ‖lap (U t) x - lap (U t) y‖ ≤ (R + R) * ‖x - y‖ ^ β := by
    simp only [lap, Fin.sum_univ_two]
    rw [add_sub_add_comm]
    exact ((norm_add_le _ _).trans (add_le_add (hR t ht 0 0 x y)
      (hR t ht 1 1 x y))).trans_eq (by ring)
  change ‖dt T U t x - dt T U t y‖ ≤ _
  calc
    _ = ‖ν • (lap (U t) x - lap (U t) y) -
        ((P 0 x - P 0 y) + (P 1 x - P 1 y))‖ := by
      rw [hdt x, hdt y, smul_sub]
      congr 1
      abel
    _ ≤ ‖ν • (lap (U t) x - lap (U t) y)‖ +
        (‖P 0 x - P 0 y‖ + ‖P 1 x - P 1 y‖) :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ |ν| * ((R + R) * ‖x - y‖ ^ β) +
        (H₀ * ‖x - y‖ ^ β + H₁ * ‖x - y‖ ^ β) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left hlap (abs_nonneg _))
        (add_le_add (hHH₀ t x y) (hHH₁ t x y))
    _ = _ := by ring

/-- Identifies any genuine bounded continuous real mild solution with a slab
fixed point, preserving its original initial data and all values on `[0,T]`.
This is a proved representation, not an extra existence hypothesis. -/
theorem real_scalar_mild_slab_representation {T ν β : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (θ₀ : Pt 2 → ℝ) (hθc : Continuous θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∃ (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
      (f : Pt 2 →ᵇ ℂ) (u : SlabScalar T),
      scalarMildMap hν hT (slabDriftComponent v (hv.continuousOn hβ₀) C hC) f u = u ∧
      (f : Pt 2 → ℂ) = (fun y => (θ₀ y : ℂ)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, extendSlabScalar hT u t = fun y => (θ t y : ℂ) := by
  have hvc := hv.continuousOn hβ₀
  obtain ⟨C, hC⟩ := hv.bdd
  let b : Fin 2 → SlabScalar T := slabDriftComponent v hvc C hC
  have hfcont : Continuous (fun x => (θ₀ x : ℂ)) := Complex.continuous_ofReal.comp hθc
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
  refine ⟨C, hC, f, u, ?_, rfl, ?_⟩
  · change scalarMildMap hν hT b f u = u
    apply BoundedContinuousFunction.ext
    intro p
    simp only [scalarMildMap, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.sum_apply, slabHeatInitial_apply, slabDuhamel_apply]
    simp_rw [he]
    exact (hmild p.1 p.1.property p.2).symm
  · intro t ht
    funext y
    rw [extendSlabScalar_of_mem hT u ht]
    rfl

/-- Spatial Hölder bounds for the true Hessian and true time derivative of
a real mild solution for the original data, with the original exponent. -/
theorem real_scalar_mild_spatial_schauder {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : IsHolderC2 β θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    (∃ H, 0 ≤ H ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ i j x y,
      ‖pd i (pd j (θ t)) x - pd i (pd j (θ t)) y‖ ≤ H * ‖x - y‖ ^ β) ∧
    (∃ H, 0 ≤ H ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      ‖dt T θ t x - dt T θ t y‖ ≤ H * ‖x - y‖ ^ β) := by
  obtain ⟨C, hC, f, u, hu, hf, hslice⟩ := real_scalar_mild_slab_representation hT.le hν hβ₀
    v hv θ₀ hθc.1.continuous hθper θ hθjoint hθbound hmild
  have hfper : IsPeriodic f := by
    rw [hf]
    intro x m
    dsimp only
    rw [hθper x m]
  have hfc : IsHolderC2 β (f : Pt 2 → ℂ) := by
    rw [hf]
    exact hθc.clm Complex.ofRealCLM
  have hθ₂ := real_scalar_mild_contDiff_two hT.le hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc.1 hθper θ hθjoint hθbound hmild
  constructor
  · obtain ⟨H, hH, hholder⟩ := scalar_mild_fixedPoint_hessian_spatial_holder_regular_drift
      hν hT.le hβ₀ hβ₁ v hv hvper (hv.continuousOn hβ₀) C hC f hfper hfc hu
    refine ⟨H, hH, fun t ht i j x y => ?_⟩
    have hh := hholder t ht i j x y
    rw [hslice t ht, pd2_complex_ofReal_C2 _ (hθ₂ t ht)] at hh
    simpa only [← Complex.ofReal_sub, Complex.norm_real] using hh
  · obtain ⟨H, hH, hholder⟩ := scalar_mild_fixedPoint_dt_spatial_holder_regular_drift
      hν hT hβ₀ hβ₁ v hv hvper (hv.continuousOn hβ₀) C hC f hfper hfc hu
    refine ⟨H, hH, fun t ht x y => ?_⟩
    have hdt : ∀ z, dt T (extendSlabScalar hT.le u) t z = ((dt T θ t z : ℝ) : ℂ) := by
      intro z
      calc
        _ = dt T (fun s w => (θ s w : ℂ)) t z :=
          derivWithin_congr (fun s hs => congrFun (hslice s hs) z)
            (congrFun (hslice t ht) z)
        _ = _ := dt_clm hT Complex.ofRealCLM θ z ht
          (real_scalar_mild_hasDerivWithinAt hT.le hν hβ₀ hβ₁ v hv hvper
            θ₀ hθc.1 hθper θ hθjoint hθbound hmild ht z).differentiableWithinAt
    have hh := hholder t ht x y
    simpa only [hdt, ← Complex.ofReal_sub, Complex.norm_real] using hh


/-- The actual fixed-point Hessian has the required `β/2` time exponent
including both closed-slab endpoints. -/
theorem scalar_mild_fixedPoint_hessian_time_holder_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : IsHolderC2 β (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u) (i j : Fin 2) :
    TimeHolder T (β / 2) (fun t => pd i (pd j (extendSlabScalar hT u t))) := by
  let b := slabDriftComponent v hc C hC
  let A : ℝ → Pt 2 → ℂ := fun t => heatOp (Real.toNNReal (2 * ν * t)) f
  let D : Fin 2 → ℝ → Pt 2 → ℂ := fun k =>
    duhamelComponent ν (extendSlabScalar hT (b k * u)) k
  have hflux := scalar_mild_fixedPoint_flux_derivative_regular hν hT hβ₀ hβ₁
    hβ₀.le le_rfl v hv hvper hc C hC f hfper hfc.1 hu
  have hDs : ∀ k t, 0 ≤ t → ContDiff ℝ 2 (D k t) := by
    intro k t ht
    obtain ⟨hGc, hGs, hGp, ⟨B, hB⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    exact contDiff_two_duhamelComponent_of_flux_derivative_holder hν k hGc hGs hGp
      hB hH hβ₀ hholder ht
  have hAs : ∀ t, ContDiff ℝ 2 (A t) := fun t =>
    contDiff_heatOp (isQP_zero_iff.2 hfper) hfc.1 _
  have hDtime : ∀ k, TimeHolder T (β / 2) (fun t => pd i (pd j (D k t))) := by
    intro k
    obtain ⟨hGc, hGs, hGp, ⟨B, hB⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    apply timeHolder_congr (G := fun t => pd i (pd j
      (heatDuhamel ν (fun s => pd k (extendSlabScalar hT (b k * u) s)) t)))
    · intro t ht
      have he : D k t = heatDuhamel ν
          (fun s => pd k (extendSlabScalar hT (b k * u) s)) t := by
        funext z
        exact duhamelComponent_eq_heatDuhamel_pd hν hGs hGp ht.1 k z
      rw [he]
    · exact timeHolder_pd2_heatDuhamel_holder hν hGc
        (fun s => isPeriodic_pd _ (hGp s) k) hB hH hβ₀ hβ₁ hholder T i j
  obtain ⟨KA, hKA⟩ := (pd2_heatOp_timeHolder hfc hfper hβ₀ hν.le i j :
    TimeHolder T (β / 2) (fun t => pd i (pd j (A t))))
  obtain ⟨K₀, hK₀⟩ := hDtime 0
  obtain ⟨K₁, hK₁⟩ := hDtime 1
  have he : ∀ t ∈ Icc (0 : ℝ) T, extendSlabScalar hT u t =
      fun z => A t z - D 0 t z - D 1 t z := by
    intro t ht
    funext z
    rw [extendSlabScalar_of_mem hT u ht]
    have hh := congrArg (fun w : SlabScalar T => w (⟨t, ht⟩, z)) hu
    simpa [scalarMildMap, A, D, b, Fin.sum_univ_two, sub_add_eq_sub_sub] using hh.symm
  have hdecomp : ∀ t ∈ Icc (0 : ℝ) T, ∀ z,
      pd i (pd j (extendSlabScalar hT u t)) z =
        pd i (pd j (A t)) z - pd i (pd j (D 0 t)) z - pd i (pd j (D 1 t)) z := by
    intro t ht z
    rw [he t ht, pd2_sub_C2 _ _ ((hAs t).sub (hDs 0 t ht.1)) (hDs 1 t ht.1),
      pd2_sub_C2 _ _ (hAs t) (hDs 0 t ht.1)]
  refine ⟨KA + K₀ + K₁, fun t ht s hs x => ?_⟩
  dsimp only
  rw [hdecomp t ht x, hdecomp s hs x]
  have heq : ∀ a b c d e f : ℂ,
      (a - b - c) - (d - e - f) = ((a - d) - (b - e)) - (c - f) := by intros; ring
  rw [heq]
  apply ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
  exact (add_le_add (add_le_add (hKA t ht s hs x) (hK₀ t ht s hs x))
    (hK₁ t ht s hs x)).trans_eq (by ring)

/-- The original real mild solution has the precise Hessian time Hölder
estimate used in parabolic `C^{1+β/2,2+β}`. -/
theorem real_scalar_mild_hessian_time_holder {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : IsHolderC2 β θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∀ i j : Fin 2, TimeHolder T (β / 2) (fun t => pd i (pd j (θ t))) := by
  obtain ⟨C, hC, f, u, hu, hf, hslice⟩ := real_scalar_mild_slab_representation hT.le hν hβ₀
    v hv θ₀ hθc.1.continuous hθper θ hθjoint hθbound hmild
  have hfper : IsPeriodic f := by
    rw [hf]
    intro x m
    dsimp only
    rw [hθper x m]
  have hfc : IsHolderC2 β (f : Pt 2 → ℂ) := by
    rw [hf]
    exact hθc.clm Complex.ofRealCLM
  have hθ₂ := real_scalar_mild_contDiff_two hT.le hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc.1 hθper θ hθjoint hθbound hmild
  intro i j
  have hh := scalar_mild_fixedPoint_hessian_time_holder_regular_drift
    hν hT.le hβ₀ hβ₁ v hv hvper (hv.continuousOn hβ₀) C hC f hfper hfc hu i j
  apply timeHolder_congr (G := fun t x =>
    Complex.reCLM (pd i (pd j (extendSlabScalar hT.le u t)) x))
  · intro t ht
    funext x
    rw [hslice t ht, pd2_complex_ofReal_C2 _ (hθ₂ t ht)]
    rfl
  · exact hh.clm Complex.reCLM


/-- The true gradient of the fixed point has the full `(1+β)/2`
time Hölder exponent. -/
theorem scalar_mild_fixedPoint_gradient_time_holder_regular_drift
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hc : ContinuousOn (Function.uncurry v) (Icc (0 : ℝ) T ×ˢ univ))
    (C : ℝ) (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ C)
    (f : Pt 2 →ᵇ ℂ) (hfper : IsPeriodic f) (hfc : IsHolderC2 β (f : Pt 2 → ℂ))
    {u : SlabScalar T}
    (hu : scalarMildMap hν hT (slabDriftComponent v hc C hC) f u = u) (i : Fin 2) :
    TimeHolder T ((1 + β) / 2) (fun t => pd i (extendSlabScalar hT u t)) := by
  let b := slabDriftComponent v hc C hC
  let A : ℝ → Pt 2 → ℂ := fun t => heatOp (Real.toNNReal (2 * ν * t)) f
  let D : Fin 2 → ℝ → Pt 2 → ℂ := fun k =>
    duhamelComponent ν (extendSlabScalar hT (b k * u)) k
  have hflux := scalar_mild_fixedPoint_flux_derivative_regular hν hT hβ₀ hβ₁
    hβ₀.le le_rfl v hv hvper hc C hC f hfper hfc.1 hu
  have hDs : ∀ k t, 0 ≤ t → ContDiff ℝ 2 (D k t) := by
    intro k t ht
    obtain ⟨hGc, hGs, hGp, ⟨B, hB⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    exact contDiff_two_duhamelComponent_of_flux_derivative_holder hν k hGc hGs hGp
      hB hH hβ₀ hholder ht
  have hAs : ∀ t, ContDiff ℝ 2 (A t) := fun t =>
    contDiff_heatOp (isQP_zero_iff.2 hfper) hfc.1 _
  have hDtime : ∀ k, TimeHolder T ((1 + β) / 2) (fun t => pd i (D k t)) := by
    intro k
    obtain ⟨hGc, hGs, hGp, ⟨B, hB⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    apply timeHolder_congr (G := fun t => pd i
      (heatDuhamel ν (fun s => pd k (extendSlabScalar hT (b k * u) s)) t))
    · intro t ht
      have he : D k t = heatDuhamel ν
          (fun s => pd k (extendSlabScalar hT (b k * u) s)) t := by
        funext z
        exact duhamelComponent_eq_heatDuhamel_pd hν hGs hGp ht.1 k z
      rw [he]
    · exact timeHolder_pd_heatDuhamel_holder hν hGc
        (fun s => isPeriodic_pd _ (hGp s) k) hB hH hβ₀ hβ₁ hholder T i
  have hAtime : TimeHolder T ((1 + β) / 2) (fun t => pd i (A t)) :=
    pd_heatOp_timeHolder hfc hfper hβ₀.le hν.le i
  apply timeHolder_congr (G := fun t x =>
    pd i (A t) x - pd i (D 0 t) x - pd i (D 1 t) x)
  · intro t ht
    have he : extendSlabScalar hT u t = fun z => A t z - D 0 t z - D 1 t z := by
      funext z
      rw [extendSlabScalar_of_mem hT u ht]
      have hh := congrArg (fun w : SlabScalar T => w (⟨t, ht⟩, z)) hu
      simpa [scalarMildMap, A, D, b, Fin.sum_univ_two, sub_add_eq_sub_sub] using hh.symm
    rw [he, pd_sub_fun _ _ (((hAs t).sub (hDs 0 t ht.1)).differentiable (by norm_num))
      ((hDs 1 t ht.1).differentiable (by norm_num)),
      pd_sub_fun _ _ ((hAs t).differentiable (by norm_num))
        ((hDs 0 t ht.1).differentiable (by norm_num))]
  · exact (hAtime.sub (hDtime 0)).sub (hDtime 1)

/-- The actual real gradient has the full temporal exponent required by
`IsParabolicC12`, with no loss of the initial exponent. -/
theorem real_scalar_mild_gradient_time_holder {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : IsHolderC2 β θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∀ i : Fin 2, TimeHolder T ((1 + β) / 2) (fun t => pd i (θ t)) := by
  obtain ⟨C, hC, f, u, hu, hf, hslice⟩ := real_scalar_mild_slab_representation hT.le hν hβ₀
    v hv θ₀ hθc.1.continuous hθper θ hθjoint hθbound hmild
  have hfper : IsPeriodic f := by
    rw [hf]
    intro x m
    dsimp only
    rw [hθper x m]
  have hfc : IsHolderC2 β (f : Pt 2 → ℂ) := by
    rw [hf]
    exact hθc.clm Complex.ofRealCLM
  have hθ₂ := real_scalar_mild_contDiff_two hT.le hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc.1 hθper θ hθjoint hθbound hmild
  intro i
  have hh := scalar_mild_fixedPoint_gradient_time_holder_regular_drift
    hν hT.le hβ₀ hβ₁ v hv hvper (hv.continuousOn hβ₀) C hC f hfper hfc hu i
  apply timeHolder_congr (G := fun t x =>
    Complex.reCLM (pd i (extendSlabScalar hT.le u t) x))
  · intro t ht
    funext x
    rw [hslice t ht]
    change pd i (θ t) x = Complex.reCLM (pd i (fun y => Complex.ofRealCLM (θ t y)) x)
    rw [pd_clm_fun Complex.ofRealCLM _ i ((hθ₂ t ht).differentiable (by norm_num))]
    rfl
  · exact hh.clm Complex.reCLM

/-- The actual real Hessian is parabolically `β`-Hölder on the entire closed
slab, including the original initial value. -/
theorem real_scalar_mild_hessian_parHolder {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : IsHolderC2 β θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∀ i j : Fin 2, ParHolder T β (fun t => pd i (pd j (θ t))) := by
  obtain ⟨⟨H, _, hH⟩, _⟩ := real_scalar_mild_spatial_schauder hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc hθper θ hθjoint hθbound hmild
  intro i j
  apply parHolder_of_spatial_time ⟨H, fun t ht x y => hH t ht i j x y⟩
  exact real_scalar_mild_hessian_time_holder hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc hθper θ hθjoint hθbound hmild i j


/-- The actual real gradient keeps the original uniform spatial exponent. -/
theorem real_scalar_mild_gradient_spatial_holder {T ν β : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : ContDiff ℝ 2 θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∃ H, 0 ≤ H ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ i x y,
      ‖pd i (θ t) x - pd i (θ t) y‖ ≤ H * ‖x - y‖ ^ β := by
  obtain ⟨C, hC, f, u, hu, hf, hslice⟩ := real_scalar_mild_slab_representation hT hν hβ₀
    v hv θ₀ hθc.continuous hθper θ hθjoint hθbound hmild
  have hfper : IsPeriodic f := by
    rw [hf]
    intro x m
    dsimp only
    rw [hθper x m]
  have hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ) := by
    rw [hf]
    exact Complex.ofRealCLM.contDiff.comp hθc
  have hvc := hv.continuousOn hβ₀
  let b := slabDriftComponent v hvc C hC
  have hbper := slabDriftComponent_periodic v hvc C hC hvper
  have hbholder := slabDriftComponent_spatial_holder hβ₀.le hβ₁.le v hv hvc C hC
  obtain ⟨H, hH, hholder⟩ := scalar_mild_fixedPoint_fderiv_spatial_holder
    hν hT hβ₀ hβ₁ b f hbper hfper hfc hbholder hu
  have hθ₂ := real_scalar_mild_contDiff_two hT hν hβ₀ hβ₁ v hv hvper
    θ₀ hθc hθper θ hθjoint hθbound hmild
  refine ⟨H, hH, fun t ht i x y => ?_⟩
  have hh := partial_holder_of_fderiv_holder (hholder ⟨t, ht⟩) i x y
  have he : (fun z => u (⟨t, ht⟩, z)) = fun z => (θ t z : ℂ) := by
    have hh := hslice t ht
    rw [show extendSlabScalar hT u t = fun z => u (⟨t, ht⟩, z) by
      funext z; rw [extendSlabScalar_of_mem hT u ht]] at hh
    exact hh
  rw [he] at hh
  have hp : pd i (fun z => (θ t z : ℂ)) =
      fun z => ((pd (E := ℝ) i (θ t) z : ℝ) : ℂ) :=
    pd_clm_fun Complex.ofRealCLM _ i ((hθ₂ t ht).differentiable (by norm_num))
  simpa only [hp, ← Complex.ofReal_sub, Complex.norm_real] using hh

/-- Components of the original drift are parabolically Hölder at the
original exponent. -/
theorem IsParabolicC01.component_parHolder {T β : ℝ} {v : ℝ → Pt 2 → Pt 2}
    (hv : IsParabolicC01 T β v) (hβ₀ : 0 < β) (hβ₁ : β < 1) (i : Fin 2) :
    ParHolder T β (fun t x => v t x i) := by
  have hc := hv.continuousOn hβ₀
  obtain ⟨C, hC⟩ := hv.bdd
  obtain ⟨H, hH⟩ := slabDriftComponent_spatial_holder hβ₀.le hβ₁.le v hv hc C hC i
  apply parHolder_of_spatial_time
  · refine ⟨H, ?_⟩
    intro t ht x y
    have hh := hH ⟨t, ht⟩ x y
    simpa only [slabDriftComponent_apply, ← Complex.ofReal_sub, Complex.norm_real] using hh
  · exact hv.holder_time.clm (ContinuousLinearMap.proj i)

/-- The actual gradient is parabolically Hölder at exponent `β`. The proved
stronger time exponent is reduced using its actual uniform bound. -/
theorem real_scalar_mild_gradient_parHolder {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (θ₀ : Pt 2 → ℝ) (hθc : IsHolderC2 β θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ∀ i : Fin 2, ParHolder T β (fun t => pd i (θ t)) := by
  obtain ⟨H, _, hH⟩ := real_scalar_mild_gradient_spatial_holder hT.le hν hβ₀ hβ₁
    v hv hvper θ₀ hθc.1 hθper θ hθjoint hθbound hmild
  obtain ⟨hD₁, _, _⟩ := real_scalar_mild_bdd_derivatives hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc.1 hθper θ hθjoint hθbound hmild
  intro i
  apply parHolder_of_spatial_time ⟨H, fun t ht x y => hH t ht i x y⟩
  exact (real_scalar_mild_gradient_time_holder hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc hθper θ hθjoint hθbound hmild i).lower_of_bdd
      (hD₁ i) (by positivity) (by linarith)

/-- The actual time derivative is parabolically Hölder at the original
exponent, by the actual advection–diffusion equation and the proved
Hessian and gradient estimates. -/
theorem real_scalar_mild_dt_parHolder {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hvdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (hθc : IsHolderC2 β θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    ParHolder T β (dt T θ) := by
  have hH₂ := real_scalar_mild_hessian_parHolder hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc hθper θ hθjoint hθbound hmild
  have hH₁ := real_scalar_mild_gradient_parHolder hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc hθper θ hθjoint hθbound hmild
  obtain ⟨hD₁, _, _⟩ := real_scalar_mild_bdd_derivatives hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc.1 hθper θ hθjoint hθbound hmild
  have hprod : ∀ i : Fin 2, ParHolder T β (fun t x => v t x i * pd i (θ t) x) := by
    intro i
    exact (hv.component_parHolder hβ₀ hβ₁ i).mul (hH₁ i)
      (hv.bdd.clm (ContinuousLinearMap.proj i)) (hD₁ i)
  have hconv : ParHolder T β (fun t x => conv (v t) (θ t) x) := by
    simpa only [conv, Fin.sum_univ_two, smul_eq_mul] using (hprod 0).add (hprod 1)
  have hlap : ParHolder T β (fun t x => lap (θ t) x) := by
    simpa only [lap, Fin.sum_univ_two] using (hH₂ 0 0).add (hH₂ 1 1)
  have hνlap : ParHolder T β (fun t x => ν * lap (θ t) x) := by
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      using hlap.clm (ν • ContinuousLinearMap.id ℝ ℝ)
  apply parHolder_congr (G := fun t x => ν * lap (θ t) x - conv (v t) (θ t) x)
  · intro t ht
    funext x
    exact eq_sub_of_add_eq (real_scalar_mild_equation hT hν hβ₀ hβ₁ v hv hvper hvdiv
      θ₀ hθc.1 hθper θ hθjoint hθbound hmild t ht x)
  · exact hνlap.sub hconv

/-- The genuine real mild solution has all the fields of the original
parabolic Hölder predicate, at the original exponent `β`. -/
theorem real_scalar_mild_isParabolicC12 {T ν β : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) (v : ℝ → Pt 2 → Pt 2) (hv : IsParabolicC01 T β v)
    (hvper : ∀ t ∈ Icc (0 : ℝ) T, IsPeriodic (v t))
    (hvdiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (hθc : IsHolderC2 β θ₀) (hθper : IsPeriodic θ₀)
    (θ : ℝ → Pt 2 → ℝ) (hθjoint : Continuous (Function.uncurry θ))
    {Cθ : ℝ} (hθbound : ∀ t x, |θ t x| ≤ Cθ)
    (hmild : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (θ t x : ℂ) = heatOp (Real.toNNReal (2 * ν * t)) (fun y => (θ₀ y : ℂ)) x -
        ∑ i : Fin 2, duhamelComponent ν
          (fun s y => (v s y i : ℂ) * (θ s y : ℂ)) i t x) :
    IsParabolicC12 T β θ := by
  obtain ⟨hD₁, hD₂, hDt⟩ := real_scalar_mild_bdd_derivatives hT hν hβ₀ hβ₁
    v hv hvper θ₀ hθc.1 hθper θ hθjoint hθbound hmild
  exact {
    smooth_x := real_scalar_mild_contDiff_two hT.le hν hβ₀ hβ₁
      v hv hvper θ₀ hθc.1 hθper θ hθjoint hθbound hmild
    diff_t := fun x t ht => (real_scalar_mild_hasDerivWithinAt hT.le hν hβ₀ hβ₁
      v hv hvper θ₀ hθc.1 hθper θ hθjoint hθbound hmild ht x).differentiableWithinAt
    bdd := ⟨Cθ, fun t ht x => by simpa only [Real.norm_eq_abs] using hθbound t x⟩
    bdd_dt := hDt
    holder_dt := real_scalar_mild_dt_parHolder hT hν hβ₀ hβ₁
      v hv hvper hvdiv θ₀ hθc hθper θ hθjoint hθbound hmild
    bdd_d1 := hD₁
    holder_d1_time := real_scalar_mild_gradient_time_holder hT hν hβ₀ hβ₁
      v hv hvper θ₀ hθc hθper θ hθjoint hθbound hmild
    bdd_d2 := hD₂
    holder_d2 := real_scalar_mild_hessian_parHolder hT hν hβ₀ hβ₁
      v hv hvper θ₀ hθc hθper θ hθjoint hθbound hmild }

/-- Unconditional classical scalar existence with the exact original
parabolic exponent; all existence, PDE, and regularity fields are proved
from the original drift and initial data. -/
theorem scalarClassicalExistence_proved : ScalarClassicalExistence := by
  intro T ν β hT hν hβ₀ hβ₁ v hvper hv hvdiv θ₀ hθper hθc
  obtain ⟨θ, hc, ⟨C, hC⟩, hp, hinit, hm⟩ :=
    exists_real_periodic_global_scalar_mild hT.le hν hβ₀ v hv hvper θ₀ hθc.1.continuous hθper
  have hreg := real_scalar_mild_isParabolicC12 hT hν hβ₀ hβ₁
    v hv hvper hvdiv θ₀ hθc hθper θ hc hC hm
  exact ⟨θ, hreg, {
    periodic := fun t ht => hp t
    regular := ⟨β, hβ₀, hβ₁, hreg⟩
    init := hinit
    eqn := real_scalar_mild_equation hT hν hβ₀ hβ₁ v hv hvper hvdiv
      θ₀ hθc.1 hθper θ hc hC hm }⟩

/-- The scalar analytic interface is a theorem, using the separately proved
maximum-principle uniqueness theorem. -/
theorem externalScalar_proved : ExternalScalar :=
  externalScalar_of_existence scalarClassicalExistence_proved

end AnomDiss
