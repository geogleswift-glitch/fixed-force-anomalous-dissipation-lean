module

public import RequestProject.Controls

/-!
# Lemma 2.16: the damped response

The damped response `B_{μ,ω}` of Definition 2.15 lies in the four-dimensional space `𝓔` for every
time, with coefficient vector obtained from the coefficients of the control by a damped time
integral.  The `C^a` norm and the `L^∞` operator norm of the gradient are seminorms on the
coefficient vectors satisfying a Jensen-type inequality for time integrals, from which the
estimates of Lemma 2.16 follow.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-! ### Linear structure of the eigenfields -/

lemma eBasis_eq_eField (i : Fin 4) : eBasis i = eField (Pi.single i 1) := by
  funext x; simp [eField, Pi.single_apply]

lemma contDiff_eBasis (i : Fin 4) : ContDiff ℝ ∞ (eBasis i) := by
  rw [eBasis_eq_eField]; exact (eigenspace_properties _).1

lemma eField_eq_sum (c : Fin 4 → ℝ) : eField c = fun x => ∑ i, c i • eBasis i x := rfl

/-- `v ↦ D^k (∑ vᵢ eᵢ)(x)` as a continuous linear map. -/
noncomputable def iterCLM (k : ℕ) (x : Pt 2) :
    (Fin 4 → ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Pt 2) (Pt 2) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (iteratedFDeriv ℝ k (eBasis i) x)

lemma iteratedFDeriv_eField (k : ℕ) (c : Fin 4 → ℝ) (x : Pt 2) :
    iteratedFDeriv ℝ k (eField c) x = iterCLM k x c := by
  rw [eField_eq_sum, iteratedFDeriv_sum (fun i _ => ((contDiff_eBasis i).const_smul (c i)).of_le
    (by exact_mod_cast le_top))]
  simp only [iterCLM, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact iteratedFDeriv_const_smul_apply (R := ℝ) (a := c i) (f := eBasis i)
    ((contDiff_eBasis i).of_le (by exact_mod_cast le_top)).contDiffAt

lemma continuous_iterCLM (k : ℕ) (v : Fin 4 → ℝ) : Continuous fun x => iterCLM k x v := by
  simp only [iterCLM, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  exact continuous_finset_sum _ fun i _ =>
    ((contDiff_eBasis i).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).fun_const_smul (v i)

/-- The function whose supremum is the `C^a` norm of `∑ vᵢ eᵢ`. -/
noncomputable def cSum (a : ℕ) (v : Fin 4 → ℝ) (x : Pt 2) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (a + 1), ‖iterCLM k x v‖ₑ

lemma cNormE_eField (a : ℕ) (v : Fin 4 → ℝ) : cNormE a (eField v) = ⨆ x, cSum a v x := by
  simp [cNormE, cSum, iteratedFDeriv_eField]

lemma cNormE_eField_sub (a : ℕ) (v : Fin 4 → ℝ) (z : Pt 2) :
    cNormE a (fun x => eField v (x - z)) = cNormE a (eField v) := by
  simp only [cNormE]
  simp_rw [iteratedFDeriv_comp_sub]
  exact (Equiv.subRight z).iSup_comp (g := fun y => ∑ k ∈ Finset.range (a + 1),
    ‖iteratedFDeriv ℝ k (eField v) y‖ₑ)

lemma cSum_smul (a : ℕ) (t : ℝ) (v : Fin 4 → ℝ) (x : Pt 2) :
    cSum a (t • v) x = ‖t‖ₑ * cSum a v x := by
  simp [cSum, enorm_smul, Finset.mul_sum]

lemma cSum_sub_le (a : ℕ) (v w : Fin 4 → ℝ) (x : Pt 2) :
    cSum a (v - w) x ≤ cSum a v x + cSum a w x := by
  simp only [cSum, map_sub, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => enorm_sub_le

lemma iSup_cSum_smul (a : ℕ) (t : ℝ) (v : Fin 4 → ℝ) :
    (⨆ x, cSum a (t • v) x) = ‖t‖ₑ * ⨆ x, cSum a v x := by
  simp [cSum_smul, ENNReal.mul_iSup]

lemma iSup_cSum_sub_le (a : ℕ) (v w : Fin 4 → ℝ) :
    (⨆ x, cSum a (v - w) x) ≤ (⨆ x, cSum a v x) + ⨆ x, cSum a w x :=
  iSup_le fun x => (cSum_sub_le a v w x).trans (add_le_add (le_iSup _ x) (le_iSup _ x))

lemma continuous_cSum (a : ℕ) (v : Fin 4 → ℝ) : Continuous (cSum a v) :=
  continuous_finset_sum _ fun k _ => continuous_enorm.comp (continuous_iterCLM k v)

lemma continuous_cSum_comp (a : ℕ) {h : ℝ → Fin 4 → ℝ} (hh : Continuous h) (x : Pt 2) :
    Continuous fun r => cSum a (h r) x :=
  continuous_finset_sum _ fun k _ => continuous_enorm.comp ((iterCLM k x).continuous.comp hh)

/-- A supremum of a continuous function over `ℝ²` is a supremum over rational points. -/
lemma iSup_eq_iSup_rat {f : Pt 2 → ℝ≥0∞} (hf : Continuous f) :
    (⨆ x, f x) = ⨆ q : Fin 2 → ℚ, f (fun i => (q i : ℝ)) := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun q => le_iSup _ _)
  have hd : DenseRange (fun q : Fin 2 → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hcl : IsClosed {y : Pt 2 | f y ≤ ⨆ q : Fin 2 → ℚ, f (fun i => (q i : ℝ))} :=
    isClosed_le hf continuous_const
  have : Set.range (fun q : Fin 2 → ℚ => fun i => (q i : ℝ)) ⊆
      {y : Pt 2 | f y ≤ ⨆ q : Fin 2 → ℚ, f (fun i => (q i : ℝ))} := by
    rintro _ ⟨q, rfl⟩; exact le_iSup (fun q : Fin 2 → ℚ => f (fun i => (q i : ℝ))) q
  have := hcl.closure_subset_iff.2 this
  rw [hd.closure_range] at this
  exact this (Set.mem_univ x)

lemma measurable_iSup_cSum (a : ℕ) {h : ℝ → Fin 4 → ℝ} (hh : Continuous h) :
    Measurable fun r => ⨆ x, cSum a (h r) x := by
  simp_rw [iSup_eq_iSup_rat (continuous_cSum a _)]
  exact Measurable.iSup fun q => (continuous_cSum_comp a hh _).measurable

lemma iSup_cSum_integral_le (a : ℕ) {h : ℝ → Fin 4 → ℝ} (hh : Continuous h) {s : ℝ}
    (hs : 0 ≤ s) :
    (⨆ x, cSum a (∫ r in (0 : ℝ)..s, h r) x) ≤ ∫⁻ r in Ioc 0 s, ⨆ x, cSum a (h r) x := by
  refine iSup_le fun x => ?_
  have hint : IntegrableOn h (Ioc 0 s) := (hh.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  calc cSum a (∫ r in (0 : ℝ)..s, h r) x
      = ∑ k ∈ Finset.range (a + 1), ‖∫ r in Ioc 0 s, iterCLM k x (h r)‖ₑ := by
        simp only [cSum, intervalIntegral.integral_of_le hs]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ContinuousLinearMap.integral_comp_comm _ hint]
    _ ≤ ∑ k ∈ Finset.range (a + 1), ∫⁻ r in Ioc 0 s, ‖iterCLM k x (h r)‖ₑ :=
        Finset.sum_le_sum fun k _ => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ r in Ioc 0 s, cSum a (h r) x := by
        simp only [cSum]
        rw [lintegral_finset_sum]
        · intro k _
          exact (continuous_enorm.comp ((iterCLM k x).continuous.comp hh)).measurable
    _ ≤ ∫⁻ r in Ioc 0 s, ⨆ x, cSum a (h r) x := lintegral_mono fun r => le_iSup _ x

/-- `ℝ²` with the Euclidean norm. -/
noncomputable def toE : Pt 2 →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap

lemma euclNorm_eq (v : Pt 2) : euclNorm v = ‖toE v‖ := by
  simp [euclNorm, EuclideanSpace.norm_eq, toE]

lemma norm_le_euclNorm (v : Pt 2) : ‖v‖ ≤ euclNorm v := by
  refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

lemma euclNorm_le (v : Pt 2) : euclNorm v ≤ 2 * ‖v‖ := by
  unfold euclNorm; rw [Real.sqrt_le_left (by positivity)]
  simp only [Fin.sum_univ_two]
  have h0 := norm_le_pi_norm v 0
  have h1 := norm_le_pi_norm v 1
  rw [Real.norm_eq_abs] at h0 h1
  have := abs_nonneg (v 0); have := abs_nonneg (v 1)
  nlinarith [sq_abs (v 0), sq_abs (v 1)]

lemma euclNorm_nonneg (v : Pt 2) : 0 ≤ euclNorm v := Real.sqrt_nonneg _

lemma euclNorm_add_le (v w : Pt 2) : euclNorm (v + w) ≤ euclNorm v + euclNorm w := by
  simp only [euclNorm_eq, map_add]; exact norm_add_le _ _

lemma euclNorm_smul (t : ℝ) (v : Pt 2) : euclNorm (t • v) = |t| * euclNorm v := by
  simp only [euclNorm_eq, map_smul, norm_smul, Real.norm_eq_abs]

/-- The unit vector `(1,0)`. -/
lemma euclNorm_e0 : euclNorm (![1, 0] : Pt 2) = 1 := by simp [euclNorm]

lemma bddAbove_eucOp (A : Pt 2 →L[ℝ] Pt 2) :
    BddAbove (Set.range fun e : {e : Pt 2 // euclNorm e = 1} => euclNorm (A e.1)) := by
  refine ⟨2 * ‖A‖, ?_⟩
  rintro _ ⟨e, rfl⟩
  calc euclNorm (A e.1) ≤ 2 * ‖A e.1‖ := euclNorm_le _
    _ ≤ 2 * (‖A‖ * ‖e.1‖) := by gcongr; exact A.le_opNorm _
    _ ≤ 2 * (‖A‖ * 1) := by
        gcongr; exact (norm_le_euclNorm _).trans e.2.le
    _ = 2 * ‖A‖ := by ring

lemma le_eucOp (A : Pt 2 →L[ℝ] Pt 2) (e : Pt 2) (he : euclNorm e = 1) :
    euclNorm (A e) ≤ eucOp A :=
  le_ciSup (f := fun e : {e : Pt 2 // euclNorm e = 1} => euclNorm (A e.1)) (bddAbove_eucOp A) ⟨e, he⟩

lemma eucOp_le_of (A : Pt 2 →L[ℝ] Pt 2) (B : ℝ) (h : ∀ e : Pt 2, euclNorm e = 1 → euclNorm (A e) ≤ B) :
    eucOp A ≤ B := by
  haveI : Nonempty {e : Pt 2 // euclNorm e = 1} := ⟨⟨_, euclNorm_e0⟩⟩
  exact ciSup_le fun e => h e.1 e.2

lemma eucOp_nonneg (A : Pt 2 →L[ℝ] Pt 2) : 0 ≤ eucOp A :=
  (euclNorm_nonneg _).trans (le_eucOp A _ euclNorm_e0)

lemma eucOp_le_two_norm (A : Pt 2 →L[ℝ] Pt 2) : eucOp A ≤ 2 * ‖A‖ :=
  eucOp_le_of A _ fun e he => by
    calc euclNorm (A e) ≤ 2 * ‖A e‖ := euclNorm_le _
      _ ≤ 2 * (‖A‖ * ‖e‖) := by gcongr; exact A.le_opNorm _
      _ ≤ 2 * (‖A‖ * 1) := by gcongr; exact (norm_le_euclNorm _).trans he.le
      _ = 2 * ‖A‖ := by ring

lemma eucOp_add_le (A B : Pt 2 →L[ℝ] Pt 2) : eucOp (A + B) ≤ eucOp A + eucOp B :=
  eucOp_le_of _ _ fun e he => (euclNorm_add_le _ _).trans
    (add_le_add (le_eucOp A e he) (le_eucOp B e he))

lemma eucOp_smul_le (t : ℝ) (A : Pt 2 →L[ℝ] Pt 2) : eucOp (t • A) ≤ |t| * eucOp A :=
  eucOp_le_of _ _ fun e he => by
    rw [ContinuousLinearMap.smul_apply, euclNorm_smul]
    exact mul_le_mul_of_nonneg_left (le_eucOp A e he) (abs_nonneg _)

lemma continuous_eucOp : Continuous (eucOp : (Pt 2 →L[ℝ] Pt 2) → ℝ) := by
  refine (LipschitzWith.of_le_add_mul' 2 fun A B => ?_).continuous
  calc eucOp A = eucOp (B + (A - B)) := by rw [add_sub_cancel]
    _ ≤ eucOp B + eucOp (A - B) := eucOp_add_le _ _
    _ ≤ eucOp B + 2 * dist A B := by rw [dist_eq_norm]; gcongr; exact eucOp_le_two_norm _


/-- `v ↦ D(∑ vᵢ eᵢ)(x)` as a continuous linear map. -/
noncomputable def gradCLM (x : Pt 2) : (Fin 4 → ℝ) →L[ℝ] (Pt 2 →L[ℝ] Pt 2) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (fderiv ℝ (eBasis i) x)

lemma fderiv_eField (c : Fin 4 → ℝ) (x : Pt 2) : fderiv ℝ (eField c) x = gradCLM x c := by
  have h : HasFDerivAt (eField c) (∑ i, c i • fderiv ℝ (eBasis i) x) x := by
    rw [eField_eq_sum]
    exact HasFDerivAt.fun_sum fun i _ =>
      (((contDiff_eBasis i).differentiable (by simp)) x).hasFDerivAt.const_smul (c i)
  rw [h.fderiv]
  simp [gradCLM]

lemma continuous_gradCLM (v : Fin 4 → ℝ) : Continuous fun x => gradCLM x v := by
  simp only [gradCLM, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  exact continuous_finset_sum _ fun i _ =>
    ((contDiff_eBasis i).continuous_fderiv (by simp)).fun_const_smul (v i)

/-- The function whose supremum is `‖∇(∑ vᵢ eᵢ)‖_{L^∞, op}`. -/
noncomputable def gSum (v : Fin 4 → ℝ) (x : Pt 2) : ℝ≥0∞ := ENNReal.ofReal (eucOp (gradCLM x v))

lemma ofReal_eucOp_le (A : Pt 2 →L[ℝ] Pt 2) (B : ℝ≥0∞)
    (h : ∀ e : Pt 2, euclNorm e = 1 → ENNReal.ofReal (euclNorm (A e)) ≤ B) :
    ENNReal.ofReal (eucOp A) ≤ B := by
  rcases eq_or_ne B ⊤ with rfl | hB
  · exact le_top
  rw [← ENNReal.ofReal_toReal hB]
  refine ENNReal.ofReal_le_ofReal (eucOp_le_of A _ fun e he => ?_)
  exact (ENNReal.ofReal_le_iff_le_toReal hB).1 (h e he)

lemma gSum_smul_le (t : ℝ) (v : Fin 4 → ℝ) (x : Pt 2) : gSum (t • v) x ≤ ‖t‖ₑ * gSum v x := by
  simp only [gSum, map_smul]
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (eucOp_smul_le _ _)

lemma gSum_sub_le (v w : Fin 4 → ℝ) (x : Pt 2) : gSum (v - w) x ≤ gSum v x + gSum w x := by
  simp only [gSum, map_sub]
  rw [← ENNReal.ofReal_add (eucOp_nonneg _) (eucOp_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := eucOp_add_le (gradCLM x v) (-gradCLM x w)
  have h2 : eucOp (-gradCLM x w) ≤ eucOp (gradCLM x w) := by
    refine eucOp_le_of _ _ fun e he => ?_
    rw [ContinuousLinearMap.neg_apply, euclNorm_eq, map_neg, norm_neg, ← euclNorm_eq]
    exact le_eucOp _ e he
  rw [sub_eq_add_neg]; linarith

lemma iSup_gSum_smul_le (t : ℝ) (v : Fin 4 → ℝ) :
    (⨆ x, gSum (t • v) x) ≤ ‖t‖ₑ * ⨆ x, gSum v x := by
  rw [ENNReal.mul_iSup]; exact iSup_mono fun x => gSum_smul_le t v x

lemma iSup_gSum_sub_le (v w : Fin 4 → ℝ) :
    (⨆ x, gSum (v - w) x) ≤ (⨆ x, gSum v x) + ⨆ x, gSum w x :=
  iSup_le fun x => (gSum_sub_le v w x).trans (add_le_add (le_iSup _ x) (le_iSup _ x))

lemma continuous_gSum (v : Fin 4 → ℝ) : Continuous (gSum v) :=
  ENNReal.continuous_ofReal.comp (continuous_eucOp.comp (continuous_gradCLM v))

lemma continuous_gSum_comp {h : ℝ → Fin 4 → ℝ} (hh : Continuous h) (x : Pt 2) :
    Continuous fun r => gSum (h r) x :=
  ENNReal.continuous_ofReal.comp (continuous_eucOp.comp ((gradCLM x).continuous.comp hh))

lemma measurable_iSup_gSum {h : ℝ → Fin 4 → ℝ} (hh : Continuous h) :
    Measurable fun r => ⨆ x, gSum (h r) x := by
  simp_rw [iSup_eq_iSup_rat (continuous_gSum _)]
  exact Measurable.iSup fun q => (continuous_gSum_comp hh _).measurable

lemma iSup_gSum_integral_le {h : ℝ → Fin 4 → ℝ} (hh : Continuous h) {s : ℝ} (hs : 0 ≤ s) :
    (⨆ x, gSum (∫ r in (0 : ℝ)..s, h r) x) ≤ ∫⁻ r in Ioc 0 s, ⨆ x, gSum (h r) x := by
  refine iSup_le fun x => ofReal_eucOp_le _ _ fun e he => ?_
  have hint : IntegrableOn h (Ioc 0 s) := (hh.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  set Φ : (Fin 4 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (toE.comp (ContinuousLinearMap.apply ℝ (Pt 2) e)).comp (gradCLM x)
  have hΦ : ∀ v, Φ v = toE (gradCLM x v e) := fun v => rfl
  calc ENNReal.ofReal (euclNorm (gradCLM x (∫ r in (0 : ℝ)..s, h r) e))
      = ‖∫ r in Ioc 0 s, Φ (h r)‖ₑ := by
        rw [euclNorm_eq, ← hΦ, intervalIntegral.integral_of_le hs,
          ← ContinuousLinearMap.integral_comp_comm _ hint, ofReal_norm_eq_enorm]
    _ ≤ ∫⁻ r in Ioc 0 s, ‖Φ (h r)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r in Ioc 0 s, ⨆ x, gSum (h r) x := by
        refine lintegral_mono fun r => ?_
        rw [hΦ, ← ofReal_norm_eq_enorm, ← euclNorm_eq]
        exact (ENNReal.ofReal_le_ofReal (le_eucOp _ e he)).trans (le_iSup (gSum (h r)) x)


/-! ### The exponential kernel and a Taylor bound -/

/-- The exponential kernel `μ e^{-μ t}`. -/
noncomputable def expKer (μ t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (μ * Real.exp (-(μ * t)))

lemma expKer_eq_pdf {μ t : ℝ} (ht : 0 ≤ t) : expKer μ t = exponentialPDF μ t := by
  rw [exponentialPDF_of_nonneg ht, expKer]

lemma lintegral_expKer_left {μ : ℝ} (hμ : 0 ≤ μ) (s : ℝ) :
    ∫⁻ r in Ioc 0 s, expKer μ (s - r) ≤ 1 := by
  rcases hμ.eq_or_lt with rfl | hμ
  · simp [expKer]
  calc ∫⁻ r in Ioc 0 s, expKer μ (s - r) = ∫⁻ r in Ioc 0 s, exponentialPDF μ (s - r) :=
        setLIntegral_congr_fun measurableSet_Ioc fun r hr => expKer_eq_pdf (by linarith [hr.2])
    _ ≤ ∫⁻ r, exponentialPDF μ (s - r) := setLIntegral_le_lintegral _ _
    _ = 1 := by rw [lintegral_sub_left_eq_self (fun r => exponentialPDF μ r) s,
        lintegral_exponentialPDF_eq_one hμ]

lemma lintegral_expKer_right {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ) :
    ∫⁻ s, (if r ≤ s then expKer μ (s - r) else 0) ≤ 1 := by
  rcases hμ.eq_or_lt with rfl | hμ
  · simp [expKer]
  have : (fun s => if r ≤ s then expKer μ (s - r) else 0) = fun s => exponentialPDF μ (s - r) := by
    funext s
    split_ifs with h
    · exact expKer_eq_pdf (by linarith)
    · exact (exponentialPDF_of_neg (by linarith)).symm
  rw [this, lintegral_sub_right_eq_self (fun s => exponentialPDF μ s) r,
    lintegral_exponentialPDF_eq_one hμ]

lemma measurable_expKer (μ : ℝ) : Measurable (expKer μ) := by
  unfold expKer; fun_prop

lemma tonelli_expKer {μ : ℝ} (hμ : 0 ≤ μ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s in Icc 0 1, ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F r ≤ ∫⁻ r in Icc 0 1, F r := by
  set G : ℝ → ℝ → ℝ≥0∞ := fun s r =>
    (Icc (0 : ℝ) 1).indicator F r * (if r ≤ s then expKer μ (s - r) else 0)
  have hG : Measurable (Function.uncurry G) := by
    refine ((hF.indicator measurableSet_Icc).comp measurable_snd).mul ?_
    refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ measurable_const
    exact (measurable_expKer μ).comp (measurable_fst.sub measurable_snd)
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F r ≤ ∫⁻ r, G s r := by
    intro s hs
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_mono fun r => ?_
    by_cases hr : r ∈ Ioc 0 s
    · have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.trans hs.2⟩
      simp [G, indicator_of_mem hr, indicator_of_mem hr1, hr.2, mul_comm]
    · simp [indicator_of_notMem hr]
  calc ∫⁻ s in Icc 0 1, ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F r
      ≤ ∫⁻ s in Icc 0 1, ∫⁻ r, G s r := setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ ∫⁻ s, ∫⁻ r, G s r := setLIntegral_le_lintegral _ _
    _ = ∫⁻ r, ∫⁻ s, G s r := lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ r, (Icc (0 : ℝ) 1).indicator F r * ∫⁻ s, (if r ≤ s then expKer μ (s - r) else 0) := by
        refine lintegral_congr fun r => ?_
        rw [← lintegral_const_mul]
        refine Measurable.ite (measurableSet_Ici) ?_ measurable_const
        exact (measurable_expKer μ).comp (measurable_id.sub measurable_const)
    _ ≤ ∫⁻ r, (Icc (0 : ℝ) 1).indicator F r * 1 :=
        lintegral_mono fun r => by gcongr; exact lintegral_expKer_right hμ r
    _ = ∫⁻ r in Icc 0 1, F r := by rw [← lintegral_indicator measurableSet_Icc]; simp

lemma exp_sub_taylor_le (x : ℝ) (hx : 0 ≤ x) (M : ℕ) :
    0 ≤ Real.exp x - ∑ j ∈ Finset.range M, x ^ j / j.factorial ∧
      Real.exp x - ∑ j ∈ Finset.range M, x ^ j / j.factorial ≤
        x ^ M / M.factorial * Real.exp x := by
  have hexp : Real.exp x = ∑' n : ℕ, x ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hs := Real.summable_pow_div_factorial x
  have htail : Real.exp x - ∑ j ∈ Finset.range M, x ^ j / j.factorial =
      ∑' k : ℕ, x ^ (k + M) / (k + M).factorial := by
    rw [hexp, ← hs.sum_add_tsum_nat_add M]; ring
  rw [htail]
  refine ⟨tsum_nonneg fun k => by positivity, ?_⟩
  rw [hexp, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff M).2 hs) (hs.mul_left _)
  have hd : M.factorial * k.factorial ≤ (k + M).factorial := by
    rw [add_comm]
    exact Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add M k)
  have hd' : (M.factorial : ℝ) * k.factorial ≤ (k + M).factorial := by exact_mod_cast hd
  have h1 : (0 : ℝ) < M.factorial := by positivity
  have h2 : (0 : ℝ) < k.factorial := by positivity
  rw [pow_add, div_le_iff₀ (by positivity)]
  calc x ^ k * x ^ M
      = x ^ M / M.factorial * (x ^ k / k.factorial) * (M.factorial * k.factorial) := by
        field_simp
    _ ≤ x ^ M / M.factorial * (x ^ k / k.factorial) * (k + M).factorial := by gcongr


/-! ### The damped response -/

/-- Evaluation of `∑ vᵢ eᵢ` at a point, as a continuous linear map of `v`. -/
noncomputable def eFieldCLM (y : Pt 2) : (Fin 4 → ℝ) →L[ℝ] Pt 2 :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (eBasis i y)

lemma eFieldCLM_apply (y : Pt 2) (v : Fin 4 → ℝ) : eFieldCLM y v = eField v y := by
  simp [eFieldCLM, eField]

variable {L M : ℕ} {S : ℕ → ℝ}

lemma ControlFamily.contDiff_coef (cf : ControlFamily L M S) (w : Fin L → Bool × Pt 2) :
    ContDiff ℝ ∞ (cf.coef w) := by
  have h := (cf.smooth fun i => (w i).1).comp
    ((contDiff_const (c := fun i => (w i).2)).prodMk contDiff_id)
  simpa [Function.comp_def] using h

lemma ControlFamily.coef_zero (cf : ControlFamily L M S) (w : Fin L → Bool × Pt 2) :
    cf.coef w 0 = 0 :=
  cf.support w 0 fun h => absurd h.1 (not_le.2 cf.ha₀)

lemma ControlFamily.coef_one (cf : ControlFamily L M S) (w : Fin L → Bool × Pt 2) :
    cf.coef w 1 = 0 :=
  cf.support w 1 fun h => absurd h.2 (not_le.2 cf.hb₀)

/-- The coefficient vector of the damped response `B_{μ,ω}(s)`. -/
noncomputable def dampedCoef (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ) :
    Fin 4 → ℝ :=
  cf.coef w.1 s - μ • ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r

lemma dampedB_eq (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ) :
    dampedB cf μ w s = fun x => eField (dampedCoef cf μ w s) (x - w.2) := by
  funext x
  have hc := (cf.contDiff_coef w.1).continuous
  have hint : IntervalIntegrable (fun r => Real.exp (-μ * (s - r)) • cf.coef w.1 r) volume 0 s :=
    (by fun_prop : Continuous fun r => Real.exp (-μ * (s - r)) • cf.coef w.1 r).intervalIntegrable _ _
  simp only [dampedB, bField, dampedCoef, ← eFieldCLM_apply, map_sub, map_smul]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  simp only [map_smul]

lemma bField_eq (cf : ControlFamily L M S) (w : BlockParam L) (s : ℝ) :
    bField cf w s = fun x => eField (cf.coef w.1 s) (x - w.2) := rfl

lemma hasDerivAt_dampedCoef (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ) :
    HasDerivAt (dampedCoef cf μ w) (deriv (cf.coef w.1) s - μ • dampedCoef cf μ w s) s := by
  have hcd := cf.contDiff_coef w.1
  have hc := hcd.continuous
  set I : ℝ → Fin 4 → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.exp (μ * r) • cf.coef w.1 r
  have hI : HasDerivAt I (Real.exp (μ * s) • cf.coef w.1 s) s :=
    intervalIntegral.integral_hasDerivAt_right
      ((by fun_prop : Continuous fun r => Real.exp (μ * r) • cf.coef w.1 r).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun r => Real.exp (μ * r) • cf.coef w.1 r).stronglyMeasurableAtFilter _ _)
      (by fun_prop : Continuous fun r => Real.exp (μ * r) • cf.coef w.1 r).continuousAt
  have hJ : ∀ s, (∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r) =
      Real.exp (-μ * s) • I s := by
    intro s
    rw [← intervalIntegral.integral_smul]
    congr 1; funext r
    rw [smul_smul, ← Real.exp_add]; congr 2; ring
  have hE : HasDerivAt (fun s => Real.exp (-μ * s)) (-μ * Real.exp (-μ * s)) s := by
    have := ((hasDerivAt_id s).const_mul (-μ)).exp
    simpa [mul_comm] using this
  have hdc : HasDerivAt (cf.coef w.1) (deriv (cf.coef w.1) s) s :=
    ((hcd.differentiable (by simp)) s).hasDerivAt
  have hD : HasDerivAt (dampedCoef cf μ w)
      (deriv (cf.coef w.1) s - μ • (Real.exp (-μ * s) • Real.exp (μ * s) • cf.coef w.1 s +
        (-μ * Real.exp (-μ * s)) • I s)) s := by
    have := hdc.sub ((hE.smul hI).const_smul μ)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [dampedCoef, hJ]; rfl
  convert hD using 1
  simp only [dampedCoef, hJ, smul_smul, ← Real.exp_add]
  have : -μ * s + μ * s = 0 := by ring
  rw [this, Real.exp_zero, one_smul]
  module

lemma ofReal_add_self (K : ℝ) : ENNReal.ofReal K + ENNReal.ofReal K = ENNReal.ofReal (2 * K) := by
  rcases le_or_gt 0 K with h | h
  · rw [two_mul, ENNReal.ofReal_add h h]
  · rw [ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_of_nonpos (by linarith)]; simp

lemma expKer_le {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) : expKer μ t ≤ ENNReal.ofReal μ := by
  refine ENNReal.ofReal_le_ofReal ?_
  have : Real.exp (-(μ * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  nlinarith [Real.exp_pos (-(μ * t))]

section Generic

variable (F : (Fin 4 → ℝ) → ℝ≥0∞) (hsmul : ∀ (t : ℝ) v, F (t • v) ≤ ‖t‖ₑ * F v)
  (hsub : ∀ v w, F (v - w) ≤ F v + F w)
  (hJ : ∀ h : ℝ → Fin 4 → ℝ, Continuous h → ∀ s : ℝ, 0 ≤ s →
    F (∫ r in (0 : ℝ)..s, h r) ≤ ∫⁻ r in Ioc 0 s, F (h r))
include hsmul hJ

lemma damped_integral_le {c : ℝ → Fin 4 → ℝ} (hc : Continuous c) {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ)
    (ht : ‖t‖ₑ = ENNReal.ofReal μ) {s : ℝ} (hs : 0 ≤ s) :
    F (t • ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • c r) ≤
      ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (c r) := by
  calc F (t • ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • c r)
      ≤ ‖t‖ₑ * F (∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • c r) := hsmul _ _
    _ ≤ ‖t‖ₑ * ∫⁻ r in Ioc 0 s, F (Real.exp (-μ * (s - r)) • c r) := by
        gcongr; exact hJ _ (by fun_prop) s hs
    _ ≤ ‖t‖ₑ * ∫⁻ r in Ioc 0 s, ‖Real.exp (-μ * (s - r))‖ₑ * F (c r) := by
        gcongr with r; exact hsmul _ _
    _ = ∫⁻ r in Ioc 0 s, ‖t‖ₑ * (‖Real.exp (-μ * (s - r))‖ₑ * F (c r)) :=
        (lintegral_const_mul' _ _ (by rw [ht]; exact ENNReal.ofReal_ne_top)).symm
    _ = ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (c r) := by
        refine lintegral_congr fun r => ?_
        rw [← mul_assoc, ht, Real.enorm_eq_ofReal (Real.exp_pos _).le, ← ENNReal.ofReal_mul hμ,
          expKer, neg_mul]

include hsub

variable {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L)
include hμ

lemma dampedCoef_le {s : ℝ} (hs : 0 ≤ s) :
    F (dampedCoef cf μ w s) ≤ F (cf.coef w.1 s) +
      ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (cf.coef w.1 r) :=
  (hsub _ _).trans (add_le_add le_rfl (damped_integral_le F hsmul hJ
    (cf.contDiff_coef w.1).continuous hμ μ (Real.enorm_eq_ofReal hμ) hs))

omit hsub in
lemma dampedCoef_sub_le {s : ℝ} (hs : 0 ≤ s) :
    F (dampedCoef cf μ w s - cf.coef w.1 s) ≤
      ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (cf.coef w.1 r) := by
  have e : dampedCoef cf μ w s - cf.coef w.1 s =
      (-μ) • ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r := by
    simp [dampedCoef, neg_smul]
  rw [e]
  exact damped_integral_le F hsmul hJ (cf.contDiff_coef w.1).continuous hμ (-μ)
    (by rw [enorm_neg, Real.enorm_eq_ofReal hμ]) hs

lemma damped_bound_int (hmeas : Measurable fun r => F (cf.coef w.1 r)) {K : ℝ}
    (hK : ∫⁻ s in Icc 0 1, F (cf.coef w.1 s) ≤ ENNReal.ofReal K) :
    ∫⁻ s in Icc 0 1, F (dampedCoef cf μ w s) ≤ ENNReal.ofReal (2 * K) := by
  calc ∫⁻ s in Icc 0 1, F (dampedCoef cf μ w s)
      ≤ ∫⁻ s in Icc 0 1, (F (cf.coef w.1 s) +
          ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (cf.coef w.1 r)) :=
        setLIntegral_mono' measurableSet_Icc fun s hs =>
          dampedCoef_le F hsmul hsub hJ cf hμ w hs.1
    _ = (∫⁻ s in Icc 0 1, F (cf.coef w.1 s)) +
          ∫⁻ s in Icc 0 1, ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (cf.coef w.1 r) :=
        lintegral_add_left hmeas _
    _ ≤ ENNReal.ofReal K + ENNReal.ofReal K :=
        add_le_add hK ((tonelli_expKer hμ _ hmeas).trans hK)
    _ = ENNReal.ofReal (2 * K) := ofReal_add_self K

omit hsub in
lemma damped_bound_sub (hmeas : Measurable fun r => F (cf.coef w.1 r)) {K : ℝ}
    (hK : ∫⁻ s in Icc 0 1, F (cf.coef w.1 s) ≤ ENNReal.ofReal K) :
    ∫⁻ s in Icc 0 1, F (dampedCoef cf μ w s - cf.coef w.1 s) ≤ ENNReal.ofReal (μ * K) := by
  calc ∫⁻ s in Icc 0 1, F (dampedCoef cf μ w s - cf.coef w.1 s)
      ≤ ∫⁻ (s : ℝ) in Icc (0 : ℝ) 1, ENNReal.ofReal μ * ENNReal.ofReal K := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        refine (dampedCoef_sub_le F hsmul hJ cf hμ w hs.1).trans ?_
        calc ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (cf.coef w.1 r)
            ≤ ∫⁻ r in Ioc 0 s, ENNReal.ofReal μ * F (cf.coef w.1 r) :=
              setLIntegral_mono' measurableSet_Ioc fun r hr =>
                by gcongr; exact expKer_le hμ (by linarith [hr.2])
          _ = ENNReal.ofReal μ * ∫⁻ r in Ioc 0 s, F (cf.coef w.1 r) := lintegral_const_mul _ hmeas
          _ ≤ ENNReal.ofReal μ * ∫⁻ r in Icc 0 1, F (cf.coef w.1 r) := by
              gcongr ENNReal.ofReal μ * ?_
              exact lintegral_mono_set (fun r (hr : r ∈ Ioc (0 : ℝ) s) =>
                (⟨hr.1.le, hr.2.trans hs.2⟩ : r ∈ Icc (0 : ℝ) 1))
          _ ≤ ENNReal.ofReal μ * ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (μ * K) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
          ENNReal.ofReal_mul hμ]

lemma damped_bound_sup :
    (⨆ s ∈ Icc (0 : ℝ) 1, F (dampedCoef cf μ w s)) ≤ 2 * ⨆ s ∈ Icc (0 : ℝ) 1, F (cf.coef w.1 s) := by
  set B := ⨆ s ∈ Icc (0 : ℝ) 1, F (cf.coef w.1 s)
  refine iSup₂_le fun s hs => ?_
  have hB : ∀ r ∈ Icc (0 : ℝ) 1, F (cf.coef w.1 r) ≤ B := fun r hr =>
    le_iSup₂ (f := fun r (_ : r ∈ Icc (0 : ℝ) 1) => F (cf.coef w.1 r)) r hr
  calc F (dampedCoef cf μ w s)
      ≤ F (cf.coef w.1 s) + ∫⁻ r in Ioc 0 s, expKer μ (s - r) * F (cf.coef w.1 r) :=
        dampedCoef_le F hsmul hsub hJ cf hμ w hs.1
    _ ≤ B + ∫⁻ r in Ioc 0 s, expKer μ (s - r) * B :=
        add_le_add (hB s hs) (setLIntegral_mono' measurableSet_Ioc fun r hr => by
          gcongr; exact hB r ⟨hr.1.le, hr.2.trans hs.2⟩)
    _ = B + (∫⁻ r in Ioc 0 s, expKer μ (s - r)) * B := by
        rw [lintegral_mul_const (f := fun r => expKer μ (s - r)) _
          (by exact (measurable_expKer μ).comp (measurable_const.sub measurable_id))]
    _ ≤ B + 1 * B := by gcongr; exact lintegral_expKer_left hμ s
    _ = 2 * B := by rw [one_mul, two_mul]

omit hsub in
lemma damped_bound_terminal {K : ℝ}
    (hK : ∫⁻ s in Icc 0 1, F (cf.coef w.1 s) ≤ ENNReal.ofReal K) :
    F (dampedCoef cf μ w 1) ≤ ENNReal.ofReal (K / (M.factorial : ℝ) * μ ^ (M + 1)) := by
  set c := cf.coef w.1 with hc_def
  have hc : Continuous c := (cf.contDiff_coef w.1).continuous
  set a : ℕ → ℝ := fun j => Real.exp (-μ) * μ ^ j / j.factorial
  set P : ℝ → ℝ := fun r => ∑ j ∈ Finset.range M, a j * r ^ j
  set R : ℝ → ℝ := fun r => Real.exp (-μ * (1 - r)) - P r
  have hPc : Continuous P := by fun_prop
  have hPint : ∫ r in (0 : ℝ)..1, P r • c r = 0 := by
    have : (fun r => P r • c r) = fun r => ∑ j ∈ Finset.range M, a j • (r ^ j • c r) := by
      funext r; simp only [P, Finset.sum_smul, mul_smul]
    rw [this, intervalIntegral.integral_finset_sum (fun j _ =>
      (by fun_prop : Continuous fun r => a j • (r ^ j • c r)).intervalIntegrable _ _)]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [intervalIntegral.integral_smul, cf.moments w.1 j (Finset.mem_range.1 hj), smul_zero]
  have hRint : ∫ r in (0 : ℝ)..1, Real.exp (-μ * (1 - r)) • c r = ∫ r in (0 : ℝ)..1, R r • c r := by
    have : (fun r => R r • c r) = fun r => Real.exp (-μ * (1 - r)) • c r - P r • c r := by
      funext r; simp only [R, sub_smul]
    rw [this, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun r => Real.exp (-μ * (1 - r)) • c r).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun r => P r • c r).intervalIntegrable _ _), hPint, sub_zero]
  have hD : dampedCoef cf μ w 1 = (-μ) • ∫ r in (0 : ℝ)..1, R r • c r := by
    simp only [dampedCoef, ← hc_def, cf.coef_one w.1, hRint, zero_sub, neg_smul]
  have hR : ∀ r ∈ Ioc (0 : ℝ) 1, ‖R r‖ₑ ≤ ENNReal.ofReal (μ ^ M / M.factorial) := by
    intro r hr
    have hx : 0 ≤ μ * r := mul_nonneg hμ hr.1.le
    obtain ⟨h0, h1⟩ := exp_sub_taylor_le (μ * r) hx M
    have hRe : R r = Real.exp (-μ) * (Real.exp (μ * r) -
        ∑ j ∈ Finset.range M, (μ * r) ^ j / j.factorial) := by
      simp only [R, P, a, mul_sub, Finset.mul_sum, ← Real.exp_add]
      congr 1
      · congr 1; ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow]; ring
    have hRnn : 0 ≤ R r := by rw [hRe]; exact mul_nonneg (Real.exp_pos _).le h0
    have hRle : R r ≤ μ ^ M / M.factorial := by
      rw [hRe]
      have hf : (0 : ℝ) < M.factorial := by positivity
      have hexp : Real.exp (-μ) * Real.exp (μ * r) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]; nlinarith [hr.2]
      have hpow : (μ * r) ^ M ≤ μ ^ M := by
        rw [mul_pow]
        exact mul_le_of_le_one_right (pow_nonneg hμ _) (pow_le_one₀ hr.1.le hr.2)
      calc Real.exp (-μ) * (Real.exp (μ * r) - ∑ j ∈ Finset.range M, (μ * r) ^ j / j.factorial)
          ≤ Real.exp (-μ) * ((μ * r) ^ M / M.factorial * Real.exp (μ * r)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = (μ * r) ^ M / M.factorial * (Real.exp (-μ) * Real.exp (μ * r)) := by ring
        _ ≤ (μ * r) ^ M / M.factorial * 1 := by
            gcongr
        _ ≤ μ ^ M / M.factorial := by rw [mul_one]; gcongr
    rw [Real.enorm_eq_ofReal hRnn]
    exact ENNReal.ofReal_le_ofReal hRle
  calc F (dampedCoef cf μ w 1)
      ≤ ‖-μ‖ₑ * F (∫ r in (0 : ℝ)..1, R r • c r) := by rw [hD]; exact hsmul _ _
    _ ≤ ENNReal.ofReal μ * ∫⁻ r in Ioc 0 1, F (R r • c r) := by
        rw [enorm_neg, Real.enorm_eq_ofReal hμ]
        gcongr
        exact hJ _ (by fun_prop) 1 zero_le_one
    _ ≤ ENNReal.ofReal μ * ∫⁻ r in Ioc 0 1, ENNReal.ofReal (μ ^ M / M.factorial) * F (c r) := by
        gcongr ENNReal.ofReal μ * ?_
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
        exact (hsmul _ _).trans (by gcongr; exact hR r hr)
    _ = ENNReal.ofReal μ * (ENNReal.ofReal (μ ^ M / M.factorial) * ∫⁻ r in Ioc 0 1, F (c r)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal μ * (ENNReal.ofReal (μ ^ M / M.factorial) * ENNReal.ofReal K) := by
        gcongr
        exact (lintegral_mono_set Ioc_subset_Icc_self).trans hK
    _ = ENNReal.ofReal (K / (M.factorial : ℝ) * μ ^ (M + 1)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hμ, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [pow_succ]; ring

end Generic

/-- **Lemma 2.16** (damped response).  `∂ₛB + μB = ∂ₛb`, `B(0) = 0`, and the estimates
`∫₀¹‖B‖_{C^a} ≤ 2S_a`, `‖B‖_{L^∞C^a} ≤ 2‖b‖_{L^∞C^a}`, `∫₀¹‖B - b‖_{C^a} ≤ μ S_a`,
`‖B(1)‖_{C^a} ≤ S_a μ^{M+1}/M!` (and the analogue `∫₀¹‖∇B‖_{L^∞,op} ≤ 2 S_1`). -/
theorem damped_response {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) (μ : ℝ) (hμ : 0 ≤ μ)
    (w : BlockParam L) :
    (∀ s x, HasDerivAt (fun s => dampedB cf μ w s x)
      (bDot cf w s x - μ • dampedB cf μ w s x) s) ∧
    dampedB cf μ w 0 = 0 ∧
    (∀ a : ℕ,
      (∫⁻ s in Icc 0 1, cNormE a (dampedB cf μ w s)) ≤ ENNReal.ofReal (2 * S a) ∧
      (⨆ s ∈ Icc (0 : ℝ) 1, cNormE a (dampedB cf μ w s)) ≤
        2 * ⨆ s ∈ Icc (0 : ℝ) 1, cNormE a (bField cf w s) ∧
      (∫⁻ s in Icc 0 1, cNormE a (dampedB cf μ w s - bField cf w s)) ≤
        ENNReal.ofReal (μ * S a) ∧
      cNormE a (dampedB cf μ w 1) ≤ ENNReal.ofReal (S a / (M.factorial : ℝ) * μ ^ (M + 1))) ∧
    (∫⁻ s in Icc 0 1, ⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (dampedB cf μ w s) x))) ≤
      ENNReal.ofReal (2 * S 1) := by
  have hc := (cf.contDiff_coef w.1).continuous
  have hNs : ∀ a (t : ℝ) v, (⨆ x, cSum a (t • v) x) ≤ ‖t‖ₑ * ⨆ x, cSum a v x :=
    fun a t v => (iSup_cSum_smul a t v).le
  have hNJ : ∀ a (h : ℝ → Fin 4 → ℝ), Continuous h → ∀ s : ℝ, 0 ≤ s →
      (⨆ x, cSum a (∫ r in (0 : ℝ)..s, h r) x) ≤ ∫⁻ r in Ioc 0 s, ⨆ x, cSum a (h r) x :=
    fun a h hh s hs => iSup_cSum_integral_le a hh hs
  have hGJ : ∀ (h : ℝ → Fin 4 → ℝ), Continuous h → ∀ s : ℝ, 0 ≤ s →
      (⨆ x, gSum (∫ r in (0 : ℝ)..s, h r) x) ≤ ∫⁻ r in Ioc 0 s, ⨆ x, gSum (h r) x :=
    fun h hh s hs => iSup_gSum_integral_le hh hs
  have eD : ∀ a s, cNormE a (dampedB cf μ w s) = ⨆ x, cSum a (dampedCoef cf μ w s) x := by
    intro a s; rw [dampedB_eq, cNormE_eField_sub, cNormE_eField]
  have eb : ∀ a s, cNormE a (bField cf w s) = ⨆ x, cSum a (cf.coef w.1 s) x := by
    intro a s; rw [bField_eq, cNormE_eField_sub, cNormE_eField]
  have eDb : ∀ a s, cNormE a (dampedB cf μ w s - bField cf w s) =
      ⨆ x, cSum a (dampedCoef cf μ w s - cf.coef w.1 s) x := by
    intro a s
    have : dampedB cf μ w s - bField cf w s =
        fun x => eField (dampedCoef cf μ w s - cf.coef w.1 s) (x - w.2) := by
      funext x
      simp only [Pi.sub_apply, dampedB_eq, bField_eq, ← eFieldCLM_apply, map_sub]
    rw [this, cNormE_eField_sub, cNormE_eField]
  have eG : ∀ s, (⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (dampedB cf μ w s) x))) =
      ⨆ x, gSum (dampedCoef cf μ w s) x := by
    intro s
    rw [dampedB_eq]
    simp_rw [fderiv_comp_sub, fderiv_eField]
    exact (Equiv.subRight w.2).iSup_comp (g := fun y => gSum (dampedCoef cf μ w s) y)
  have hKa : ∀ a, ∫⁻ s in Icc 0 1, (⨆ x, cSum a (cf.coef w.1 s) x) ≤ ENNReal.ofReal (S a) := by
    intro a; simpa only [cNormE_eField] using cf.bound a w.1
  have hK1 : ∫⁻ s in Icc 0 1, (⨆ x, gSum (cf.coef w.1 s) x) ≤ ENNReal.ofReal (S 1) := by
    simpa only [fderiv_eField, gSum] using cf.bound_grad w.1
  refine ⟨?_, ?_, fun a => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro s x
    have := (eFieldCLM (x - w.2)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_dampedCoef cf μ w s)
    convert this using 1
    · funext s; simp [dampedB_eq, eFieldCLM_apply]
    · simp only [bDot, dampedB_eq, ← eFieldCLM_apply, map_sub, map_smul]
  · rw [dampedB_eq]; funext x
    simp [dampedCoef, cf.coef_zero, eField]
  · simp only [eD]
    exact damped_bound_int (fun v => ⨆ x, cSum a v x)
      (hNs a) (iSup_cSum_sub_le a) (hNJ a) cf hμ w
      (measurable_iSup_cSum a hc) (hKa a)
  · simp only [eD, eb]
    exact damped_bound_sup (fun v => ⨆ x, cSum a v x)
      (hNs a) (iSup_cSum_sub_le a) (hNJ a) cf hμ w
  · simp only [eDb]
    exact damped_bound_sub (fun v => ⨆ x, cSum a v x)
      (hNs a) (hNJ a) cf hμ w (measurable_iSup_cSum a hc) (hKa a)
  · rw [eD]
    exact damped_bound_terminal (fun v => ⨆ x, cSum a v x)
      (hNs a) (hNJ a) cf hμ w (hKa a)
  · simp only [eG]
    exact damped_bound_int (fun v => ⨆ x, gSum v x)
      iSup_gSum_smul_le iSup_gSum_sub_le hGJ cf hμ w
      (measurable_iSup_gSum hc) hK1

end AnomDiss
