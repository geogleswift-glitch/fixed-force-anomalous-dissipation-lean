module

public import RequestProject.ControlsExist
public import RequestProject.TorusCalc

/-!
# Lemma 2.13: construction of the controls

Explicit construction of the controls of Lemma 2.13: uniform bounds for the eigenfields,
smooth time profiles, moment corrections and the assembly of the control family.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-! ### Uniform bounds for the eigenfields -/

lemma periodic_bound {E : Type*} [NormedAddCommGroup E] (f : Pt 2 → E) (hf : Continuous f)
    (hp : IsPeriodic f) : ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Pt 2)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  obtain ⟨y, hy, n, rfl⟩ := exists_cell_rep x
  rw [hp y n]
  exact (hC y hy).trans (le_max_left _ _)

lemma isPeriodic_eBasis (i : Fin 4) : IsPeriodic (eBasis i) := by
  rw [eBasis_eq_eField]; exact (eigenspace_properties _).2.1

lemma isPeriodic_iteratedFDeriv_eBasis (k : ℕ) (i : Fin 4) :
    IsPeriodic (iteratedFDeriv ℝ k (eBasis i)) := by
  intro x n
  have h : (fun y => eBasis i (y + intVec n)) = eBasis i := funext fun y => isPeriodic_eBasis i y n
  rw [← iteratedFDeriv_comp_add_right, h]

lemma exists_bound_iteratedFDeriv_eBasis (k : ℕ) (i : Fin 4) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k (eBasis i) x‖ ≤ C :=
  periodic_bound _ ((contDiff_eBasis i).continuous_iteratedFDeriv (by exact_mod_cast le_top))
    (isPeriodic_iteratedFDeriv_eBasis k i)

/-- A uniform bound for `D^k eᵢ`. -/
def eBound (k : ℕ) (i : Fin 4) : ℝ := Classical.choose (exists_bound_iteratedFDeriv_eBasis k i)

lemma eBound_nonneg (k : ℕ) (i : Fin 4) : 0 ≤ eBound k i :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_eBasis k i)).1

lemma norm_iteratedFDeriv_eBasis_le (k : ℕ) (i : Fin 4) (x : Pt 2) :
    ‖iteratedFDeriv ℝ k (eBasis i) x‖ ≤ eBound k i :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_eBasis k i)).2 x

/-- The constant `∑_{k ≤ a} ∑ᵢ sup |D^k eᵢ|`. -/
def aConst (a : ℕ) : ℝ := ∑ k ∈ Finset.range (a + 1), ∑ i, eBound k i

lemma aConst_nonneg (a : ℕ) : 0 ≤ aConst a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => eBound_nonneg _ _

lemma iterCLM_apply (k : ℕ) (x : Pt 2) (v : Fin 4 → ℝ) :
    iterCLM k x v = ∑ i, v i • iteratedFDeriv ℝ k (eBasis i) x := by
  simp [iterCLM]

lemma norm_iterCLM_le (k : ℕ) (x : Pt 2) (v : Fin 4 → ℝ) :
    ‖iterCLM k x v‖ ≤ (∑ i, eBound k i) * ‖v‖ := by
  rw [iterCLM_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul (norm_iteratedFDeriv_eBasis_le k i x) (norm_le_pi_norm v i) (norm_nonneg _)
    (eBound_nonneg _ _)

lemma cSum_le (a : ℕ) (v : Fin 4 → ℝ) (x : Pt 2) :
    cSum a v x ≤ ENNReal.ofReal (aConst a * ‖v‖) := by
  unfold cSum aConst
  rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg (Finset.sum_nonneg fun _ _ => eBound_nonneg _ _) (norm_nonneg _)]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (norm_iterCLM_le k x v)

lemma gradCLM_apply (x : Pt 2) (v : Fin 4 → ℝ) :
    gradCLM x v = ∑ i, v i • fderiv ℝ (eBasis i) x := by
  simp [gradCLM]

lemma gSum_le (v : Fin 4 → ℝ) (x : Pt 2) :
    gSum v x ≤ ENNReal.ofReal (2 * aConst 1 * ‖v‖) := by
  unfold gSum
  refine ENNReal.ofReal_le_ofReal ((eucOp_le_two_norm _).trans ?_)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [gradCLM_apply]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ i, eBound 1 i ≤ aConst 1 := by
    unfold aConst
    exact Finset.single_le_sum (f := fun k => ∑ i, eBound k i)
      (fun _ _ => Finset.sum_nonneg fun _ _ => eBound_nonneg _ _) (by simp)
  calc ∑ i, ‖v i • fderiv ℝ (eBasis i) x‖ ≤ ∑ i, eBound 1 i * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, mul_comm, ← norm_iteratedFDeriv_one]
        exact mul_le_mul (norm_iteratedFDeriv_eBasis_le 1 i x) (norm_le_pi_norm v i)
          (norm_nonneg _) (eBound_nonneg _ _)
    _ = (∑ i, eBound 1 i) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ aConst 1 * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)


/-! ### Smooth time profiles -/

/-- The bump function underlying all time profiles. -/
def baseBump : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A smooth nonnegative profile with unit integral, supported in `[-1/4, 1/4]`. -/
def rho0 : ℝ → ℝ := baseBump.normed volume

lemma contDiff_rho0 : ContDiff ℝ ∞ rho0 := baseBump.contDiff_normed (n := ⊤)

lemma rho0_nonneg (s : ℝ) : 0 ≤ rho0 s := baseBump.nonneg_normed s

lemma integral_rho0 : ∫ s, rho0 s = 1 := baseBump.integral_normed

lemma support_rho0 : Function.support rho0 = Ioo (-(1 / 4)) (1 / 4) := by
  rw [rho0, baseBump.support_normed_eq, Real.ball_eq_Ioo]
  simp [baseBump]

lemma rho0_eq_zero {s : ℝ} (hs : s ∉ Ioo (-(1 / 4) : ℝ) (1 / 4)) : rho0 s = 0 := by
  rw [← support_rho0] at hs; simpa using hs

lemma rho0_pos {s : ℝ} (hs : s ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) : 0 < rho0 s := by
  rw [← support_rho0] at hs
  exact lt_of_le_of_ne (rho0_nonneg s) (Ne.symm hs)

lemma tsupport_rho0 : tsupport rho0 ⊆ Icc (-(1 / 4)) (1 / 4) := by
  rw [tsupport, support_rho0, closure_Ioo (by norm_num)]

lemma continuous_rho0 : Continuous rho0 := contDiff_rho0.continuous

/-- The rescaled profile `ε⁻¹ ρ((s - t)/ε)` centered at `t`. -/
def bumpAt (ε t : ℝ) (s : ℝ) : ℝ := ε⁻¹ * rho0 ((s - t) / ε)

lemma contDiff_bumpAt (ε t : ℝ) : ContDiff ℝ ∞ (bumpAt ε t) := by
  unfold bumpAt
  exact contDiff_const.mul (contDiff_rho0.comp ((contDiff_id.sub contDiff_const).div_const _))

lemma continuous_bumpAt (ε t : ℝ) : Continuous (bumpAt ε t) := (contDiff_bumpAt ε t).continuous

variable {ε : ℝ}

lemma bumpAt_nonneg (hε : 0 < ε) (t s : ℝ) : 0 ≤ bumpAt ε t s :=
  mul_nonneg (inv_nonneg.2 hε.le) (rho0_nonneg _)

lemma bumpAt_eq_zero (hε : 0 < ε) {t s : ℝ} (hs : s ∉ Ioo (t - ε / 4) (t + ε / 4)) :
    bumpAt ε t s = 0 := by
  unfold bumpAt
  rw [rho0_eq_zero, mul_zero]
  intro h
  apply hs
  obtain ⟨h1, h2⟩ := h
  rw [lt_div_iff₀ hε] at h1
  rw [div_lt_iff₀ hε] at h2
  constructor <;> linarith

lemma integral_bumpAt (hε : 0 < ε) (t : ℝ) : ∫ s, bumpAt ε t s = 1 := by
  unfold bumpAt
  rw [integral_const_mul]
  have h1 : ∫ s, rho0 ((s - t) / ε) = ∫ s, rho0 (s / ε) :=
    integral_sub_right_eq_self (fun s => rho0 (s / ε)) t
  rw [h1, Measure.integral_comp_div, integral_rho0, abs_of_pos hε]
  field_simp
  simp

lemma bumpAt_add (ε t c s : ℝ) : bumpAt ε (t + c) s = bumpAt ε t (s - c) := by
  unfold bumpAt; ring_nf

lemma integrable_bumpAt_mul (hε : 0 < ε) (t : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable fun s => F s * bumpAt ε t s := by
  refine (hF.mul (continuous_bumpAt ε t)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.mul_left ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := t - ε / 4) (b := t + ε / 4)) fun s hs => ?_
  exact bumpAt_eq_zero hε fun h => hs (Ioo_subset_Icc_self h)

/-- Averages against the profile are bounded by the supremum on its support. -/
lemma abs_integral_mul_bumpAt_le (hε : 0 < ε) (t : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {B : ℝ}
    (hB : ∀ s ∈ Ioo (t - ε / 4) (t + ε / 4), |F s| ≤ B) :
    |∫ s, F s * bumpAt ε t s| ≤ B := by
  calc |∫ s, F s * bumpAt ε t s| ≤ ∫ s, |F s * bumpAt ε t s| := by
        exact abs_integral_le_integral_abs
    _ ≤ ∫ s, B * bumpAt ε t s := by
        refine integral_mono (integrable_bumpAt_mul hε t hF).abs
          ((integrable_bumpAt_mul hε t continuous_const)) fun s => ?_
        by_cases hs : s ∈ Ioo (t - ε / 4) (t + ε / 4)
        · rw [abs_mul, abs_of_nonneg (bumpAt_nonneg hε t s)]
          exact mul_le_mul_of_nonneg_right (hB s hs) (bumpAt_nonneg hε t s)
        · simp [bumpAt_eq_zero hε hs]
    _ = B := by rw [integral_const_mul, integral_bumpAt hε, mul_one]

/-- The `p`-th moment of a translated profile changes by at most `p` times the shift. -/
lemma moment_shift_le (hε : 0 < ε) (t c : ℝ) (hc : 0 ≤ c) (p : ℕ)
    (h0 : 0 ≤ t - ε / 4) (h1 : t + ε / 4 + c ≤ 1) :
    |(∫ s, s ^ p * bumpAt ε (t + c) s) - ∫ s, s ^ p * bumpAt ε t s| ≤ c * p := by
  have hshift : ∫ s, s ^ p * bumpAt ε (t + c) s = ∫ s, (s + c) ^ p * bumpAt ε t s := by
    simp_rw [bumpAt_add]
    rw [← integral_sub_right_eq_self (fun s => (s + c) ^ p * bumpAt ε t s) c]
    simp
  rw [hshift, ← integral_sub (integrable_bumpAt_mul hε t (by fun_prop))
    (integrable_bumpAt_mul hε t (by fun_prop))]
  simp_rw [← sub_mul]
  refine abs_integral_mul_bumpAt_le hε t (by fun_prop) fun s hs => ?_
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hs1 : s + c ≤ 1 := by linarith [hs.2]
  refine (abs_pow_sub_pow_le _ _ p).trans ?_
  have hm : max |s + c| |s| ≤ 1 := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hs0]; exact max_le hs1 (by linarith)
  have hm0 : 0 ≤ max |s + c| |s| := le_max_of_le_right (abs_nonneg _)
  calc |s + c - s| * p * max |s + c| |s| ^ (p - 1) ≤ |s + c - s| * p * 1 := by
        gcongr; exact pow_le_one₀ hm0 hm
    _ = c * p := by rw [add_sub_cancel_left, abs_of_nonneg hc, mul_one]


/-! ### Moment corrections on the windows `(1/2 + i/10, 1/2 + (i+1)/10)` -/

/-- Left end of the `i`-th correction window. -/
def winA (i : Fin 4) : ℝ := 1 / 2 + (i : ℕ) / 10

/-- Center of the `i`-th correction window. -/
def winC (i : Fin 4) : ℝ := winA i + 1 / 20

/-- The cut-off of the `i`-th correction window. -/
def psiC (i : Fin 4) (s : ℝ) : ℝ := rho0 ((s - winC i) * 10)

lemma contDiff_psiC (i : Fin 4) : ContDiff ℝ ∞ (psiC i) :=
  contDiff_rho0.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)

lemma psiC_eq_zero (i : Fin 4) {s : ℝ} (hs : s ∉ Ioo (winC i - 1 / 40) (winC i + 1 / 40)) :
    psiC i s = 0 := by
  refine rho0_eq_zero fun h => hs ⟨?_, ?_⟩ <;> linarith [h.1, h.2]

lemma tsupport_psiC (i : Fin 4) : tsupport (psiC i) ⊆ Icc (winC i - 1 / 40) (winC i + 1 / 40) :=
  closure_minimal (fun _ hs => Ioo_subset_Icc_self (by_contra fun h => hs (psiC_eq_zero i h)))
    isClosed_Icc

lemma tsupport_psiC_sub (i : Fin 4) : tsupport (psiC i) ⊆ Ioo (winA i) (winA i + 1 / 10) := by
  refine (tsupport_psiC i).trans fun s hs => ?_
  simp only [winC, mem_Icc] at hs
  constructor <;> linarith [hs.1, hs.2]

lemma finite_moment_correction_psiC (M : ℕ) (i : Fin 4) :
    ∃ (Λ : (Fin (M - 1) → ℝ) →ₗ[ℝ] Polynomial ℝ) (C : ℝ), ∀ m : Fin (M - 1) → ℝ,
      (Λ m).degree < ((M - 1 : ℕ) : WithBot ℕ) ∧
      (∀ r : Fin (M - 1), ∫ s in winA i..winA i + 1 / 10, s ^ (r : ℕ) * (psiC i s * (Λ m).eval s)
        = m r) ∧
      (∀ P : Polynomial ℝ, P.degree < ((M - 1 : ℕ) : WithBot ℕ) →
        (∀ r : Fin (M - 1), ∫ s in winA i..winA i + 1 / 10, s ^ (r : ℕ) * (psiC i s * P.eval s)
          = m r) → P = Λ m) ∧
      ∫ s in winA i..winA i + 1 / 10, |deriv (fun s => psiC i s * (Λ m).eval s) s| ≤ C * ‖m‖ :=
  finite_moment_correction M _ _ (by linarith) (psiC i) (contDiff_psiC i) (tsupport_psiC_sub i)
    (fun s => rho0_nonneg _)
    ⟨winC i - 1 / 40, winC i + 1 / 40, by linarith, fun s hs => rho0_pos ⟨by
      linarith [hs.1], by linarith [hs.2]⟩⟩

/-- The linear map `m ↦ P_m` of Lemma 2.11 on the `i`-th window. -/
def corrMap (M : ℕ) (i : Fin 4) : (Fin (M - 1) → ℝ) →ₗ[ℝ] Polynomial ℝ :=
  Classical.choose (finite_moment_correction_psiC M i)

/-- The constant of Lemma 2.11 on the `i`-th window. -/
def corrConst (M : ℕ) (i : Fin 4) : ℝ :=
  Classical.choose (Classical.choose_spec (finite_moment_correction_psiC M i))

lemma corrMap_spec (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) :
    (∀ r : Fin (M - 1), ∫ s in winA i..winA i + 1 / 10,
        s ^ (r : ℕ) * (psiC i s * (corrMap M i m).eval s) = m r) ∧
      ∫ s in winA i..winA i + 1 / 10, |deriv (fun s => psiC i s * (corrMap M i m).eval s) s|
        ≤ corrConst M i * ‖m‖ := by
  have := Classical.choose_spec (Classical.choose_spec (finite_moment_correction_psiC M i)) m
  exact ⟨this.2.1, this.2.2.2⟩

/-- The correction profile `θ = ψ P_m`. -/
def corrTheta (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) (s : ℝ) : ℝ :=
  psiC i s * (corrMap M i m).eval s

/-- Its derivative, the correcting control. -/
def corrH (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) : ℝ → ℝ := deriv (corrTheta M i m)

lemma contDiff_corrTheta (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) :
    ContDiff ℝ ∞ (corrTheta M i m) :=
  (contDiff_psiC i).mul (by simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) (corrMap M i m) ∞)

lemma contDiff_corrH (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) : ContDiff ℝ ∞ (corrH M i m) :=
  (contDiff_corrTheta M i m).iterate_deriv 1

lemma continuous_corrH (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) : Continuous (corrH M i m) :=
  (contDiff_corrH M i m).continuous

lemma corrTheta_eq_zero (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) {s : ℝ}
    (hs : s ∉ Ioo (winA i) (winA i + 1 / 10)) : corrTheta M i m s = 0 := by
  have : s ∉ tsupport (psiC i) := fun h => hs (tsupport_psiC_sub i h)
  simp [corrTheta, image_eq_zero_of_notMem_tsupport this]

lemma corrH_eq_zero (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) {s : ℝ}
    (hs : s ∉ Ioo (winA i) (winA i + 1 / 10)) : corrH M i m s = 0 := by
  have h1 : s ∉ tsupport (corrTheta M i m) := fun h =>
    hs (tsupport_psiC_sub i (tsupport_mul_subset_left h))
  by_contra h
  exact h1 (support_deriv_subset h)

lemma corrTheta_sum {ι : Type*} (M : ℕ) (i : Fin 4) (t : Finset ι) (a : ι → ℝ)
    (m : ι → Fin (M - 1) → ℝ) :
    corrTheta M i (∑ k ∈ t, a k • m k) = fun s => ∑ k ∈ t, a k * corrTheta M i (m k) s := by
  funext s
  simp only [corrTheta, map_sum, map_smul, Polynomial.eval_finset_sum, Polynomial.eval_smul,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma corrH_sum {ι : Type*} (M : ℕ) (i : Fin 4) (t : Finset ι) (a : ι → ℝ)
    (m : ι → Fin (M - 1) → ℝ) (s : ℝ) :
    corrH M i (∑ k ∈ t, a k • m k) s = ∑ k ∈ t, a k * corrH M i (m k) s := by
  simp only [corrH, corrTheta_sum]
  rw [deriv_fun_sum fun k _ => ((contDiff_corrTheta M i (m k)).differentiable (by simp) s).const_mul _]
  exact Finset.sum_congr rfl fun k _ =>
    deriv_const_mul _ ((contDiff_corrTheta M i (m k)).differentiable (by simp) s)

lemma integrable_corrH_mul (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) {F : ℝ → ℝ}
    (hF : Continuous F) : Integrable fun s => F s * corrH M i m s := by
  refine (hF.mul (continuous_corrH M i m)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.mul_left ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := winA i) (b := winA i + 1 / 10))
    fun s hs => corrH_eq_zero M i m fun h => hs (Ioo_subset_Icc_self h)

lemma integral_eq_window {f : ℝ → ℝ} (i : Fin 4)
    (hf : ∀ s, s ∉ Ioo (winA i) (winA i + 1 / 10) → f s = 0) :
    ∫ s, f s = ∫ s in winA i..winA i + 1 / 10, f s := by
  refine (intervalIntegral.integral_eq_integral_of_support_subset fun s hs => ?_).symm
  by_contra h
  exact hs (hf s fun h' => h (Ioo_subset_Ioc_self h'))

lemma integral_abs_corrH_le (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) :
    ∫ s, |corrH M i m s| ≤ corrConst M i * ‖m‖ := by
  rw [integral_eq_window i fun s hs => by rw [corrH_eq_zero M i m hs, abs_zero]]
  exact (corrMap_spec M i m).2

/-- Integration by parts for the corrections: `∫ sʳ θ' = -r ∫ s^{r-1} θ`. -/
lemma integral_pow_mul_corrH (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) (r : ℕ) :
    ∫ s, s ^ (r + 1) * corrH M i m s = -((r + 1 : ℕ) : ℝ) *
      ∫ s in winA i..winA i + 1 / 10, s ^ r * corrTheta M i m s := by
  rw [integral_eq_window i fun s hs => by rw [corrH_eq_zero M i m hs, mul_zero]]
  have hd : Differentiable ℝ (corrTheta M i m) := (contDiff_corrTheta M i m).differentiable (by simp)
  unfold corrH
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (u' := fun s => ((r + 1 : ℕ) : ℝ) * s ^ r)
    (fun s _ => by simpa using hasDerivAt_pow (r + 1) s) (fun s _ => (hd s).hasDerivAt)
    ((by fun_prop : Continuous fun s : ℝ => ((r + 1 : ℕ) : ℝ) * s ^ r).intervalIntegrable _ _)
    ((continuous_corrH M i m).intervalIntegrable _ _)]
  rw [corrTheta_eq_zero M i m (fun h => lt_irrefl _ h.2),
    corrTheta_eq_zero M i m (fun h => lt_irrefl _ h.1)]
  simp only [mul_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  congr 1; funext s; ring

lemma integral_corrH (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) : ∫ s, corrH M i m s = 0 := by
  rw [integral_eq_window i fun s hs => corrH_eq_zero M i m hs]
  have hd : Differentiable ℝ (corrTheta M i m) := (contDiff_corrTheta M i m).differentiable (by simp)
  unfold corrH
  rw [intervalIntegral.integral_deriv_eq_sub (fun s _ => hd s)
    ((continuous_corrH M i m).intervalIntegrable _ _)]
  rw [corrTheta_eq_zero M i m (fun h => lt_irrefl _ h.2),
    corrTheta_eq_zero M i m (fun h => lt_irrefl _ h.1), sub_zero]

/-- The corrections realize the prescribed moments. -/
lemma moment_corrH (M : ℕ) (i : Fin 4) (m : Fin (M - 1) → ℝ) (r : ℕ) (hr : r + 1 < M) :
    ∫ s, s ^ (r + 1) * corrH M i m s = -((r + 1 : ℕ) : ℝ) * m ⟨r, by omega⟩ := by
  rw [integral_pow_mul_corrH]
  have := (corrMap_spec M i m).1 ⟨r, by omega⟩
  simp only at this
  rw [← this]
  rfl

end AnomDiss
