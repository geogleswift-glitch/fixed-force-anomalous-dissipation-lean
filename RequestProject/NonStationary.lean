module

public import RequestProject.WeightedFourier
public import RequestProject.TorusCalc

/-!
# Non-stationary phase for low outputs (Lemma 3.4)

If `|DΨ(y)ᵀe| ≥ 4a` and `|ξ + n| ≤ aρ` with `ξ = ρe`, the phase `φ(y) = ξ·w(y) - n·y` of
`c_n^Ψ(ξ)` has gradient `V = DΨᵀξ - (ξ + n)` of length `≥ 3aρ`.  With `W = V/|V|²` one has
`W·∇e^{2πiφ} = 2πi e^{2πiφ}`, so `∫ g e^{2πiφ} = ∫ (Tg) e^{2πiφ}` with
`Tg = -(2πi)⁻¹ div(gW)`.  Since all derivatives of `W` up to order `J` are `O(1/ρ)`,
`|c_n| ≤ sup|T^J 1| = O(ρ^{-J})`; there are `O(ρ²)` such `n`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- Uniform bound `A` on all iterated derivatives of order `≤ M`. -/
def SymBd (M : ℕ) (A : ℝ) (g : Pt 2 → ℂ) : Prop :=
  ∀ k ≤ M, ∀ y, ‖iteratedFDeriv ℝ k g y‖ ≤ A

/-- The transposed operator of one integration by parts, `Tg = -(2πi)⁻¹ div(gW)`. -/
def ibpOp (W : Fin 2 → Pt 2 → ℂ) (g : Pt 2 → ℂ) (y : Pt 2) : ℂ :=
  -(2 * π * Complex.I)⁻¹ * ∑ i, pd i (fun x => g x * W i x) y

lemma integral_pd_periodic_complex (h : Pt 2 → ℂ) (hh : ContDiff ℝ 1 h) (hp : IsPeriodic h)
    (i : Fin 2) : ∫ x in cell 2, pd i h x = 0 := by
  have hint : IntegrableOn (pd i h) (cell 2) :=
    (continuous_pd_of_C1 h hh i).continuousOn.integrableOn_compact isCompact_Icc
  have hre : ∀ x, (pd i h x).re = pd i (fun y => (h y).re) x := by
    intro x; unfold pd
    rw [show (fun y => (h y).re) = Complex.reCLM ∘ h from rfl,
      (Complex.reCLM.hasFDerivAt.comp x (hh.differentiable one_ne_zero x).hasFDerivAt).fderiv]
    rfl
  have him : ∀ x, (pd i h x).im = pd i (fun y => (h y).im) x := by
    intro x; unfold pd
    rw [show (fun y => (h y).im) = Complex.imCLM ∘ h from rfl,
      (Complex.imCLM.hasFDerivAt.comp x (hh.differentiable one_ne_zero x).hasFDerivAt).fderiv]
    rfl
  apply Complex.ext
  · have hr := integral_re hint
    simp only [RCLike.re_to_complex] at hr
    rw [← hr]
    simp only [hre, Complex.zero_re]
    exact integral_pd_periodic _ (Complex.reCLM.contDiff.comp hh) (fun x n => by simp [hp x n]) i
  · have hr := integral_im hint
    simp only [RCLike.im_to_complex] at hr
    rw [← hr]
    simp only [him, Complex.zero_im]
    exact integral_pd_periodic _ (Complex.imCLM.contDiff.comp hh) (fun x n => by simp [hp x n]) i

lemma pd_mul_complex (f g : Pt 2 → ℂ) (x : Pt 2) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  unfold pd
  rw [fderiv_fun_mul hf hg]
  simp; ring

lemma integral_mul_pd_complex (f g : Pt 2 → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : IsPeriodic f) (hgp : IsPeriodic g) (i : Fin 2) :
    ∫ x in cell 2, f x * pd i g x = -∫ x in cell 2, pd i f x * g x := by
  have h0 := integral_pd_periodic_complex _ (hf.mul hg) (fun x n => by simp [hfp x n, hgp x n]) i
  have e : ∀ x, pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x :=
    fun x => pd_mul_complex f g x (hf.differentiable one_ne_zero x)
      (hg.differentiable one_ne_zero x) i
  simp only [e] at h0
  have hc : ∀ (F : Pt 2 → ℂ), Continuous F → IntegrableOn F (cell 2) := fun F hF =>
    hF.continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_add (f := fun x => pd i f x * g x) (g := fun x => f x * pd i g x)
    (hc _ ((continuous_pd_of_C1 f hf i).mul hg.continuous))
    (hc _ (hf.continuous.mul (continuous_pd_of_C1 g hg i)))] at h0
  linear_combination h0

lemma contDiff_pd_inf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Pt 2 → E)
    (hh : ContDiff ℝ ∞ h) (i : Fin 2) : ContDiff ℝ ∞ (pd i h) :=
  (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma ibpOp_contDiff (W : Fin 2 → Pt 2 → ℂ) (g : Pt 2 → ℂ) (hW : ∀ i, ContDiff ℝ ∞ (W i))
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (ibpOp W g) := by
  unfold ibpOp
  exact contDiff_const.mul (ContDiff.sum fun i _ => contDiff_pd_inf _ (hg.mul (hW i)) i)

lemma ibpOp_periodic (W : Fin 2 → Pt 2 → ℂ) (g : Pt 2 → ℂ) (hWp : ∀ i, IsPeriodic (W i))
    (hgp : IsPeriodic g) : IsPeriodic (ibpOp W g) := by
  intro x n
  unfold ibpOp
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact isPeriodic_pd _ (fun y m => by simp [hgp y m, hWp i y m]) i x n

/-- One integration by parts. -/
lemma ibp_identity (E g : Pt 2 → ℂ) (W V : Fin 2 → Pt 2 → ℂ)
    (hE : ContDiff ℝ ∞ E) (hEp : IsPeriodic E) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodic g)
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (hWp : ∀ i, IsPeriodic (W i))
    (hdE : ∀ i y, pd i E y = 2 * π * Complex.I * V i y * E y)
    (hWV : ∀ y, ∑ i, W i y * V i y = 1) :
    ∫ y in cell 2, g y * E y = ∫ y in cell 2, ibpOp W g y * E y := by
  have c1 : ∀ {f : Pt 2 → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ 1 f := fun hf => hf.of_le (by simp)
  have hc : ∀ (F : Pt 2 → ℂ), Continuous F → IntegrableOn F (cell 2) := fun F hF =>
    hF.continuousOn.integrableOn_compact isCompact_Icc
  set c : ℂ := 2 * π * Complex.I with hcdef
  have hc0 : c ≠ 0 := by simp [c, pi_ne_zero]
  have hgW : ∀ i, ContDiff ℝ ∞ (fun x => g x * W i x) := fun i => hg.mul (hW i)
  have step1 : ∀ y, g y * E y = c⁻¹ * ∑ i, (g y * W i y) * pd i E y := by
    intro y
    simp only [hdE]
    calc g y * E y = g y * E y * ∑ i, W i y * V i y := by rw [hWV, mul_one]
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
  have step2 : ∀ y, ibpOp W g y * E y = -c⁻¹ * ∑ i, pd i (fun x => g x * W i x) y * E y := by
    intro y; unfold ibpOp; rw [mul_assoc, Finset.sum_mul]
  simp only [step1, step2]
  rw [integral_const_mul, integral_const_mul, integral_finset_sum, integral_finset_sum]
  · rw [neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1; refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_mul_pd_complex _ _ (c1 (hgW i)) (c1 hE)
      (fun y m => by simp [hgp y m, hWp i y m]) hEp i
  · exact fun i _ => hc _ ((continuous_pd_of_C1 _ (c1 (hgW i)) i).mul hE.continuous)
  · exact fun i _ => hc _ ((hgW i).continuous.mul (continuous_pd_of_C1 _ (c1 hE) i))
lemma natCast_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

lemma norm_iteratedFDeriv_pd_le (h : Pt 2 → ℂ) (hh : ContDiff ℝ ∞ h) (i : Fin 2) (k : ℕ)
    (y : Pt 2) : ‖iteratedFDeriv ℝ k (pd i h) y‖ ≤ ‖iteratedFDeriv ℝ (k + 1) h y‖ := by
  have e : pd i h = (ContinuousLinearMap.apply ℝ ℂ (Pi.single i (1:ℝ) : Pt 2)) ∘ fderiv ℝ h :=
    rfl
  rw [e]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (N := ∞)
    ((hh.fderiv_right (m := ∞) (by simp)).contDiffAt) (natCast_le_infty k)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (le_of_eq (one_mul _))
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
  simp only [ContinuousLinearMap.apply_apply, one_mul]
  refine (L.le_opNorm _).trans (le_of_eq ?_)
  simp [Pi.norm_single]

/-- One step of the symbol calculus: `T` gains the factor `B` and loses one derivative. -/
lemma ibpOp_symBd (W : Fin 2 → Pt 2 → ℂ) (g : Pt 2 → ℂ) (hW : ∀ i, ContDiff ℝ ∞ (W i))
    (hg : ContDiff ℝ ∞ g) (M : ℕ) (A B : ℝ) (hgA : SymBd (M + 1) A g)
    (hWB : ∀ i, SymBd (M + 1) B (W i)) :
    SymBd M (2 ^ (M + 2) * A * B) (ibpOp W g) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hgA 0 (Nat.zero_le _) 0)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hWB 0 0 (Nat.zero_le _) 0)
  have hgW : ∀ i, ContDiff ℝ ∞ (fun x => g x * W i x) := fun i => hg.mul (hW i)
  have hprod : ∀ i, ∀ k ≤ M, ∀ y,
      ‖iteratedFDeriv ℝ (k + 1) (fun x => g x * W i x) y‖ ≤ 2 ^ (k + 1) * A * B := by
    intro i k hk y
    refine (norm_iteratedFDeriv_mul_le hg (hW i) y (natCast_le_infty _)).trans ?_
    calc _ ≤ ∑ j ∈ Finset.range (k + 1 + 1), ((k + 1).choose j : ℝ) * A * B := by
          gcongr with j hj
          · exact hgA j (by simp at hj; omega) y
          · exact hWB i _ (by omega) y
      _ = 2 ^ (k + 1) * A * B := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          norm_cast
          rw [Nat.sum_range_choose]
  intro k hk y
  have hpd : ∀ i, ContDiff ℝ ∞ (pd i (fun x => g x * W i x)) :=
    fun i => contDiff_pd_inf _ (hgW i) i
  have e : ibpOp W g = (-(2 * π * Complex.I)⁻¹) • fun y => ∑ i, pd i (fun x => g x * W i x) y :=
    rfl
  rw [e, iteratedFDeriv_const_smul_apply
    ((ContDiff.sum fun i _ => hpd i).of_le (natCast_le_infty k)).contDiffAt,
    iteratedFDeriv_sum (fun j _ => (hpd j).of_le (natCast_le_infty k)), norm_smul,
    Finset.sum_apply]
  have hc : ‖-(2 * (π : ℂ) * Complex.I)⁻¹‖ ≤ 1 := by
    rw [norm_neg, norm_inv]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos pi_pos]
    apply inv_le_one_of_one_le₀
    nlinarith [pi_gt_three]
  have hs : ‖∑ i, iteratedFDeriv ℝ k (pd i (fun x => g x * W i x)) y‖ ≤ 2 * (2 ^ (k + 1) * A * B) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ i : Fin 2, 2 ^ (k + 1) * A * B := by
          gcongr with i
          exact (norm_iteratedFDeriv_pd_le _ (hgW i) i k y).trans (hprod i k hk y)
      _ = _ := by simp
  have hk2 : (2:ℝ) ^ (k + 2) ≤ 2 ^ (M + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc _ ≤ 1 * (2 * (2 ^ (k + 1) * A * B)) := by gcongr
    _ = 2 ^ (k + 2) * A * B := by ring
    _ ≤ _ := by gcongr

lemma symBd_one (M : ℕ) : SymBd M 1 (fun _ : Pt 2 => (1 : ℂ)) := by
  intro k _ y
  cases k with
  | zero => simp [norm_iteratedFDeriv_zero]
  | succ k => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]; simp

lemma SymBd.mono {M M' : ℕ} {A A' : ℝ} {g : Pt 2 → ℂ} (h : SymBd M A g) (hM : M' ≤ M)
    (hA : A ≤ A') : SymBd M' A' g :=
  fun k hk y => (h k (hk.trans hM) y).trans hA

/-- Iterating `T` on the constant `1`. -/
lemma ibpOp_iter_symBd (W : Fin 2 → Pt 2 → ℂ) (hW : ∀ i, ContDiff ℝ ∞ (W i)) (J : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hWB : ∀ i, SymBd J B (W i)) :
    ∀ s ≤ J, ContDiff ℝ ∞ ((ibpOp W)^[s] (fun _ => 1)) ∧
      SymBd (J - s) ((2 ^ (J + 2) * B) ^ s) ((ibpOp W)^[s] (fun _ => 1)) := by
  intro s
  induction s with
  | zero => intro _; exact ⟨contDiff_const, by simpa using symBd_one J⟩
  | succ s ih =>
    intro hs
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    refine ⟨ibpOp_contDiff W _ hW h1, ?_⟩
    have hJs : J - s = (J - (s + 1)) + 1 := by omega
    rw [hJs] at h2
    have hAs : 0 ≤ (2 ^ (J + 2) * B) ^ s := by positivity
    refine (ibpOp_symBd W _ hW h1 (J - (s + 1)) _ B h2
      (fun i => (hWB i).mono (by omega) le_rfl)).mono le_rfl ?_
    have : (2:ℝ) ^ (J - (s + 1) + 2) ≤ 2 ^ (J + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2:ℝ) ^ (J - (s + 1) + 2) * (2 ^ (J + 2) * B) ^ s * B
        ≤ 2 ^ (J + 2) * (2 ^ (J + 2) * B) ^ s * B := by gcongr
      _ = _ := by ring

/-- The phase gradient `V = DΨᵀξ - (ξ + n)`. -/
def ngrad (Ψ : Pt 2 → Pt 2) (ξ : Pt 2) (n : Fin 2 → ℤ) (i : Fin 2) (y : Pt 2) : ℝ :=
  ∑ j, ξ j * jac Ψ y j i - ξ i - (n i : ℝ)

/-- The integration-by-parts field `W = V / |V|²`. -/
def nW (Ψ : Pt 2 → Pt 2) (ξ : Pt 2) (n : Fin 2 → ℤ) (i : Fin 2) (y : Pt 2) : ℂ :=
  ((ngrad Ψ ξ n i y / (ngrad Ψ ξ n 0 y ^ 2 + ngrad Ψ ξ n 1 y ^ 2) : ℝ) : ℂ)

/-- `u ↦ u / |u|²`. -/
noncomputable def invSq (u : Pt 2) : Pt 2 := fun i => u i / (u 0 ^ 2 + u 1 ^ 2)

/-- The open set `u ≠ 0`. -/
def posSet : Set (Pt 2) := {u | 0 < u 0 ^ 2 + u 1 ^ 2}

lemma isOpen_posSet : IsOpen posSet :=
  isOpen_lt continuous_const (by fun_prop)

lemma contDiffOn_invSq : ContDiffOn ℝ ∞ invSq posSet := by
  refine contDiffOn_pi.2 fun i => ?_
  exact ((contDiff_apply ℝ ℝ i).contDiffOn).div
    (((contDiff_apply ℝ ℝ 0).pow 2).add ((contDiff_apply ℝ ℝ 1).pow 2)).contDiffOn
    (fun u hu => ne_of_gt hu)

lemma invSq_deriv_bound (a R : ℝ) (ha : 0 < a) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Pt 2, 9 * a ^ 2 ≤ u 0 ^ 2 + u 1 ^ 2 → ‖u‖ ≤ R →
      ∀ i ≤ J, ‖iteratedFDerivWithin ℝ i invSq posSet u‖ ≤ C := by
  set Kc : Set (Pt 2) := {u | 9 * a ^ 2 ≤ u 0 ^ 2 + u 1 ^ 2} ∩ Metric.closedBall 0 R
  have hKc : IsCompact Kc :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const (by fun_prop))
  have hsub : Kc ⊆ posSet := fun u hu => by
    have h := hu.1; simp only [mem_setOf_eq] at h; simp only [posSet, mem_setOf_eq]
    nlinarith [sq_pos_of_pos ha]
  have hcont : ContinuousOn
      (fun u => ∑ i ∈ Finset.range (J + 1), ‖iteratedFDerivWithin ℝ i invSq posSet u‖) Kc := by
    refine ContinuousOn.mono ?_ hsub
    refine continuousOn_finset_sum _ fun i _ => ?_
    exact (contDiffOn_invSq.continuousOn_iteratedFDerivWithin (natCast_le_infty i)
      isOpen_posSet.uniqueDiffOn).norm
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun u hu1 hu2 i hi => ?_⟩
  have hu : u ∈ Kc := ⟨hu1, by simpa using hu2⟩
  have h1 := hC u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  refine le_trans ?_ (h1.trans (le_max_left _ _))
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i invSq posSet u‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))


/-- The linear map `A ↦ Aᵀ e` on Jacobians. -/
noncomputable def trE (e : Pt 2) : (Pt 2 →L[ℝ] Pt 2) →L[ℝ] Pt 2 :=
  ContinuousLinearMap.pi fun j => ∑ l, e l • (ContinuousLinearMap.proj l).comp
    (ContinuousLinearMap.apply ℝ (Pt 2) (Pi.single j (1:ℝ) : Pt 2))

lemma trE_apply (e : Pt 2) (A : Pt 2 →L[ℝ] Pt 2) (j : Fin 2) :
    trE e A j = ∑ l, e l * A (Pi.single j 1) l := by
  simp [trE]

lemma norm_trE_le (e : Pt 2) (he : ∀ l, |e l| ≤ 1) : ‖trE e‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun A => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [trE_apply, Real.norm_eq_abs]
  have hv : ‖A (Pi.single j 1)‖ ≤ ‖A‖ := by
    refine (A.le_opNorm _).trans (le_of_eq ?_); simp [Pi.norm_single]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |e l * A (Pi.single j 1) l| ≤ ∑ _l : Fin 2, ‖A‖ := by
        gcongr with l
        rw [abs_mul]
        have h1 : |A (Pi.single j 1) l| ≤ ‖A‖ :=
          ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm (A (Pi.single j 1)) l).trans hv
        calc |e l| * |A (Pi.single j 1) l| ≤ 1 * ‖A‖ :=
              mul_le_mul (he l) h1 (abs_nonneg _) zero_le_one
          _ = ‖A‖ := one_mul _
    _ = 2 * ‖A‖ := by simp

lemma trE_fderiv_eq (e : Pt 2) (Ψ : Pt 2 → Pt 2) (y : Pt 2) :
    trE e (fderiv ℝ Ψ y) = (jac Ψ y)ᵀ *ᵥ e := by
  funext j
  rw [trE_apply]
  simp [Matrix.mulVec, dotProduct, jac, mul_comm]

lemma norm_iteratedFDeriv_trE_le (e : Pt 2) (he : ∀ l, |e l| ≤ 1) (Ψ : Pt 2 → Pt 2)
    (hΨ : ContDiff ℝ ∞ Ψ) (c : Pt 2) (k : ℕ) (hk : k ≠ 0) (y : Pt 2) :
    ‖iteratedFDeriv ℝ k (fun y => trE e (fderiv ℝ Ψ y) + c) y‖ ≤
      2 * ‖iteratedFDeriv ℝ (k + 1) Ψ y‖ := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ Ψ) := hΨ.fderiv_right (m := ∞) (by simp)
  rw [iteratedFDeriv_add_const_of_ne (f := fun y => trE e (fderiv ℝ Ψ y))
    ((trE e).contDiff.comp hd) hk]
  refine ((trE e).norm_iteratedFDeriv_comp_left hd.contDiffAt (natCast_le_infty k)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  gcongr
  exact norm_trE_le e he

lemma abs_apply_le_euclNorm (v : Pt 2) (l : Fin 2) : |v l| ≤ euclNorm v := by
  unfold euclNorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ l))

lemma fderiv_lift_periodic {Ψ : Pt 2 → Pt 2} (hlift : IsLift Ψ) (y : Pt 2) (m : Fin 2 → ℤ) :
    fderiv ℝ Ψ (y + intVec m) = fderiv ℝ Ψ y := by
  rw [← fderiv_comp_add_right]
  have e : (fun x => Ψ (x + intVec m)) = fun x => Ψ x + intVec m := by
    funext x; exact hlift x m
  rw [e, fderiv_add_const]

/-- Uniform `O(1/ρ)` bounds on the derivatives of `W` up to order `J`. -/
lemma nW_bounds (a : ℝ) (ha : 0 < a) (K : ℕ → ℝ) (J : ℕ) :
    ∃ CW : ℝ, 0 ≤ CW ∧ ∀ Ψ : Pt 2 → Pt 2, ContDiff ℝ ∞ Ψ → IsLift Ψ →
      (∀ y, ∀ e : Pt 2, euclNorm e = 1 → 4 * a ≤ euclNorm ((jac Ψ y)ᵀ *ᵥ e)) →
      (∀ y, ∀ k, 1 ≤ k → k ≤ J + 1 → ‖iteratedFDeriv ℝ k Ψ y‖ ≤ K k) →
      ∀ e : Pt 2, euclNorm e = 1 → ∀ ρ : ℝ, 1 ≤ ρ → ∀ n : Fin 2 → ℤ,
      euclNorm (ρ • e + intVec n) ≤ a * ρ →
      (∀ i, ContDiff ℝ ∞ (nW Ψ (ρ • e) n i)) ∧ (∀ i, IsPeriodic (nW Ψ (ρ • e) n i)) ∧
      (∀ y, ∑ i, nW Ψ (ρ • e) n i y * (ngrad Ψ (ρ • e) n i y : ℂ) = 1) ∧
      ∀ i, SymBd J (CW / ρ) (nW Ψ (ρ • e) n i) := by
  obtain ⟨C, hC0, hC⟩ := invSq_deriv_bound a (2 * K 1 + a) ha J
  set D : ℝ := 1 + 2 * ∑ i ∈ Finset.range (J + 2), |K i| with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ i ∈ Finset.range (J + 2), |K i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  refine ⟨J.factorial * C * D ^ J, by positivity,
    fun Ψ hΨ hlift hlow hbd e he ρ hρ n hn => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  have hel : ∀ l, |e l| ≤ 1 := fun l => he ▸ abs_apply_le_euclNorm e l
  set c : Pt 2 := (-ρ⁻¹) • (ρ • e + intVec n) with hcdef
  have hcn : euclNorm c ≤ a := by
    rw [hcdef, euclNorm_smul, abs_neg, abs_inv, abs_of_pos hρ0]
    rw [inv_mul_le_iff₀ hρ0]; linarith
  set U : Pt 2 → Pt 2 := fun y => trE e (fderiv ℝ Ψ y) + c with hUdef
  have hd : ContDiff ℝ ∞ (fderiv ℝ Ψ) := hΨ.fderiv_right (m := ∞) (by simp)
  have hU : ContDiff ℝ ∞ U := ((trE e).contDiff.comp hd).add contDiff_const
  have hVU : ∀ y j, ngrad Ψ (ρ • e) n j y = ρ * U y j := by
    intro y j
    simp only [ngrad, hUdef, hcdef, Pi.add_apply, trE_apply, Pi.smul_apply, smul_eq_mul, intVec,
      jac, Matrix.of_apply]
    field_simp
    simp only [Finset.mul_sum, mul_assoc]
    ring
  have hUlow : ∀ y, 9 * a ^ 2 ≤ U y 0 ^ 2 + U y 1 ^ 2 := by
    intro y
    have h1 := hlow y e he
    have h2 : (jac Ψ y)ᵀ *ᵥ e = U y + (-c) := by
      simp [hUdef, trE_fderiv_eq]
    rw [h2] at h1
    have h3 := euclNorm_add_le (U y) (-c)
    have h4 : euclNorm (-c) = euclNorm c := by
      rw [show -c = (-1 : ℝ) • c by simp, euclNorm_smul]; simp
    have h5 : 3 * a ≤ euclNorm (U y) := by linarith
    have h6 := euclNorm_sq' (U y)
    rw [Fin.sum_univ_two] at h6
    nlinarith
  have hUpos : ∀ y, U y ∈ posSet := fun y => by
    have := hUlow y; simp only [posSet, mem_setOf_eq]; nlinarith [sq_pos_of_pos ha]
  have hUup : ∀ y, ‖U y‖ ≤ 2 * K 1 + a := by
    intro y
    refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_le_euclNorm c).trans hcn))
    refine ((trE e).le_opNorm _).trans ?_
    have h1 : ‖fderiv ℝ Ψ y‖ ≤ K 1 := by
      rw [← norm_iteratedFDeriv_one]; exact hbd y 1 le_rfl (by omega)
    exact mul_le_mul (norm_trE_le e hel) h1 (norm_nonneg _) (by norm_num)
  have hWeq : ∀ i, nW Ψ (ρ • e) n i = fun y => ((ρ⁻¹ * invSq (U y) i : ℝ) : ℂ) := by
    intro i; funext y
    simp only [nW, invSq, hVU]
    have := hUpos y; simp only [posSet, mem_setOf_eq] at this
    congr 1
    field_simp
  have hG : ContDiff ℝ ∞ (invSq ∘ U) := contDiffOn_invSq.comp_contDiff hU hUpos
  set L : Fin 2 → Pt 2 →L[ℝ] ℂ := fun i => ρ⁻¹ • (Complex.ofRealCLM.comp
    (ContinuousLinearMap.proj i)) with hLdef
  have hLeq : ∀ i, nW Ψ (ρ • e) n i = L i ∘ (invSq ∘ U) := by
    intro i; rw [hWeq]; funext y; simp [hLdef]
  have hLn : ∀ i, ‖L i‖ ≤ ρ⁻¹ := by
    intro i
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    simp only [hLdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, norm_smul, Complex.norm_real,
      norm_inv, Real.norm_eq_abs, abs_of_pos hρ0]
    gcongr
    exact (Real.norm_eq_abs (u i)).symm ▸ norm_le_pi_norm u i
  refine ⟨fun i => ?_, fun i => ?_, fun y => ?_, fun i => ?_⟩
  · rw [hLeq]; exact (L i).contDiff.comp hG
  · intro y m
    rw [hWeq]
    simp only [hUdef, fderiv_lift_periodic hlift]
  · simp only [nW, Fin.sum_univ_two]
    have hS : 0 < ngrad Ψ (ρ • e) n 0 y ^ 2 + ngrad Ψ (ρ • e) n 1 y ^ 2 := by
      have := hUpos y; simp only [posSet, mem_setOf_eq] at this
      rw [hVU, hVU]; nlinarith [mul_pos hρ0 hρ0]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [← Complex.ofReal_one]; congr 1
    field_simp
  · intro k hk y
    rw [hLeq]
    refine ((L i).norm_iteratedFDeriv_comp_left hG.contDiffAt (natCast_le_infty k)).trans ?_
    have hFdB : ‖iteratedFDeriv ℝ k (invSq ∘ U) y‖ ≤ k.factorial * C * D ^ k := by
      rw [← iteratedFDerivWithin_univ]
      refine norm_iteratedFDerivWithin_comp_le contDiffOn_invSq hU.contDiffOn
        (natCast_le_infty k) isOpen_posSet.uniqueDiffOn uniqueDiffOn_univ
        (fun y _ => hUpos y) (mem_univ y) (fun j hj => hC _ (hUlow y) (hUup y) j (by omega))
        (fun j hj1 hj2 => ?_)
      rw [iteratedFDerivWithin_univ]
      refine (norm_iteratedFDeriv_trE_le e hel Ψ hΨ c j (by omega) y).trans ?_
      refine ((mul_le_mul_of_nonneg_left (hbd y (j + 1) (by omega) (by omega))
        (by norm_num))).trans ?_
      refine le_trans ?_ (le_self_pow₀ hD1 (by omega))
      have : |K (j + 1)| ≤ ∑ i ∈ Finset.range (J + 2), |K i| :=
        Finset.single_le_sum (f := fun i => |K i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
      have := le_abs_self (K (j + 1))
      linarith
    have hkJ : (k.factorial : ℝ) * C * D ^ k ≤ J.factorial * C * D ^ J := by
      have h1 : (k.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hk
      have h2 : D ^ k ≤ D ^ J := pow_le_pow_right₀ hD1 hk
      have : 0 ≤ D ^ k := by positivity
      calc (k.factorial : ℝ) * C * D ^ k ≤ J.factorial * C * D ^ k := by gcongr
        _ ≤ _ := by gcongr
    calc ‖L i‖ * ‖iteratedFDeriv ℝ k (invSq ∘ U) y‖ ≤ ρ⁻¹ * (J.factorial * C * D ^ J) :=
          mul_le_mul (hLn i) (hFdB.trans hkJ) (norm_nonneg _) (by positivity)
      _ = _ := by rw [div_eq_inv_mul]

/-- The derivative of the real phase `φ(y) = ξ·(Ψ(y) - y) - n·y`. -/
lemma pd_phase_real (Ψ : Pt 2 → Pt 2) (hΨ : ContDiff ℝ ∞ Ψ) (ξ : Pt 2) (n : Fin 2 → ℤ)
    (y : Pt 2) :
    HasFDerivAt (fun y => dot ξ (Ψ y - y) - dot (intVec n) y)
      (fderiv ℝ (fun y => dot ξ (Ψ y - y) - dot (intVec n) y) y) y ∧
    ∀ i, pd i (fun y => dot ξ (Ψ y - y) - dot (intVec n) y) y = ngrad Ψ ξ n i y := by
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  set L : Pt 2 →L[ℝ] ℝ := ∑ j, ξ j • ContinuousLinearMap.proj j
  set M : Pt 2 →L[ℝ] ℝ := ∑ j, (ξ j + n j) • ContinuousLinearMap.proj j
  have key : (fun y => dot ξ (Ψ y - y) - dot (intVec n) y) = fun y => L (Ψ y) - M y := by
    funext y; simp [L, M, dot, intVec, Fin.sum_univ_two]; ring
  rw [key]
  have h : HasFDerivAt (fun y => L (Ψ y) - M y) (L.comp (fderiv ℝ Ψ y) - M) y :=
    (L.hasFDerivAt.comp y (hΨd y).hasFDerivAt).sub M.hasFDerivAt
  refine ⟨h.differentiableAt.hasFDerivAt, fun i => ?_⟩
  unfold pd ngrad jac
  rw [h.fderiv]
  simp [L, M, Fin.sum_univ_two, Pi.single_apply]
  fin_cases i <;> simp <;> ring

/-- The derivative of the phase factor. -/
lemma pd_phase (Ψ : Pt 2 → Pt 2) (hΨ : ContDiff ℝ ∞ Ψ) (ξ : Pt 2) (n : Fin 2 → ℤ) (i : Fin 2)
    (y : Pt 2) :
    pd i (fun y => Complex.exp (2 * π * Complex.I *
        ((dot ξ (Ψ y - y) - dot (intVec n) y : ℝ) : ℂ))) y =
      2 * π * Complex.I * (ngrad Ψ ξ n i y : ℂ) *
        Complex.exp (2 * π * Complex.I * ((dot ξ (Ψ y - y) - dot (intVec n) y : ℝ) : ℂ)) := by
  obtain ⟨hφ, hpd⟩ := pd_phase_real Ψ hΨ ξ n y
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp y hφ).const_mul (2 * π * Complex.I)).cexp
  have h' : HasFDerivAt (fun y => Complex.exp (2 * π * Complex.I *
      ((dot ξ (Ψ y - y) - dot (intVec n) y : ℝ) : ℂ))) _ y := h
  unfold pd at hpd ⊢
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Function.comp_apply]
  rw [hpd i]; ring

/-- The pointwise non-stationary phase bound `|c_n| ≤ C ρ^{-J}`. -/
lemma coeff_decay (a : ℝ) (ha : 0 < a) (K : ℕ → ℝ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Ψ : Pt 2 → Pt 2, ContDiff ℝ ∞ Ψ → IsLift Ψ →
      (∀ y, ∀ e : Pt 2, euclNorm e = 1 → 4 * a ≤ euclNorm ((jac Ψ y)ᵀ *ᵥ e)) →
      (∀ y, ∀ k, 1 ≤ k → k ≤ J + 1 → ‖iteratedFDeriv ℝ k Ψ y‖ ≤ K k) →
      ∀ e : Pt 2, euclNorm e = 1 → ∀ ρ : ℝ, 1 ≤ ρ → ∀ n : Fin 2 → ℤ,
      euclNorm (ρ • e + intVec n) ≤ a * ρ → ‖coeffC Ψ (ρ • e) n‖ ≤ C / ρ ^ J := by
  obtain ⟨CW, hCW0, hW⟩ := nW_bounds a ha K J
  refine ⟨(2 ^ (J + 2) * CW) ^ J, by positivity,
    fun Ψ hΨ hlift hlow hbd e he ρ hρ n hn => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨hWs, hWp, hWV, hWB⟩ := hW Ψ hΨ hlift hlow hbd e he ρ hρ n hn
  set W := nW Ψ (ρ • e) n with hWdef
  set E : Pt 2 → ℂ := fun y => Complex.exp (2 * π * Complex.I *
    ((dot (ρ • e) (Ψ y - y) - dot (intVec n) y : ℝ) : ℂ)) with hEdef
  have hEs : ContDiff ℝ ∞ E := by
    have h1 : ContDiff ℝ ∞ fun y : Pt 2 => dot (ρ • e) (Ψ y - y) - dot (intVec n) y := by
      unfold dot
      refine (ContDiff.sum fun i _ => contDiff_const.mul
        ((contDiff_apply ℝ ℝ i).comp (hΨ.sub contDiff_id))).sub
        (ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i))
    exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1))
  have hEp : IsPeriodic E := by
    intro y m
    have h := isPeriodic_scPhase ρ e hlift y m
    have h2 := isPeriodic_expChar (-n) y m
    have hE' : ∀ x, E x = scPhase ρ e Ψ x * expChar (intVec (-n)) x := by
      intro x
      simp only [hEdef, scPhase, expChar, ← Complex.exp_add]
      congr 1
      have : dot (intVec (-n)) x = -dot (intVec n) x := by
        simp [dot, intVec, Finset.sum_neg_distrib]
      rw [this]; push_cast; ring
    rw [hE', hE', h, h2]
  have hdE : ∀ i y, pd i E y = 2 * π * Complex.I * (ngrad Ψ (ρ • e) n i y : ℂ) * E y :=
    fun i y => pd_phase Ψ hΨ (ρ • e) n i y
  have hreg : ∀ s, ContDiff ℝ ∞ ((ibpOp W)^[s] (fun _ => 1)) ∧
      IsPeriodic ((ibpOp W)^[s] (fun _ => 1)) := by
    intro s
    induction s with
    | zero => exact ⟨contDiff_const, fun _ _ => rfl⟩
    | succ s ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ibpOp_contDiff W _ hWs ih.1, ibpOp_periodic W _ hWp ih.2⟩
  have hiter : ∀ s, ∫ y in cell 2, E y =
      ∫ y in cell 2, (ibpOp W)^[s] (fun _ => 1) y * E y := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [ih, Function.iterate_succ_apply']
      exact ibp_identity E _ W (fun i y => (ngrad Ψ (ρ • e) n i y : ℂ)) hEs hEp (hreg s).1
        (hreg s).2 hWs hWp hdE hWV
  have hB : SymBd 0 ((2 ^ (J + 2) * (CW / ρ)) ^ J) ((ibpOp W)^[J] (fun _ => 1)) := by
    have := (ibpOp_iter_symBd W hWs J (CW / ρ) (by positivity) hWB J le_rfl).2
    simpa using this
  have hcoef : coeffC Ψ (ρ • e) n = ∫ y in cell 2, E y := rfl
  rw [hcoef, hiter J]
  have hμ : ((volume : Measure (Pt 2)).restrict (cell 2)).real univ = 1 := by
    simp [Measure.real, volume_cell_two]
  haveI : IsFiniteMeasure ((volume : Measure (Pt 2)).restrict (cell 2)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_cell_two]; simp⟩
  have hbound := norm_integral_le_of_norm_le_const
    (μ := (volume : Measure (Pt 2)).restrict (cell 2))
    (C := (2 ^ (J + 2) * (CW / ρ)) ^ J)
    (f := fun y => (ibpOp W)^[J] (fun _ => 1) y * E y)
    (Filter.Eventually.of_forall fun y => by
      rw [norm_mul]
      have hEn : ‖E y‖ = 1 := by
        simp only [hEdef, Complex.norm_exp]; simp
      rw [hEn, mul_one]
      have := hB 0 le_rfl y
      rwa [norm_iteratedFDeriv_zero] at this)
  rw [hμ, mul_one] at hbound
  refine hbound.trans (le_of_eq ?_)
  rw [mul_div_assoc', div_pow]

/-- Lattice point count: at most `(2aρ + 1)²` integer vectors with `|ξ + n| ≤ aρ`. -/
lemma lattice_count (ξ : Pt 2) (r : ℝ) (hr : 0 ≤ r) :
    ∃ S : Finset (Fin 2 → ℤ), (∀ n, euclNorm (ξ + intVec n) ≤ r → n ∈ S) ∧
      (S.card : ℝ) ≤ (2 * r + 1) ^ 2 := by
  refine ⟨Finset.Icc (fun i => ⌈-ξ i - r⌉) (fun i => ⌊-ξ i + r⌋), fun n hn => ?_, ?_⟩
  · have hc : ∀ i, |ξ i + n i| ≤ r := by
      intro i
      refine le_trans ?_ hn
      unfold euclNorm
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      have := Finset.single_le_sum (f := fun j => (ξ + intVec n) j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      simpa [intVec] using this
    rw [Finset.mem_Icc]
    constructor
    · intro i; have := abs_le.1 (hc i); exact Int.ceil_le.2 (by linarith)
    · intro i; have := abs_le.1 (hc i); exact Int.le_floor.2 (by linarith)
  · rw [Pi.card_Icc, Fin.prod_univ_two, Nat.cast_mul, sq]
    have hb : ∀ i, ((Finset.Icc ⌈-ξ i - r⌉ ⌊-ξ i + r⌋).card : ℝ) ≤ 2 * r + 1 := by
      intro i
      rw [Int.card_Icc]
      rcases le_or_gt 0 (⌊-ξ i + r⌋ + 1 - ⌈-ξ i - r⌉) with h | h
      · rw [show (((⌊-ξ i + r⌋ + 1 - ⌈-ξ i - r⌉).toNat : ℕ) : ℝ)
          = ((⌊-ξ i + r⌋ + 1 - ⌈-ξ i - r⌉ : ℤ) : ℝ) by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg h]]
        push_cast
        have := Int.floor_le (-ξ i + r); have := Int.le_ceil (-ξ i - r)
        linarith
      · rw [Int.toNat_of_nonpos h.le]; simp; linarith
    exact mul_le_mul (hb 0) (hb 1) (by positivity) (by linarith)

theorem nonstationary_low_output_core (a : ℝ) (ha : 0 < a) (K : ℕ → ℝ) (J : ℕ) :
    ∃ C : ℝ, ∀ Ψ : Pt 2 → Pt 2, ContDiff ℝ ∞ Ψ → IsLift Ψ →
      (∀ y, ∀ e : Pt 2, euclNorm e = 1 → 4 * a ≤ euclNorm ((jac Ψ y)ᵀ *ᵥ e)) →
      (∀ y, ∀ k, 1 ≤ k → k ≤ J + 1 → ‖iteratedFDeriv ℝ k Ψ y‖ ≤ K k) →
      ∀ e : Pt 2, euclNorm e = 1 → ∀ ρ : ℝ, 1 ≤ ρ →
      (∑' n, if euclNorm (ρ • e + intVec n) ≤ a * ρ then ‖coeffC Ψ (ρ • e) n‖ ^ 2 else 0)
        ≤ C * ρ ^ (2 - 2 * (J : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := coeff_decay a ha K J
  refine ⟨C ^ 2 * (2 * a + 1) ^ 2, fun Ψ hΨ hlift hlow hbd e he ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨S, hS, hcard⟩ := lattice_count (ρ • e) (a * ρ) (by positivity)
  set F : (Fin 2 → ℤ) → ℝ := fun n =>
    if euclNorm (ρ • e + intVec n) ≤ a * ρ then ‖coeffC Ψ (ρ • e) n‖ ^ 2 else 0 with hF
  have hsupp : ∀ n ∉ S, F n = 0 := by
    intro n hn
    simp only [hF]
    rw [if_neg]
    exact fun h => hn (hS n h)
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ n ∈ S, F n ≤ (C / ρ ^ J) ^ 2 := by
    intro n _
    simp only [hF]
    split_ifs with h
    · exact pow_le_pow_left₀ (norm_nonneg _) (hC Ψ hΨ hlift hlow hbd e he ρ hρ n h) 2
    · positivity
  calc ∑ n ∈ S, F n ≤ ∑ n ∈ S, (C / ρ ^ J) ^ 2 := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (C / ρ ^ J) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (a * ρ) + 1) ^ 2 * (C / ρ ^ J) ^ 2 := by gcongr
    _ ≤ ((2 * a + 1) * ρ) ^ 2 * (C / ρ ^ J) ^ 2 := by gcongr; nlinarith
    _ = C ^ 2 * (2 * a + 1) ^ 2 * (ρ ^ 2 / (ρ ^ J) ^ 2) := by
        field_simp
    _ = C ^ 2 * (2 * a + 1) ^ 2 * ρ ^ (2 - 2 * (J : ℝ)) := by
        congr 1
        rw [Real.rpow_sub hρ0, ← pow_mul]
        norm_cast
        rw [mul_comm J 2]

end AnomDiss
