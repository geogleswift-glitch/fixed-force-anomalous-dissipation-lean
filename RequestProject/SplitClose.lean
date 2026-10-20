module

public import RequestProject.SplitStoch
public import RequestProject.FlowStab
public import RequestProject.SplitNegMoment

/-!
# Closeness of the split maps to the terminal flow map (derivative part of Lemma 3.9)

For every `x`, `𝔼_ζ ‖DΨ_n(x) - DΨ₀(x)‖ ≤ C √μ`, uniformly in `μ ∈ [0,1]`, `ω` and `n ≥ 1`.
The deviation splits into a stochastic part (the Gaussian increments, controlled in mean square)
and a deterministic part (the damping, controlled by `C¹` stability of flows).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {L M : ℕ} {S : ℕ → ℝ}

lemma dampedCoef_zero (cf : ControlFamily L M S) (w : BlockParam L) (s : ℝ) :
    dampedCoef cf 0 w s = cf.coef w.1 s := by
  simp [dampedCoef]

lemma norm_dampedCoef_sub_coef_le (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖dampedCoef cf μ w s - cf.coef w.1 s‖ ≤ μ * coefBound cf := by
  unfold dampedCoef
  have hint : ‖∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r‖ ≤
      coefBound cf * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    rw [uIoc_of_le hs.1] at hr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-μ * (s - r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hμ.1, hr.2])
    calc Real.exp (-μ * (s - r)) * ‖cf.coef w.1 r‖ ≤ 1 * coefBound cf := by
          gcongr
          · exact norm_coef_le cf w.1 r
      _ = coefBound cf := one_mul _
  have hs0 : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1]
  have := coefBound_nonneg cf
  calc μ * ‖∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r‖
      ≤ μ * (coefBound cf * 1) :=
        mul_le_mul_of_nonneg_left (hint.trans (by gcongr)) hμ.1
    _ = μ * coefBound cf := by ring

lemma splitField_sub_zero (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ) :
    (fun y => splitField cf μ w s y - splitField cf 0 w s y) =
      fun y => eField (dampedCoef cf μ w (clamp01 s) - cf.coef w.1 (clamp01 s)) (y - w.2) := by
  funext y
  rw [splitField_apply, splitField_apply, eField_sub_coef, dampedCoef_zero]

lemma norm_splitField_sub_zero_le (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (s : ℝ) (y : Pt 2) :
    ‖splitField cf μ w s y - splitField cf 0 w s y‖ ≤ 2 * (μ * coefBound cf) := by
  have := congrFun (splitField_sub_zero cf μ w s) y
  rw [this]
  exact (norm_eField_le _ _).trans
    (by gcongr; exact norm_dampedCoef_sub_coef_le cf hμ w (clamp01_mem s))

lemma norm_fderiv_splitField_sub_zero_le (cf : ControlFamily L M S) {μ : ℝ}
    (hμ : μ ∈ Icc (0 : ℝ) 1) (w : BlockParam L) (s : ℝ) (y : Pt 2) :
    ‖fderiv ℝ (splitField cf μ w s) y - fderiv ℝ (splitField cf 0 w s) y‖ ≤
      4 * π * (μ * coefBound cf) := by
  have hμ0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 := (splitField_C2 cf hμ w).differentiable0 s
  have h2 := (splitField_C2 cf hμ0 w).differentiable0 s
  rw [← fderiv_sub (h1 y) (h2 y)]
  have e : (splitField cf μ w s - splitField cf 0 w s) =
      fun y => splitField cf μ w s y - splitField cf 0 w s y := rfl
  rw [e, splitField_sub_zero]
  set c := dampedCoef cf μ w (clamp01 s) - cf.coef w.1 (clamp01 s)
  have hc : ‖c‖ ≤ μ * coefBound cf := norm_dampedCoef_sub_coef_le cf hμ w (clamp01_mem s)
  have hC0 : 0 ≤ 4 * π * (μ * coefBound cf) := by
    have := coefBound_nonneg cf; have := hμ.1; positivity
  refine norm_fderiv_le_of_lip' ℝ hC0 (Eventually.of_forall fun x => ?_)
  refine (norm_eField_sub_le c _ _).trans ?_
  rw [show x - w.2 - (y - w.2) = x - y by abel]
  gcongr

/-- The inverse terminal flow map is the backward flow of the undamped splitting field. -/
lemma termInv_eq_gflow (cf : ControlFamily L M S) (w : BlockParam L) :
    termInv w = gflow (splitField cf 0 w) 1 0 := by
  have hμ0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hS := splitField_good cf hμ0 w
  obtain ⟨Φ, hΦ0, hΦd, hΦ1⟩ := termInv_isInverseFlowMap cf w
  have hB : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, bField cf w s x = splitField cf 0 w s x := fun s hs x => by
    rw [splitField_eq_of_mem cf 0 w hs]; simp [dampedB]
  have hΦS : ∀ x, Φ 1 x = gflow (splitField cf 0 w) 0 1 x := fun x => by
    refine hS.eqOn_Icc (α := fun s => Φ s x) (β := fun s => gflow (splitField cf 0 w) 0 s x)
      (left_mem_Icc.2 zero_le_one) (fun s hs => ?_) (fun s _ => ?_)
      (by simp only [hΦ0, hS.gflow_self]) (right_mem_Icc.2 zero_le_one)
    · have := (hΦd s x).hasDerivWithinAt (s := Icc 0 1)
      rwa [hB s hs] at this
    · exact (hS.hasDerivAt_gflow 0 s x).hasDerivWithinAt
  funext y
  have h := (hΦ1 (gflow (splitField cf 0 w) 1 0 y)).1
  rwa [hΦS, hS.gflow_inv] at h

/-- With all increments zero, the composition of the canonical steps is the backward flow. -/
lemma splitMap_canonPsi_zero (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (n : ℕ) (j : ℕ) :
    splitMap (canonPsi cf μ w n) 0 j = gflow (splitField cf μ w) ((j : ℝ) / n) 0 := by
  have hS := splitField_good cf hμ w
  induction j with
  | zero => funext x; simp [splitMap, hS.gflow_self]
  | succ j ih =>
    funext x
    rw [splitMap_succ, ih, Pi.zero_apply, add_zero, canonPsi,
      show (((j + 1 : ℕ) : ℝ) - 1) / n = (j : ℝ) / n by push_cast; ring, hS.gflow_gflow]

lemma splitMap_canonPsi_zero_n (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {n : ℕ} (hn : 1 ≤ n) :
    splitMap (canonPsi cf μ w n) 0 n = gflow (splitField cf μ w) 1 0 := by
  rw [splitMap_canonPsi_zero cf hμ w n n, div_self (by positivity)]

/-- Step estimates for the canonical maps, in the form used for the stochastic comparison. -/
lemma canonPsi_step_bounds (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) :
    Differentiable ℝ (canonPsi cf μ w n i) ∧
    (∀ y u, euclNorm (canonPsi cf μ w n i (y + u) - canonPsi cf μ w n i y) ≤
      (1 + 2 * (splitK cf * Real.exp (splitK cf)) / n) * euclNorm u) ∧
    (∀ y, ‖fderiv ℝ (canonPsi cf μ w n i) y‖ ≤ 1 + splitK cf * Real.exp (splitK cf) / n) ∧
    (∀ y z, ‖fderiv ℝ (canonPsi cf μ w n i) y - fderiv ℝ (canonPsi cf μ w n i) z‖ ≤
      splitK2 cf * Real.exp (3 * splitK cf) / n * ‖y - z‖) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : |((i : ℝ) - 1) / n - (i : ℝ) / n| = 1 / n := by
    rw [← sub_div, abs_div, abs_of_pos hn0]; norm_num
  obtain ⟨hc, hb⟩ := splitFlow_step cf hμ w hn habs
  obtain ⟨-, hb'⟩ := gflow_C2 (splitField_good cf hμ w) (splitField_C2 cf hμ w)
    ((i : ℝ) / n) (((i : ℝ) - 1) / n)
  set a := splitK cf * Real.exp (splitK cf) with ha
  have hK := NNReal.coe_nonneg (splitK cf)
  have hn1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hn
  have hid : ∀ y, ‖fderiv ℝ (canonPsi cf μ w n i) y - ContinuousLinearMap.id ℝ (Pt 2)‖ ≤
      a / n := fun y => by
    have h := (hb' y).1
    rw [habs] at h
    refine h.trans ?_
    have e1 : Real.exp (splitK cf * (1 / n)) ≤ Real.exp (splitK cf) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc splitK cf * (1 / n) * Real.exp (splitK cf * (1 / n))
        ≤ splitK cf * (1 / n) * Real.exp (splitK cf) := by gcongr
      _ = a / n := by rw [ha]; ring
  have hd : Differentiable ℝ (canonPsi cf μ w n i) := hc.differentiable (by norm_num)
  refine ⟨hd, fun y u => ?_, fun y => (hb y).1, fun y z => ?_⟩
  · set h : Pt 2 → Pt 2 := fun z => canonPsi cf μ w n i z - z with hh
    have hhd : Differentiable ℝ h := hd.sub differentiable_id
    have hfd : ∀ z, ‖fderiv ℝ h z‖ ≤ a / n := fun z => by
      have e : (fun z => canonPsi cf μ w n i z - z) = canonPsi cf μ w n i - id := rfl
      rw [hh, e, fderiv_sub (hd z) differentiableAt_id, fderiv_id]
      exact hid z
    have h1 := norm_sub_le_of_fderiv_le hhd hfd y (y + u)
    rw [add_sub_cancel_left] at h1
    have e : canonPsi cf μ w n i (y + u) - canonPsi cf μ w n i y = u + (h (y + u) - h y) := by
      simp only [hh]; abel
    rw [e]
    have ha0 : 0 ≤ a / n := by positivity
    calc euclNorm (u + (h (y + u) - h y)) ≤ euclNorm u + euclNorm (h (y + u) - h y) :=
          euclNorm_add_le _ _
      _ ≤ euclNorm u + 2 * (a / n * ‖u‖) := by
          gcongr; exact (euclNorm_le _).trans (by gcongr)
      _ ≤ euclNorm u + 2 * (a / n * euclNorm u) := by
          gcongr; exact norm_le_euclNorm u
      _ = (1 + 2 * a / n) * euclNorm u := by ring
  · rw [norm_sub_rev]
    have := norm_sub_le_of_fderiv_le ((hc.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) (fun x => (hb x).2) y z
    rwa [norm_sub_rev z y] at this

lemma natCast_mul_splitVar_le {μ : ℝ} (hμ : 0 ≤ μ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (splitVar μ n : ℝ) ≤ μ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold splitVar
  rw [Real.coe_toNNReal _ (by positivity)]
  have hπ : 1 ≤ 2 * π ^ 2 := by nlinarith [Real.pi_gt_three]
  rw [show (n : ℝ) * (2 * (μ / (4 * π ^ 2)) / n) = μ / (2 * π ^ 2) by field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Lemma 3.9, derivative part, pointwise in `x`**: `𝔼_ζ ‖DΨ_n(x) - DΨ₀(x)‖ ≤ C √μ`. -/
theorem split_deriv_closeness (cf : ControlFamily L M S) :
    ∃ C : ℝ, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ (w : BlockParam L) (n : ℕ), 1 ≤ n → ∀ x : Pt 2,
      ∫⁻ ζ, ‖fderiv ℝ (splitMap (canonPsi cf μ w n) ζ n) x - fderiv ℝ (termInv w) x‖ₑ
        ∂(gaussSeq (splitVar μ n)) ≤ ENNReal.ofReal (C * Real.sqrt μ) := by
  set K : ℝ := (splitK cf : ℝ) with hKdef
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  set a : ℝ := K * Real.exp K with ha
  set b : ℝ := splitK2 cf * Real.exp (3 * K) with hb
  have hCb := coefBound_nonneg cf
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by
    have : 0 ≤ splitK2 cf := by unfold splitK2; positivity
    positivity
  set C1 : ℝ := Real.exp a * b * Real.sqrt (Real.exp (4 * a) * 2) with hC1
  set C2 : ℝ := (splitK2 cf * (2 * coefBound cf) * Real.exp K + 4 * π * coefBound cf) *
    Real.exp K * Real.exp K with hC2
  refine ⟨C1 + C2, fun μ hμ w n hn x => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set v := splitVar μ n
  set ψ := canonPsi cf μ w n
  -- stochastic part
  have hstep := canonPsi_step_bounds cf hμ w hn
  have hp : 1 ≤ 1 + a / n := by have : 0 ≤ a / n := by positivity
                                linarith
  have hρ : 1 ≤ 1 + 2 * a / n := by have : 0 ≤ 2 * a / n := by positivity
                                    linarith
  have hst := lintegral_fderiv_splitMap_sub_le (ψ := ψ) n v hp (by positivity : 0 ≤ b / n) hρ
    (fun i => (hstep i).1) (fun i => (hstep i).2.1) (fun i => (hstep i).2.2.1)
    (fun i => (hstep i).2.2.2) x
  have hpn : (1 + a / n) ^ n ≤ Real.exp a := one_add_div_pow_le_exp' ha0 hn
  have hρn : (1 + 2 * a / n) ^ n ≤ Real.exp (2 * a) :=
    one_add_div_pow_le_exp' (by positivity) hn
  have hρ2n : (1 + 2 * a / n) ^ (2 * n) ≤ Real.exp (4 * a) := by
    rw [pow_mul', show 4 * a = 2 * a + 2 * a by ring, Real.exp_add, sq]
    exact mul_le_mul hρn hρn (by positivity) (by positivity)
  have hnv := natCast_mul_splitVar_le hμ.1 hn
  have hv0 : (0 : ℝ) ≤ v := v.2
  have hS : (1 + a / n) ^ n * (b / n) * n * Real.sqrt (n * (1 + 2 * a / n) ^ (2 * n) * (2 * v))
      ≤ C1 * Real.sqrt μ := by
    have e1 : (1 + a / n) ^ n * (b / n) * n = (1 + a / n) ^ n * b := by field_simp
    rw [e1, hC1, mul_assoc (Real.exp a * b), ← Real.sqrt_mul (by positivity)]
    have h2 : (n : ℝ) * (1 + 2 * a / n) ^ (2 * n) * (2 * v) ≤ Real.exp (4 * a) * 2 * μ := by
      have : (n : ℝ) * (1 + 2 * a / n) ^ (2 * n) * (2 * v) =
          (1 + 2 * a / n) ^ (2 * n) * 2 * (n * v) := by ring
      rw [this]
      have h0 : 0 ≤ (n : ℝ) * v := by positivity
      gcongr
    gcongr
  -- deterministic part
  have hdet : ‖fderiv ℝ (splitMap ψ 0 n) x - fderiv ℝ (termInv w) x‖ ≤ C2 * μ := by
    rw [splitMap_canonPsi_zero_n cf hμ w hn, termInv_eq_gflow cf w]
    have h := norm_fderiv_gflow_sub_le (splitField_good cf hμ w) (splitField_C2 cf hμ w)
      (splitField_good cf hμ0 w) (splitField_C2 cf hμ0 w) (norm_splitField_sub_zero_le cf hμ w)
      (norm_fderiv_splitField_sub_zero_le cf hμ w) 1 0 x
    rw [show |(0 : ℝ) - 1| = 1 by norm_num] at h
    refine h.trans (le_of_eq ?_)
    rw [hC2, hKdef]; ring_nf
  have hsq : μ ≤ Real.sqrt μ := by
    have h1 : Real.sqrt μ ≤ 1 := Real.sqrt_le_one.2 hμ.2
    have h2 := Real.sq_sqrt hμ.1
    nlinarith [Real.sqrt_nonneg μ]
  have hC2' : 0 ≤ C2 := by
    have : 0 ≤ splitK2 cf := by unfold splitK2; positivity
    positivity
  calc ∫⁻ ζ, ‖fderiv ℝ (splitMap ψ ζ n) x - fderiv ℝ (termInv w) x‖ₑ ∂(gaussSeq v)
      ≤ ∫⁻ ζ, (‖fderiv ℝ (splitMap ψ ζ n) x - fderiv ℝ (splitMap ψ 0 n) x‖ₑ +
          ENNReal.ofReal (C2 * μ)) ∂(gaussSeq v) := by
        refine lintegral_mono fun ζ => ?_
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        exact (ENNReal.ofReal_le_ofReal (norm_sub_le_norm_sub_add_norm_sub _ _ _)).trans
          (ENNReal.ofReal_add_le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hdet)))
    _ = ∫⁻ ζ, ‖fderiv ℝ (splitMap ψ ζ n) x - fderiv ℝ (splitMap ψ 0 n) x‖ₑ ∂(gaussSeq v) +
          ENNReal.ofReal (C2 * μ) := by
        rw [lintegral_add_right _ measurable_const]
        simp
    _ ≤ ENNReal.ofReal (C1 * Real.sqrt μ) + ENNReal.ofReal (C2 * Real.sqrt μ) := by
        gcongr
        exact hst.trans (ENNReal.ofReal_le_ofReal hS)
    _ = ENNReal.ofReal ((C1 + C2) * Real.sqrt μ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

end AnomDiss
