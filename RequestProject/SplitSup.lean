module

public import RequestProject.SplitRepFull
public import RequestProject.SplitFourierBound

/-!
# Lemma 3.9 (closeness of the split maps), with the supremum inside the expectation

Following the paper, the displacement of the random composition `Ψ_n` from the deterministic one
is compared with the running sum `S_m` of the Gaussian increments, which does not depend on the
starting point `x`.  A discrete Gronwall argument bounds the remainder pathwise and uniformly in
`x` by averages of `|S_j|`, and `𝔼|S_j| ≤ √(2 j v) ≤ √(2μ)`.  The damping is handled by the
`C⁰` and `C¹` stability of flows.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- The running sum `S_m = ζ_n + ζ_{n-1} + ⋯ + ζ_{n-m+1}` of the increments. -/
def tailSum (ζ : ℕ → Pt 2) (n m : ℕ) : Pt 2 := ∑ j ∈ Finset.range m, ζ (n - j)

lemma tailSum_succ (ζ : ℕ → Pt 2) (n m : ℕ) :
    tailSum ζ n (m + 1) = tailSum ζ n m + ζ (n - m) := by
  simp [tailSum, Finset.sum_range_succ]

lemma continuous_tailSum (n m : ℕ) : Continuous fun ζ : ℕ → Pt 2 => tailSum ζ n m := by
  unfold tailSum
  exact continuous_finset_sum _ fun j _ => continuous_apply _

lemma continuous_euclNorm2 : Continuous (euclNorm : Pt 2 → ℝ) := by
  unfold euclNorm; fun_prop

section Pathwise

variable {ψ : ℕ → Pt 2 → Pt 2} {c : ℝ}

/-- Pathwise discrete Gronwall bound: the displacement minus the running sum of the increments. -/
theorem tailDsp_sub_tailSum_le (n : ℕ) (hc : 0 ≤ c)
    (hE : ∀ i y u, euclNorm (ψ i (y + u) - ψ i y - u) ≤ c * euclNorm u) (x : Pt 2)
    (ζ : ℕ → Pt 2) (m : ℕ) :
    euclNorm (tailDsp ψ n m x ζ - tailSum ζ n m) ≤
      (1 + c) ^ m * c * ∑ j ∈ Finset.range m, euclNorm (tailSum ζ n (j + 1)) := by
  induction m with
  | zero => simp [tailDsp, tailSum, tailMap, euclNorm]
  | succ m ih =>
    have e : tailDsp ψ n (m + 1) x ζ - tailSum ζ n (m + 1) =
        (ψ (n - m) (tailMap ψ 0 n m x + (tailDsp ψ n m x ζ + ζ (n - m))) -
          ψ (n - m) (tailMap ψ 0 n m x) - (tailDsp ψ n m x ζ + ζ (n - m))) +
          (tailDsp ψ n m x ζ - tailSum ζ n m) := by
      rw [tailDsp_succ, tailSum_succ]; abel
    have eu : tailDsp ψ n m x ζ + ζ (n - m) =
        (tailDsp ψ n m x ζ - tailSum ζ n m) + tailSum ζ n (m + 1) := by
      rw [tailSum_succ]; abel
    have hu : euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) ≤
        euclNorm (tailDsp ψ n m x ζ - tailSum ζ n m) + euclNorm (tailSum ζ n (m + 1)) := by
      rw [eu]; exact euclNorm_add_le _ _
    have hsm0 : 0 ≤ ∑ j ∈ Finset.range m, euclNorm (tailSum ζ n (j + 1)) :=
      Finset.sum_nonneg fun _ _ => euclNorm_nonneg _
    have hs0 := euclNorm_nonneg (tailSum ζ n (m + 1))
    have hE0 := euclNorm_nonneg (tailDsp ψ n m x ζ - tailSum ζ n m)
    have hpow : 1 ≤ (1 + c) ^ m := one_le_pow₀ (by linarith)
    have h1 := hE (n - m) (tailMap ψ 0 n m x) (tailDsp ψ n m x ζ + ζ (n - m))
    rw [e, Finset.sum_range_succ, pow_succ]
    refine (euclNorm_add_le _ _).trans ?_
    have hcu := mul_le_mul_of_nonneg_left hu hc
    have hcs : c * euclNorm (tailSum ζ n (m + 1)) ≤
        (1 + c) ^ m * (1 + c) * c * euclNorm (tailSum ζ n (m + 1)) := by
      have : 1 ≤ (1 + c) ^ m * (1 + c) := by nlinarith
      nlinarith [mul_nonneg hc hs0]
    have hih := mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ 1 + c)
    nlinarith

end Pathwise

section Moments

variable (v : ℝ≥0)

lemma tailSum_update (n : ℕ) {m : ℕ} (hm : m ≤ n) (ζ : ℕ → Pt 2) (z : Pt 2) :
    tailSum (Function.update ζ (n - m) z) n m = tailSum ζ n m := by
  unfold tailSum
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Function.update_of_ne (by omega)]

lemma lintegral_euclNorm_tailSum_sq (n : ℕ) :
    ∀ m ≤ n, ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailSum ζ n m) ^ 2) ∂(gaussSeq v) =
      ENNReal.ofReal (m * (2 * v)) := by
  intro m
  induction m with
  | zero => intro _; simp [tailSum, euclNorm]
  | succ m ih =>
    intro hm
    simp_rw [tailSum_succ]
    rw [lintegral_euclNorm_sq_add_coord v (n - m) (continuous_tailSum n m).measurable
      (fun ζ z => tailSum_update n (by omega) ζ z), ih (by omega),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; push_cast; ring

lemma lintegral_euclNorm_tailSum_le (n : ℕ) {m : ℕ} (hm : m ≤ n) :
    ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailSum ζ n m)) ∂(gaussSeq v) ≤
      ENNReal.ofReal (Real.sqrt (n * (2 * v))) := by
  refine (lintegral_ofReal_le_sqrt _ (continuous_euclNorm2.comp
    (continuous_tailSum n m)).measurable (fun _ => euclNorm_nonneg _)
    (lintegral_euclNorm_tailSum_sq v n m hm).le).trans ?_
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
  have : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hv : (0 : ℝ) ≤ v := v.2
  nlinarith

/-- The pathwise gauge `G(ζ) = |S_n| + (1/n) ∑_{j<n} |S_{j+1}|`. -/
def sumGauge (ζ : ℕ → Pt 2) (n : ℕ) : ℝ :=
  euclNorm (tailSum ζ n n) + (∑ j ∈ Finset.range n, euclNorm (tailSum ζ n (j + 1))) / n

lemma sumGauge_nonneg (ζ : ℕ → Pt 2) (n : ℕ) : 0 ≤ sumGauge ζ n :=
  add_nonneg (euclNorm_nonneg _) (div_nonneg (Finset.sum_nonneg fun _ _ => euclNorm_nonneg _)
    (Nat.cast_nonneg n))

lemma measurable_sumGauge (n : ℕ) : Measurable fun ζ : ℕ → Pt 2 => sumGauge ζ n := by
  unfold sumGauge
  refine Continuous.measurable ?_
  refine (continuous_euclNorm2.comp (continuous_tailSum n n)).add ?_
  exact (continuous_finset_sum _ fun j _ =>
    continuous_euclNorm2.comp (continuous_tailSum n (j + 1))).div_const _

lemma lintegral_sumGauge_le (n : ℕ) :
    ∫⁻ ζ, ENNReal.ofReal (sumGauge ζ n) ∂(gaussSeq v) ≤
      ENNReal.ofReal (2 * Real.sqrt (n * (2 * v))) := by
  set B := Real.sqrt (n * (2 * v))
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hm : ∀ m, Measurable fun ζ : ℕ → Pt 2 => ENNReal.ofReal (euclNorm (tailSum ζ n m)) :=
    fun m => ENNReal.measurable_ofReal.comp
      (continuous_euclNorm2.comp (continuous_tailSum n m)).measurable
  have hpt : ∀ ζ, ENNReal.ofReal (sumGauge ζ n) = ENNReal.ofReal (euclNorm (tailSum ζ n n)) +
      ENNReal.ofReal (1 / (n : ℝ)) *
        ∑ j ∈ Finset.range n, ENNReal.ofReal (euclNorm (tailSum ζ n (j + 1))) := fun ζ => by
    unfold sumGauge
    rw [ENNReal.ofReal_add (euclNorm_nonneg _) (by
      have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range n) =>
        euclNorm_nonneg (tailSum ζ n (j + 1))
      positivity), div_eq_mul_one_div, mul_comm,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
        (fun j _ => euclNorm_nonneg _)]
  simp_rw [hpt]
  rw [lintegral_add_left (hm n), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finset_sum _ (fun j _ => hm (j + 1))]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [tailSum, euclNorm]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
  calc ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailSum ζ n n)) ∂(gaussSeq v) +
        ENNReal.ofReal (1 / (n : ℝ)) * ∑ j ∈ Finset.range n,
          ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailSum ζ n (j + 1))) ∂(gaussSeq v)
      ≤ ENNReal.ofReal B + ENNReal.ofReal (1 / (n : ℝ)) *
          ∑ j ∈ Finset.range n, ENNReal.ofReal B := by
        gcongr with j hj
        · exact lintegral_euclNorm_tailSum_le v n le_rfl
        · exact lintegral_euclNorm_tailSum_le v n (by rw [Finset.mem_range] at hj; omega)
    _ = ENNReal.ofReal (2 * B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add hB (by positivity)]
        congr 1; field_simp; ring

end Moments

variable {L M : ℕ} {S : ℕ → ℝ}

/-- Each canonical step is a perturbation of the identity of size `O(1/n)` in Lipschitz norm. -/
lemma canonPsi_near_id (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (y u : Pt 2) :
    euclNorm (canonPsi cf μ w n i (y + u) - canonPsi cf μ w n i y - u) ≤
      2 * (splitK cf * Real.exp (splitK cf)) / n * euclNorm u := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have habs : |((i : ℝ) - 1) / n - (i : ℝ) / n| = 1 / n := by
    rw [← sub_div, abs_div, abs_of_pos hn0]; norm_num
  obtain ⟨hc, hb⟩ := splitFlow_step cf hμ w hn habs
  obtain ⟨-, hb'⟩ := gflow_C2 (splitField_good cf hμ w) (splitField_C2 cf hμ w)
    ((i : ℝ) / n) (((i : ℝ) - 1) / n)
  set a := splitK cf * Real.exp (splitK cf) with ha
  have hK := NNReal.coe_nonneg (splitK cf)
  have hid : ∀ y, ‖fderiv ℝ (canonPsi cf μ w n i) y - ContinuousLinearMap.id ℝ (Pt 2)‖ ≤
      a / n := fun y => by
    have h := (hb' y).1
    rw [habs] at h
    refine h.trans ?_
    have e1 : Real.exp (splitK cf * (1 / n)) ≤ Real.exp (splitK cf) :=
      Real.exp_le_exp.2 (by
        have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hn
        nlinarith)
    calc splitK cf * (1 / n) * Real.exp (splitK cf * (1 / n))
        ≤ splitK cf * (1 / n) * Real.exp (splitK cf) := by gcongr
      _ = a / n := by rw [ha]; ring
  have hd : Differentiable ℝ (canonPsi cf μ w n i) := hc.differentiable (by norm_num)
  set h : Pt 2 → Pt 2 := fun z => canonPsi cf μ w n i z - z with hh
  have hhd : Differentiable ℝ h := hd.sub differentiable_id
  have hfd : ∀ z, ‖fderiv ℝ h z‖ ≤ a / n := fun z => by
    have e : (fun z => canonPsi cf μ w n i z - z) = canonPsi cf μ w n i - id := rfl
    rw [hh, e, fderiv_sub (hd z) differentiableAt_id, fderiv_id]
    exact hid z
  have h1 := norm_sub_le_of_fderiv_le hhd hfd y (y + u)
  rw [add_sub_cancel_left] at h1
  have e : canonPsi cf μ w n i (y + u) - canonPsi cf μ w n i y - u = h (y + u) - h y := by
    simp only [hh]; abel
  rw [e]
  have ha0 : 0 ≤ a / n := by positivity
  calc euclNorm (h (y + u) - h y) ≤ 2 * ‖h (y + u) - h y‖ := euclNorm_le _
    _ ≤ 2 * (a / n * ‖u‖) := by gcongr
    _ ≤ 2 * (a / n * euclNorm u) := by gcongr; exact norm_le_euclNorm u
    _ = 2 * a / n * euclNorm u := by ring

/-- Any inverse terminal flow map of `b_ω` is the backward flow of the undamped splitting field. -/
lemma isInverseFlowMap_bField_eq (cf : ControlFamily L M S) (w : BlockParam L)
    {Ψ₀ : Pt 2 → Pt 2} (hΨ₀ : IsInverseFlowMap (bField cf w) 0 1 Ψ₀) :
    Ψ₀ = gflow (splitField cf 0 w) 1 0 := by
  have hμ0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hS := splitField_good cf hμ0 w
  obtain ⟨Φ, hΦ0, hΦd, hΦ1⟩ := hΨ₀
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

/-- Any splitting of `B_{μ,ω}` agrees with the canonical one on the steps that are used. -/
lemma isSplitting_eq_canonPsi (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {n : ℕ} (hn : 1 ≤ n) {ψ : ℕ → Pt 2 → Pt 2}
    (hψ : IsSplitting (dampedB cf μ w) n ψ) :
    ∀ i, 1 ≤ i → i ≤ n → ψ i = canonPsi cf μ w n i := by
  intro i hi1 hin
  rw [isSplitting_eq cf hμ.1 w hψ i hi1 hin]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hin' : (i : ℝ) ≤ n := by exact_mod_cast hin
  funext x
  exact gflow_dampedB_eq cf hμ w ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).2 hin'⟩
    ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).2 (by linarith)⟩ x

/-- Pathwise, `x`-uniform bounds for the canonical splitting in terms of the gauge. -/
theorem canon_pathwise (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {n : ℕ} (hn : 1 ≤ n) (ζ : ℕ → Pt 2) (x : Pt 2) {K a b : ℝ}
    (hKd : K = (splitK cf : ℝ)) (ha : a = K * Real.exp K) (hb : b = splitK2 cf * Real.exp (3 * K)) :
    euclNorm (splitMap (canonPsi cf μ w n) ζ n x - splitMap (canonPsi cf μ w n) 0 n x) ≤
        (1 + 2 * a * Real.exp (2 * a)) * sumGauge ζ n ∧
      ‖fderiv ℝ (splitMap (canonPsi cf μ w n) ζ n) x -
          fderiv ℝ (splitMap (canonPsi cf μ w n) 0 n) x‖ ≤
        Real.exp a * b * (2 * a * Real.exp (2 * a) + 1) * sumGauge ζ n := by
  subst hKd ha hb
  set K : ℝ := (splitK cf : ℝ) with hKd
  set a : ℝ := K * Real.exp K with ha
  set b : ℝ := splitK2 cf * Real.exp (3 * K) with hb
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by
    have : 0 ≤ splitK2 cf := by unfold splitK2; have := coefBound_nonneg cf; positivity
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set ψ := canonPsi cf μ w n
  set c : ℝ := 2 * a / n with hc
  have hc0 : 0 ≤ c := by positivity
  have hE : ∀ i y u, euclNorm (ψ i (y + u) - ψ i y - u) ≤ c * euclNorm u := fun i y u => by
    have := canonPsi_near_id cf hμ w hn i y u
    rwa [hc, ha, hKd]
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ j ∈ Finset.range n, euclNorm (tailSum ζ n (j + 1)) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ Finset.sum_nonneg fun _ _ => euclNorm_nonneg _
  have hpowc : ∀ m ≤ n, (1 + c) ^ m ≤ Real.exp (2 * a) := fun m hm => by
    calc (1 + c) ^ m ≤ (1 + c) ^ n := pow_le_pow_right₀ (by linarith) hm
      _ ≤ Real.exp (2 * a) := by rw [hc]; exact one_add_div_pow_le_exp' (by positivity) hn
  -- the remainder bound, uniform in `m ≤ n`
  have hEm : ∀ m ≤ n, euclNorm (tailDsp ψ n m x ζ - tailSum ζ n m) ≤
      Real.exp (2 * a) * (2 * a) * (A / n) := fun m hm => by
    refine (tailDsp_sub_tailSum_le n hc0 hE x ζ m).trans ?_
    have hsub : ∑ j ∈ Finset.range m, euclNorm (tailSum ζ n (j + 1)) ≤ A :=
      hA ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun _ _ _ => euclNorm_nonneg _)
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range m, euclNorm (tailSum ζ n (j + 1)) :=
      Finset.sum_nonneg fun _ _ => euclNorm_nonneg _
    calc (1 + c) ^ m * c * ∑ j ∈ Finset.range m, euclNorm (tailSum ζ n (j + 1))
        ≤ Real.exp (2 * a) * c * A := by
          gcongr
          exact hpowc m hm
      _ = Real.exp (2 * a) * (2 * a) * (A / n) := by rw [hc]; ring
  have hG : sumGauge ζ n = euclNorm (tailSum ζ n n) + A / n := by rw [hA]; rfl
  have hS0 := euclNorm_nonneg (tailSum ζ n n)
  have hAn : 0 ≤ A / n := by positivity
  constructor
  · rw [splitMap_eq_tailMap, splitMap_eq_tailMap]
    have e : tailMap ψ ζ n n x - tailMap ψ 0 n n x =
        (tailDsp ψ n n x ζ - tailSum ζ n n) + tailSum ζ n n := by
      simp only [tailDsp]; abel
    rw [e, hG]
    refine (euclNorm_add_le _ _).trans ?_
    have := hEm n le_rfl
    have : 0 ≤ 2 * a * Real.exp (2 * a) := by positivity
    nlinarith
  · have hp : 1 ≤ 1 + a / n := by have : 0 ≤ a / n := by positivity
                                  linarith
    have hstep := canonPsi_step_bounds cf hμ w hn
    have h := norm_fderiv_tailMap_sub_le (ψ := ψ) n hp (by positivity : 0 ≤ b / n)
      (fun i => (hstep i).1) (fun i => (hstep i).2.2.1) (fun i => (hstep i).2.2.2) x ζ n
    rw [splitMap_eq_tailMap, splitMap_eq_tailMap]
    refine h.trans ?_
    have hterm : ∀ j ∈ Finset.range n, euclNorm (tailDsp ψ n j x ζ + ζ (n - j)) ≤
        Real.exp (2 * a) * (2 * a) * (A / n) + euclNorm (tailSum ζ n (j + 1)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have e : tailDsp ψ n j x ζ + ζ (n - j) =
          (tailDsp ψ n j x ζ - tailSum ζ n j) + tailSum ζ n (j + 1) := by
        rw [tailSum_succ]; abel
      rw [e]
      exact (euclNorm_add_le _ _).trans (add_le_add (hEm j hj.le) le_rfl)
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hA] at hsum
    have hpn : (1 + a / n) ^ n ≤ Real.exp a := one_add_div_pow_le_exp' ha0 hn
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, euclNorm (tailDsp ψ n j x ζ + ζ (n - j)) :=
      Finset.sum_nonneg fun _ _ => euclNorm_nonneg _
    calc (1 + a / n) ^ n * (b / n) * ∑ j ∈ Finset.range n, euclNorm (tailDsp ψ n j x ζ + ζ (n - j))
        ≤ Real.exp a * (b / n) * ((n : ℝ) * (Real.exp (2 * a) * (2 * a) * (A / n)) + A) := by
          gcongr
      _ = Real.exp a * b * (2 * a * Real.exp (2 * a) + 1) * (A / n) := by
          field_simp
      _ ≤ Real.exp a * b * (2 * a * Real.exp (2 * a) + 1) * sumGauge ζ n := by
          rw [hG]; gcongr; linarith

/-- **Lemma 3.9** (closeness of the split maps): with `Ψ₀` the inverse terminal flow map of
`b_ω`, `𝔼_ζ‖Ψ_n - Ψ₀‖_∞ ≤ C√μ` and `𝔼_ζ‖DΨ_n - DΨ₀‖_∞ ≤ C√μ` for `0 ≤ μ ≤ 1`. -/
theorem split_map_closeness {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) :
    ∃ C : ℝ, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ w n ψ (Ψ₀ : Pt 2 → Pt 2), 1 ≤ n →
      IsSplitting (dampedB cf μ w) n ψ → IsInverseFlowMap (bField cf w) 0 1 Ψ₀ →
      (∫⁻ ζ, ⨆ x, ‖splitMap ψ ζ n x - Ψ₀ x‖ₑ ∂(gaussSeq (splitVar μ n)))
          ≤ ENNReal.ofReal (C * Real.sqrt μ) ∧
      (∫⁻ ζ, ⨆ x, ‖fderiv ℝ (splitMap ψ ζ n) x - fderiv ℝ Ψ₀ x‖ₑ ∂(gaussSeq (splitVar μ n)))
          ≤ ENNReal.ofReal (C * Real.sqrt μ) := by
  set K : ℝ := (splitK cf : ℝ) with hKdef
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  set a : ℝ := K * Real.exp K with ha
  set b : ℝ := splitK2 cf * Real.exp (3 * K) with hb
  have hCb := coefBound_nonneg cf
  have ha0 : 0 ≤ a := by positivity
  have hK2 : 0 ≤ splitK2 cf := by unfold splitK2; positivity
  have hb0 : 0 ≤ b := by positivity
  set P0 : ℝ := 1 + 2 * a * Real.exp (2 * a) with hP0
  set P1 : ℝ := Real.exp a * b * (2 * a * Real.exp (2 * a) + 1) with hP1
  set D0 : ℝ := 2 * coefBound cf * Real.exp K with hD0
  set D1 : ℝ := (splitK2 cf * (2 * coefBound cf) * Real.exp K + 4 * π * coefBound cf) *
    Real.exp K * Real.exp K with hD1
  have hP00 : 0 ≤ P0 := by positivity
  have hP10 : 0 ≤ P1 := by positivity
  have hD00 : 0 ≤ D0 := by positivity
  have hD10 : 0 ≤ D1 := by positivity
  refine ⟨4 * (P0 + P1) + D0 + D1, fun μ hμ w n ψ Ψ₀ hn hψ hΨ₀ => ?_⟩
  have hμ0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set v := splitVar μ n
  have hsplit : ∀ ζ, splitMap ψ ζ n = splitMap (canonPsi cf μ w n) ζ n := fun ζ =>
    splitMap_congr ζ (isSplitting_eq_canonPsi cf hμ w hn hψ)
  have hΨ₀e := isInverseFlowMap_bField_eq cf w hΨ₀
  have hdet0 := splitMap_canonPsi_zero_n cf hμ w hn
  have hsq : μ ≤ Real.sqrt μ := by
    have h1 : Real.sqrt μ ≤ 1 := Real.sqrt_le_one.2 hμ.2
    have h2 := Real.sq_sqrt hμ.1
    nlinarith [Real.sqrt_nonneg μ]
  have hgauge : ∫⁻ ζ, ENNReal.ofReal (sumGauge ζ n) ∂(gaussSeq v) ≤
      ENNReal.ofReal (4 * Real.sqrt μ) := by
    refine (lintegral_sumGauge_le v n).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.sqrt (n * (2 * (v : ℝ))) ≤ Real.sqrt (2 * μ) :=
      Real.sqrt_le_sqrt (by nlinarith [natCast_mul_splitVar_le hμ.1 hn])
    have h2 : Real.sqrt (2 * μ) ≤ 2 * Real.sqrt μ := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      gcongr
    linarith
  -- integrating a pathwise gauge bound
  have hint : ∀ (P D : ℝ), 0 ≤ P → 0 ≤ D → ∀ F : (ℕ → Pt 2) → ℝ≥0∞,
      (∀ ζ, F ζ ≤ ENNReal.ofReal (P * sumGauge ζ n + D * μ)) →
      ∫⁻ ζ, F ζ ∂(gaussSeq v) ≤ ENNReal.ofReal (4 * P * Real.sqrt μ + D * Real.sqrt μ) := by
    intro P D hP hD F hF
    calc ∫⁻ ζ, F ζ ∂(gaussSeq v)
        ≤ ∫⁻ ζ, (ENNReal.ofReal P * ENNReal.ofReal (sumGauge ζ n) + ENNReal.ofReal (D * μ))
            ∂(gaussSeq v) := by
          refine lintegral_mono fun ζ => (hF ζ).trans ?_
          rw [← ENNReal.ofReal_mul hP]
          exact ENNReal.ofReal_add_le
      _ = ENNReal.ofReal P * ∫⁻ ζ, ENNReal.ofReal (sumGauge ζ n) ∂(gaussSeq v) +
            ENNReal.ofReal (D * μ) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal P * ENNReal.ofReal (4 * Real.sqrt μ) +
            ENNReal.ofReal (D * Real.sqrt μ) := by
          gcongr
      _ = ENNReal.ofReal (4 * P * Real.sqrt μ + D * Real.sqrt μ) := by
          rw [← ENNReal.ofReal_mul hP, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  have hfinal : ∀ (P D : ℝ), 0 ≤ P → 0 ≤ D → P ≤ P0 + P1 → D ≤ D0 + D1 →
      ENNReal.ofReal (4 * P * Real.sqrt μ + D * Real.sqrt μ) ≤
        ENNReal.ofReal ((4 * (P0 + P1) + D0 + D1) * Real.sqrt μ) := by
    intro P D hP hD hPP hDD
    refine ENNReal.ofReal_le_ofReal ?_
    have := Real.sqrt_nonneg μ
    nlinarith
  constructor
  · -- `C⁰` part
    have hdet : ∀ x, ‖splitMap (canonPsi cf μ w n) 0 n x - Ψ₀ x‖ ≤ D0 * μ := fun x => by
      have hμ1 := hμ.1
      rw [hdet0, hΨ₀e, ← dist_eq_norm]
      have h := (splitField_good cf hμ w).dist_gflow_field_le (splitField_good cf hμ0 w)
        (by positivity : 0 ≤ 2 * (μ * coefBound cf)) 1 0
        (fun s _ y => norm_splitField_sub_zero_le cf hμ w s y) x
      rw [show |(0 : ℝ) - 1| = 1 by norm_num] at h
      refine h.trans (le_of_eq ?_)
      rw [hD0, hKdef]; ring_nf
    refine (hint P0 D0 hP00 hD00 _ fun ζ => iSup_le fun x => ?_).trans
      (hfinal P0 D0 hP00 hD00 (by linarith) (by linarith))
    rw [← ofReal_norm_eq_enorm, hsplit]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp := (canon_pathwise cf hμ w hn ζ x hKdef ha hb).1
    calc ‖splitMap (canonPsi cf μ w n) ζ n x - Ψ₀ x‖
        ≤ ‖splitMap (canonPsi cf μ w n) ζ n x - splitMap (canonPsi cf μ w n) 0 n x‖ +
          ‖splitMap (canonPsi cf μ w n) 0 n x - Ψ₀ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ P0 * sumGauge ζ n + D0 * μ :=
          add_le_add ((norm_le_euclNorm _).trans hp) (hdet x)
  · -- `C¹` part
    have hdet : ∀ x, ‖fderiv ℝ (splitMap (canonPsi cf μ w n) 0 n) x - fderiv ℝ Ψ₀ x‖ ≤
        D1 * μ := fun x => by
      rw [hdet0, hΨ₀e]
      have h := norm_fderiv_gflow_sub_le (splitField_good cf hμ w) (splitField_C2 cf hμ w)
        (splitField_good cf hμ0 w) (splitField_C2 cf hμ0 w) (norm_splitField_sub_zero_le cf hμ w)
        (norm_fderiv_splitField_sub_zero_le cf hμ w) 1 0 x
      rw [show |(0 : ℝ) - 1| = 1 by norm_num] at h
      refine h.trans (le_of_eq ?_)
      rw [hD1, hKdef]; ring_nf
    refine (hint P1 D1 hP10 hD10 _ fun ζ => iSup_le fun x => ?_).trans
      (hfinal P1 D1 hP10 hD10 (by linarith) (by linarith))
    rw [← ofReal_norm_eq_enorm, hsplit]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp := (canon_pathwise cf hμ w hn ζ x hKdef ha hb).2
    calc ‖fderiv ℝ (splitMap (canonPsi cf μ w n) ζ n) x - fderiv ℝ Ψ₀ x‖
        ≤ ‖fderiv ℝ (splitMap (canonPsi cf μ w n) ζ n) x -
            fderiv ℝ (splitMap (canonPsi cf μ w n) 0 n) x‖ +
          ‖fderiv ℝ (splitMap (canonPsi cf μ w n) 0 n) x - fderiv ℝ Ψ₀ x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ P1 * sumGauge ζ n + D1 * μ := add_le_add hp (hdet x)

end AnomDiss
