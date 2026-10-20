module

public import RequestProject.SplitSmooth
public import RequestProject.SplitConvergence

/-!
# Regularity of the canonical split maps

The `C²` bounds of Lemma 3.8 for the canonical splitting: each step is the flow of a smooth
field over a time `1/n`, hence `1/n`-close to the identity in `C²`, and the bounds survive the
`n`-fold composition.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

section Comp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Second-derivative bound for a composition. -/
lemma norm_fderiv_fderiv_comp_le {g f : E → E} (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : E) :
    ‖fderiv ℝ (fderiv ℝ (g ∘ f)) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ g) (f x)‖ * ‖fderiv ℝ f x‖ ^ 2 +
        ‖fderiv ℝ g (f x)‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg2 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  have hf2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  have hfd : fderiv ℝ (g ∘ f) = fun y => (fderiv ℝ g (f y)).comp (fderiv ℝ f y) := by
    funext y; exact fderiv_comp y (hg1 _) (hf1 _)
  have hA : HasFDerivAt (fun y => fderiv ℝ g (f y))
      ((fderiv ℝ (fderiv ℝ g) (f x)).comp (fderiv ℝ f x)) x :=
    (hg2 (f x)).hasFDerivAt.comp x (hf1 x).hasFDerivAt
  have h := hA.clm_comp (hf2 x).hasFDerivAt
  rw [hfd, h.fderiv]
  refine (norm_add_le (E := E →L[ℝ] E →L[ℝ] E) _ _).trans ?_
  have e1 := ContinuousLinearMap.opNorm_comp_le (ContinuousLinearMap.compL ℝ E E E
    (fderiv ℝ g (f x))) (fderiv ℝ (fderiv ℝ f) x)
  have e2 := ContinuousLinearMap.opNorm_comp_le ((ContinuousLinearMap.compL ℝ E E E).flip
    (fderiv ℝ f x)) ((fderiv ℝ (fderiv ℝ g) (f x)).comp (fderiv ℝ f x))
  have e3 := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (fderiv ℝ g) (f x)) (fderiv ℝ f x)
  have n1 := norm_compL_apply_le (E := E) (fderiv ℝ g (f x))
  have n2 := norm_compL_flip_apply_le (G := E) (fderiv ℝ f x)
  have p1 := norm_nonneg (fderiv ℝ (fderiv ℝ f) x)
  have p2 := norm_nonneg (fderiv ℝ f x)
  have p3 := norm_nonneg (fderiv ℝ (fderiv ℝ g) (f x))
  have p4 := norm_nonneg (fderiv ℝ g (f x))
  calc _ ≤ ‖fderiv ℝ g (f x)‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ +
        ‖fderiv ℝ f x‖ * (‖fderiv ℝ (fderiv ℝ g) (f x)‖ * ‖fderiv ℝ f x‖) := by
        gcongr
        · exact e1.trans (mul_le_mul_of_nonneg_right n1 p1)
        · refine e2.trans ?_
          exact mul_le_mul n2 e3 (norm_nonneg _) p2
    _ = _ := by ring

end Comp

section Iter

lemma fderiv_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (ψ : Pt 2 → F)
    (z : Pt 2) :
    fderiv ℝ (fun y => ψ (y + z)) = fun y => fderiv ℝ ψ (y + z) := by
  funext y; exact fderiv_comp_add_right z

lemma fderiv_fderiv_shift (ψ : Pt 2 → Pt 2) (z : Pt 2) :
    fderiv ℝ (fderiv ℝ (fun y => ψ (y + z))) = fun y => fderiv ℝ (fderiv ℝ ψ) (y + z) := by
  rw [fderiv_shift]; exact fderiv_shift (fderiv ℝ ψ) z

/-- Iterated `C²` bounds for the compositions `Ψ_j`. -/
theorem splitMap_C2_bounds (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (n : ℕ) {p q : ℝ}
    (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hψ : ∀ i, 1 ≤ i → i ≤ n → ContDiff ℝ 2 (ψ i) ∧
      ∀ x, ‖fderiv ℝ (ψ i) x‖ ≤ p ∧ ‖fderiv ℝ (fderiv ℝ (ψ i)) x‖ ≤ q) :
    ∀ j ≤ n, ContDiff ℝ 2 (splitMap ψ ζ j) ∧ ∀ x,
      ‖fderiv ℝ (splitMap ψ ζ j) x‖ ≤ p ^ j ∧
      ‖fderiv ℝ (fderiv ℝ (splitMap ψ ζ j)) x‖ ≤ j * q * p ^ (2 * j) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨contDiff_id, fun x => ?_⟩
    simp only [splitMap, pow_zero, Nat.cast_zero, zero_mul, mul_zero]
    have hid : fderiv ℝ (id : Pt 2 → Pt 2) = fun _ => ContinuousLinearMap.id ℝ (Pt 2) :=
      funext fun _ => fderiv_id
    rw [hid]
    exact ⟨ContinuousLinearMap.norm_id_le, by simp [norm_zero (E := Pt 2 →L[ℝ] Pt 2 →L[ℝ] Pt 2)]⟩
  | succ j ih =>
    intro hj
    obtain ⟨hc, hb⟩ := ih (by omega)
    obtain ⟨hψc, hψb⟩ := hψ (j + 1) (by omega) hj
    set f : Pt 2 → Pt 2 := fun y => ψ (j + 1) (y + ζ (j + 1)) with hf
    have hfc : ContDiff ℝ 2 f := hψc.comp (contDiff_id.add contDiff_const)
    have hfd : ∀ y, ‖fderiv ℝ f y‖ ≤ p := fun y => by
      rw [hf, fderiv_shift]; exact (hψb _).1
    have hfd2 : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ q := fun y => by
      rw [hf, fderiv_fderiv_shift]; exact (hψb _).2
    have hS : splitMap ψ ζ (j + 1) = splitMap ψ ζ j ∘ f := rfl
    rw [hS]
    have hp0 : 0 ≤ p := by linarith
    refine ⟨hc.comp hfc, fun x => ⟨?_, ?_⟩⟩
    · rw [fderiv_comp x ((hc.differentiable (by simp)) _) ((hfc.differentiable (by simp)) _)]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [pow_succ]
      exact mul_le_mul (hb _).1 (hfd x) (norm_nonneg _) (by positivity)
    · refine (norm_fderiv_fderiv_comp_le hc hfc x).trans ?_
      have h1 := (hb (f x)).2
      have h2 := (hb (f x)).1
      have h3 := hfd x
      have h4 := hfd2 x
      have hpj : p ^ j ≤ p ^ (2 * (j + 1)) := pow_le_pow_right₀ hp (by omega)
      have hn2 : 0 ≤ ‖fderiv ℝ f x‖ ^ 2 := by positivity
      have e : ((j + 1 : ℕ) : ℝ) * q * p ^ (2 * (j + 1)) =
          (j * q * p ^ (2 * j)) * p ^ 2 + q * p ^ (2 * (j + 1)) := by
        push_cast; ring
      rw [e]
      have hsq : ‖fderiv ℝ f x‖ ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hA : 0 ≤ (j : ℝ) * q * p ^ (2 * j) := by positivity
      refine add_le_add (mul_le_mul h1 hsq hn2 hA) ?_
      · calc ‖fderiv ℝ (splitMap ψ ζ j) (f x)‖ * ‖fderiv ℝ (fderiv ℝ f) x‖
            ≤ p ^ j * q := mul_le_mul h2 h4 (norm_nonneg (fderiv ℝ (fderiv ℝ f) x)) (by positivity)
          _ ≤ p ^ (2 * (j + 1)) * q := by gcongr
          _ = q * p ^ (2 * (j + 1)) := mul_comm _ _

/-- The inverse compositions `Ψ_j⁻¹ = g_j ∘ ⋯`, `g_i(z) = ψ_i⁻¹(z) - ζ_i`. -/
def splitInv (g : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) : ℕ → Pt 2 → Pt 2
  | 0 => id
  | j + 1 => (fun z => g (j + 1) z - ζ (j + 1)) ∘ splitInv g ζ j

lemma splitInv_leftInverse (ψ g : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2)
    (hg : ∀ i x, g i (ψ i x) = x) (j : ℕ) :
    Function.LeftInverse (splitInv g ζ j) (splitMap ψ ζ j) := by
  induction j with
  | zero => intro x; rfl
  | succ j ih =>
    intro x
    simp only [splitInv, splitMap, Function.comp_apply, ih _, hg, add_sub_cancel_right]

theorem splitInv_C1_bounds (g : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (n : ℕ) {p : ℝ}
    (hp : 1 ≤ p)
    (hg : ∀ i, 1 ≤ i → i ≤ n → ContDiff ℝ 1 (g i) ∧ ∀ x, ‖fderiv ℝ (g i) x‖ ≤ p) :
    ∀ j ≤ n, ContDiff ℝ 1 (splitInv g ζ j) ∧ ∀ x, ‖fderiv ℝ (splitInv g ζ j) x‖ ≤ p ^ j := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨contDiff_id, fun x => ?_⟩
    simp only [splitInv, pow_zero]
    rw [fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  | succ j ih =>
    intro hj
    obtain ⟨hc, hb⟩ := ih (by omega)
    obtain ⟨hgc, hgb⟩ := hg (j + 1) (by omega) hj
    set f : Pt 2 → Pt 2 := fun z => g (j + 1) z - ζ (j + 1) with hf
    have hfc : ContDiff ℝ 1 f := hgc.sub contDiff_const
    have hfd : ∀ y, ‖fderiv ℝ f y‖ ≤ p := fun y => by
      rw [hf, fderiv_sub_const]; exact hgb y
    have hS : splitInv g ζ (j + 1) = f ∘ splitInv g ζ j := rfl
    rw [hS]
    refine ⟨hfc.comp hc, fun x => ?_⟩
    rw [fderiv_comp x ((hfc.differentiable (by simp)) _) ((hc.differentiable (by simp)) _)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [pow_succ, mul_comm (p ^ j)]
    exact mul_le_mul (hfd _) (hb x) (norm_nonneg _) (by positivity)

end Iter

section Lift

lemma splitMap_isLift (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (hψ : ∀ i, IsLift (ψ i)) (j : ℕ) :
    IsLift (splitMap ψ ζ j) := by
  induction j with
  | zero => intro x m; rfl
  | succ j ih =>
    intro x m
    simp only [splitMap, Function.comp_apply]
    rw [show x + intVec m + ζ (j + 1) = x + ζ (j + 1) + intVec m by abel, hψ, ih]

/-- The flow of an `x`-periodic field commutes with integer translations. -/
lemma gflow_isLift {V : ℝ → Pt 2 → Pt 2} {M K : ℝ≥0} (hV : GoodField V M K)
    (hper : ∀ s x (m : Fin 2 → ℤ), V s (x + intVec m) = V s x) (t₀ t : ℝ) :
    IsLift (gflow V t₀ t) := by
  intro x m
  have hα : ∀ s, HasDerivAt (fun s => gflow V t₀ s x + intVec m)
      (V s (gflow V t₀ s x + intVec m)) s := fun s => by
    rw [hper]; exact (hV.hasDerivAt_gflow t₀ s x).add_const _
  have h := congrFun (hV.eq_gflow (t₀ := t₀) hα) t
  simp only [hV.gflow_self] at h
  exact h.symm

end Lift

section Canon

variable {L M : ℕ} {S : ℕ → ℝ}

lemma splitField_eq_eFieldAt (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) :
    splitField cf μ w = eFieldAt (fun s => dampedCoef cf μ w (clamp01 s)) w.2 := by
  funext s x; rw [splitField_apply]; rfl

lemma splitField_periodic (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ)
    (x : Pt 2) (m : Fin 2 → ℤ) : splitField cf μ w s (x + intVec m) = splitField cf μ w s x := by
  rw [splitField_apply, splitField_apply, show x + intVec m - w.2 = x - w.2 + intVec m by abel]
  exact (eigenspace_properties _).2.1 _ _

/-- The second-order constant of the splitting field. -/
def splitK2 (cf : ControlFamily L M S) : ℝ := 16 * π ^ 2 * (2 * coefBound cf)

theorem splitField_C2 (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) :
    C2Field (splitField cf μ w) (splitK2 cf) (32 * π ^ 3 * (2 * coefBound cf)) := by
  rw [splitField_eq_eFieldAt]
  refine eFieldAt_C2 ?_ (fun s => norm_dampedCoef_le cf hμ w (clamp01_mem s)) w.2
  have hc : Continuous (dampedCoef cf μ w) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_dampedCoef cf μ w s).continuousAt
  exact hc.comp continuous_clamp01

/-- One flow step of length `1/n` of the splitting field is `1/n`-close to the identity in
`C²`. -/
lemma splitFlow_step (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {n : ℕ} (hn : 1 ≤ n) {t₀ t : ℝ} (ht : |t - t₀| = 1 / n) :
    ContDiff ℝ 2 (gflow (splitField cf μ w) t₀ t) ∧ ∀ x,
      ‖fderiv ℝ (gflow (splitField cf μ w) t₀ t) x‖ ≤
        1 + splitK cf * Real.exp (splitK cf) / n ∧
      ‖fderiv ℝ (fderiv ℝ (gflow (splitField cf μ w) t₀ t)) x‖ ≤
        splitK2 cf * Real.exp (3 * splitK cf) / n := by
  obtain ⟨hc, hb⟩ := gflow_C2 (splitField_good cf hμ w) (splitField_C2 cf hμ w) t₀ t
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact_mod_cast hn
  have hn1' : 0 ≤ 1 / (n : ℝ) := by positivity
  have hK := NNReal.coe_nonneg (splitK cf)
  have hK2 : 0 ≤ splitK2 cf := by
    have := coefBound_nonneg cf; unfold splitK2; positivity
  refine ⟨hc, fun x => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, -⟩ := hb x
    rw [ht] at h1
    have e1 : Real.exp (splitK cf * (1 / n)) ≤ Real.exp (splitK cf) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc ‖fderiv ℝ (gflow (splitField cf μ w) t₀ t) x‖
        ≤ ‖fderiv ℝ (gflow (splitField cf μ w) t₀ t) x - ContinuousLinearMap.id ℝ (Pt 2)‖ +
          ‖ContinuousLinearMap.id ℝ (Pt 2)‖ := norm_le_norm_sub_add _ _
      _ ≤ splitK cf * (1 / n) * Real.exp (splitK cf * (1 / n)) + 1 :=
          add_le_add h1 ContinuousLinearMap.norm_id_le
      _ ≤ splitK cf * (1 / n) * Real.exp (splitK cf) + 1 := by gcongr
      _ = 1 + splitK cf * Real.exp (splitK cf) / n := by ring
  · obtain ⟨-, h2⟩ := hb x
    rw [ht] at h2
    have e1 : Real.exp (3 * splitK cf * (1 / n)) ≤ Real.exp (3 * splitK cf) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc _ ≤ splitK2 cf * (1 / n) * Real.exp (3 * splitK cf * (1 / n)) := h2
      _ ≤ splitK2 cf * (1 / n) * Real.exp (3 * splitK cf) := by gcongr
      _ = splitK2 cf * Real.exp (3 * splitK cf) / n := by ring

lemma one_add_div_pow_le_exp' {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    (1 + a / n) ^ n ≤ Real.exp a := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc (1 + a / n) ^ n ≤ Real.exp (a / n) ^ n := by
        have : 0 ≤ a / n := by positivity
        gcongr
        linarith [Real.add_one_le_exp (a / n)]
    _ = Real.exp a := by rw [← Real.exp_nat_mul]; congr 1; field_simp

theorem canonSplit_regular_aux (cf : ControlFamily L M S) :
    ∃ C : ℝ, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ (w : BlockParam L) (n : ℕ), 1 ≤ n → ∀ ζ : ℕ → Pt 2,
      ContDiff ℝ 2 (splitMap (canonPsi cf μ w n) ζ n) ∧
      IsLift (splitMap (canonPsi cf μ w n) ζ n) ∧
      ∃ Ψinv : Pt 2 → Pt 2, ContDiff ℝ 1 Ψinv ∧
        Function.LeftInverse Ψinv (splitMap (canonPsi cf μ w n) ζ n) ∧
        ∀ x, ‖fderiv ℝ (splitMap (canonPsi cf μ w n) ζ n) x‖ ≤ C ∧
          ‖iteratedFDeriv ℝ 2 (splitMap (canonPsi cf μ w n) ζ n) x‖ ≤ C ∧
          ‖fderiv ℝ Ψinv x‖ ≤ C := by
  set a : ℝ := splitK cf * Real.exp (splitK cf) with ha
  set b : ℝ := splitK2 cf * Real.exp (3 * splitK cf) with hb
  have hK := NNReal.coe_nonneg (splitK cf)
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by
    have := coefBound_nonneg cf
    have : 0 ≤ splitK2 cf := by unfold splitK2; positivity
    positivity
  refine ⟨max (Real.exp a) (b * Real.exp (2 * a)), fun μ hμ w n hn ζ => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set p : ℝ := 1 + a / n with hp
  have hp1 : 1 ≤ p := by have : 0 ≤ a / n := by positivity
                         linarith
  have hpn : p ^ n ≤ Real.exp a := one_add_div_pow_le_exp' ha0 hn
  have hstep : ∀ i : ℕ, ∀ t₀ t : ℝ, |t - t₀| = 1 / n →
      ContDiff ℝ 2 (gflow (splitField cf μ w) t₀ t) ∧ ∀ x,
        ‖fderiv ℝ (gflow (splitField cf μ w) t₀ t) x‖ ≤ p ∧
        ‖fderiv ℝ (fderiv ℝ (gflow (splitField cf μ w) t₀ t)) x‖ ≤ b / n := by
    intro _ t₀ t ht
    obtain ⟨h1, h2⟩ := splitFlow_step cf hμ w hn ht
    refine ⟨h1, fun x => ⟨?_, ?_⟩⟩
    · rw [hp, ha, mul_div_assoc] at *; simpa [mul_div_assoc] using (h2 x).1
    · rw [hb]; exact (h2 x).2
  have habs1 : ∀ i : ℕ, |((i : ℝ) - 1) / n - (i : ℝ) / n| = 1 / n := fun i => by
    rw [← sub_div, abs_div, abs_of_pos hn0]; norm_num
  have habs2 : ∀ i : ℕ, |(i : ℝ) / n - ((i : ℝ) - 1) / n| = 1 / n := fun i => by
    rw [← sub_div, abs_div, abs_of_pos hn0]; norm_num
  obtain ⟨hc, hbd⟩ := splitMap_C2_bounds (canonPsi cf μ w n) ζ n hp1 (by positivity)
    (fun i _ _ => hstep i _ _ (habs1 i)) n le_rfl
  set g : ℕ → Pt 2 → Pt 2 := fun i => gflow (splitField cf μ w) (((i : ℝ) - 1) / n) ((i : ℝ) / n)
    with hg
  obtain ⟨hgc, hgb⟩ := splitInv_C1_bounds g ζ n hp1
    (fun i _ _ => ⟨(hstep i _ _ (habs2 i)).1.of_le (by norm_num),
      fun x => ((hstep i _ _ (habs2 i)).2 x).1⟩) n le_rfl
  have hV := splitField_good cf hμ w
  refine ⟨hc, splitMap_isLift _ ζ (fun i => gflow_isLift hV (splitField_periodic cf μ w) _ _) n,
    splitInv g ζ n, hgc, splitInv_leftInverse _ g ζ (fun i x => hV.gflow_inv _ _ x) n,
    fun x => ⟨?_, ?_, ?_⟩⟩
  · exact ((hbd x).1.trans hpn).trans (le_max_left _ _)
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    refine ((hbd x).2.trans ?_).trans (le_max_right _ _)
    have hp2 : p ^ (2 * n) ≤ Real.exp (2 * a) := by
      rw [pow_mul', show 2 * a = a + a by ring, Real.exp_add, sq]
      exact mul_le_mul hpn hpn (by positivity) (by positivity)
    calc (n : ℝ) * (b / n) * p ^ (2 * n) = b * p ^ (2 * n) := by field_simp
      _ ≤ b * Real.exp (2 * a) := by gcongr
  · exact ((hgb x).trans hpn).trans (le_max_left _ _)

end Canon

end AnomDiss
