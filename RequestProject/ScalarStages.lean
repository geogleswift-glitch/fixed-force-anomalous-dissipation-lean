module

public import RequestProject.Parameters

/-!
# Staged advection–diffusion problems (toward Lemma 5.6)

Uniqueness of classical scalar solutions (from the maximum principle), Hölder regularity of
data, existence of solutions on a single stage (from External Result 1.6), and the chaining of
stages `I_j = [s_j, s_j + δ_j]` (drift `D_j`) and `J_j = [s_j + δ_j, s_{j+1}]` (no drift).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-! ### Stage times -/

lemma sj_one : sj 1 = 0 := by simp [sj]

lemma sj_succ (j : ℕ) (hj : 1 ≤ j) : sj (j + 1) = sj j + δs j + ηs j := by
  unfold sj; rw [Finset.sum_Ico_succ_top hj]; ring

lemma sj_mono {j k : ℕ} (h : j ≤ k) : sj j ≤ sj k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right h)
    (fun i _ _ => stage_nonneg i)

lemma ηs_nonneg (j : ℕ) : 0 ≤ ηs j := by unfold ηs τstar; positivity

lemma δs_pos (j : ℕ) (hj : 1 ≤ j) : 0 < δs j := by
  unfold δs τstar; have : (0:ℝ) < j := by exact_mod_cast hj
  positivity

lemma ηs_pos (j : ℕ) (hj : 1 ≤ j) : 0 < ηs j := by
  unfold ηs τstar; have : (0:ℝ) < j := by exact_mod_cast hj
  positivity

/-! ### Linear-algebraic facts about the operators -/

section ops
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pd_sub_fun (f g : Pt d → E) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin d) : pd i (fun x => f x - g x) = fun x => pd i f x - pd i g x := by
  funext x; simp [pd, fderiv_fun_sub (hf x) (hg x)]

end ops

/-! ### Uniqueness -/

/-- Two classical solutions with the same drift and initial datum coincide (a consequence of
the maximum principle; no assumption on the drift is needed). -/
theorem classical_scalar_unique (T ν : ℝ) (hν : 0 ≤ ν) (v : ℝ → Pt 2 → Pt 2)
    (θ₀ : Pt 2 → ℝ) (θ θ' : ℝ → Pt 2 → ℝ) (hθ : IsClassicalScalar T ν v θ₀ θ)
    (hθ' : IsClassicalScalar T ν v θ₀ θ') : ∀ t ∈ Icc 0 T, θ t = θ' t := by
  obtain ⟨β, -, -, reg⟩ := hθ.regular
  obtain ⟨β', -, -, reg'⟩ := hθ'.regular
  have hdiff2 : ∀ t ∈ Icc 0 T, Differentiable ℝ (θ t) ∧ Differentiable ℝ (θ' t) := fun t ht =>
    ⟨(reg.smooth_x t ht).differentiable (by norm_num),
      (reg'.smooth_x t ht).differentiable (by norm_num)⟩
  have key := max_principle_abs T ν hν v (fun t x => θ t x - θ' t x)
    (reg.continuousOn.sub reg'.continuousOn)
    (fun t ht y n => by simp [hθ.periodic t ht y n, hθ'.periodic t ht y n])
    (fun t ht => (reg.smooth_x t ht).sub (reg'.smooth_x t ht))
    (fun y t ht => (reg.diff_t y t ht).sub (reg'.diff_t y t ht)) ?_ 0
    (fun y => by simp [hθ.init, hθ'.init])
  · intro t ht
    funext x
    have := key t ht x
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  · intro t ht y
    have h1 := hθ.eqn t ht y
    have h2 := hθ'.eqn t ht y
    obtain ⟨d1, d2⟩ := hdiff2 t ht
    have e1 : dt T (fun t x => θ t x - θ' t x) t y = dt T θ t y - dt T θ' t y := by
      simp only [dt]
      exact derivWithin_fun_sub (reg.diff_t y t ht) (reg'.diff_t y t ht)
    have hpd : ∀ i, pd i (fun x => θ t x - θ' t x) = fun x => pd i (θ t) x - pd i (θ' t) x :=
      fun i => pd_sub_fun _ _ d1 d2 i
    have e2 : conv (v t) (fun x => θ t x - θ' t x) y = conv (v t) (θ t) y - conv (v t) (θ' t) y := by
      simp only [conv, hpd, smul_sub, Finset.sum_sub_distrib]
    have e3 : lap (fun x => θ t x - θ' t x) y = lap (θ t) y - lap (θ' t) y := by
      simp only [lap, hpd]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pd_sub_fun _ _ ((contDiff_pd_of_C2 _ (reg.smooth_x t ht) i).differentiable one_ne_zero)
        ((contDiff_pd_of_C2 _ (reg'.smooth_x t ht) i).differentiable one_ne_zero)]
    rw [e1, e2, e3, smul_sub]
    simp only [smul_eq_mul] at h1 h2 ⊢
    linarith

/-! ### Congruence: only the values on `[0,T]` matter -/

section congr
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dt_congr {T : ℝ} {u u' : ℝ → Pt d → E} (h : ∀ t ∈ Icc 0 T, u' t = u t) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : Pt d) : dt T u' t x = dt T u t x := by
  unfold dt
  exact derivWithin_congr (fun s hs => by simp [h s hs]) (by simp [h t ht])

lemma IsParabolicC12.congr {T β : ℝ} {u u' : ℝ → Pt d → E} (hu : IsParabolicC12 T β u)
    (h : ∀ t ∈ Icc 0 T, u' t = u t) : IsParabolicC12 T β u' := by
  have hd : ∀ t ∈ Icc 0 T, ∀ x, dt T u' t x = dt T u t x := fun t ht x => dt_congr h ht x
  obtain ⟨h1, h2, ⟨C3, h3⟩, ⟨C4, h4⟩, ⟨C5, h5⟩, h6, h7, h8, h9⟩ := hu
  refine ⟨fun t ht => by rw [h t ht]; exact h1 t ht, fun x t ht => ?_, ⟨C3, fun t ht x => ?_⟩,
    ⟨C4, fun t ht x => ?_⟩, ⟨C5, fun t ht s hs x y => ?_⟩, fun i => ?_, fun i => ?_,
    fun i j => ?_, fun i j => ?_⟩
  · exact (h2 x t ht).congr (fun s hs => by simp [h s hs]) (by simp [h t ht])
  · rw [h t ht]; exact h3 t ht x
  · rw [hd t ht]; exact h4 t ht x
  · rw [hd t ht, hd s hs]; exact h5 t ht s hs x y
  · obtain ⟨C, hC⟩ := h6 i; exact ⟨C, fun t ht x => by dsimp only; rw [h t ht]; exact hC t ht x⟩
  · obtain ⟨C, hC⟩ := h7 i
    exact ⟨C, fun t ht s hs x => by dsimp only; rw [h t ht, h s hs]; exact hC t ht s hs x⟩
  · obtain ⟨C, hC⟩ := h8 i j; exact ⟨C, fun t ht x => by dsimp only; rw [h t ht]; exact hC t ht x⟩
  · obtain ⟨C, hC⟩ := h9 i j
    exact ⟨C, fun t ht s hs x y => by dsimp only; rw [h t ht, h s hs]; exact hC t ht s hs x y⟩

lemma IsClassicalScalar.congr {T ν : ℝ} (hT : 0 ≤ T) {v : ℝ → Pt d → Pt d} {θ₀ : Pt d → E}
    {θ θ' : ℝ → Pt d → E} (hθ : IsClassicalScalar T ν v θ₀ θ)
    (h : ∀ t ∈ Icc 0 T, θ' t = θ t) : IsClassicalScalar T ν v θ₀ θ' := by
  obtain ⟨β, hβ0, hβ1, reg⟩ := hθ.regular
  refine ⟨fun t ht => by rw [h t ht]; exact hθ.periodic t ht, ⟨β, hβ0, hβ1, reg.congr h⟩,
    by rw [h 0 ⟨le_rfl, hT⟩]; exact hθ.init, fun t ht x => ?_⟩
  rw [dt_congr h ht, h t ht]; exact hθ.eqn t ht x

end congr

/-! ### Hölder regularity of data -/

/-- A time slice of a `C^{1+β/2,2+β}` function is `C^{2+β}`. -/
lemma IsParabolicC12.holderC2_slice {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T β : ℝ} (hβ : 0 < β) {u : ℝ → Pt d → E} (hu : IsParabolicC12 T β u)
    {t : ℝ} (ht : t ∈ Icc 0 T) : IsHolderC2 β (u t) := by
  refine ⟨hu.smooth_x t ht, ?_⟩
  choose C hC using hu.holder_d2
  refine ⟨∑ i, ∑ j, |C i j|, fun i j x y => ?_⟩
  have := hC i j t ht t ht x y
  rw [sub_self, abs_zero, Real.zero_rpow (by positivity), add_zero] at this
  refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  calc C i j ≤ |C i j| := le_abs_self _
    _ ≤ ∑ j', |C i j'| := Finset.single_le_sum (f := fun j' => |C i j'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |C i' j'| := Finset.single_le_sum (f := fun i' => ∑ j', |C i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- Bounded Lipschitz functions are `β`-Hölder for `0 ≤ β ≤ 1`. -/
lemma holder_of_lip_bdd {d : ℕ} {E : Type*} [NormedAddCommGroup E] (g : Pt d → E) {B L β : ℝ}
    (hL0 : 0 ≤ L) (hB : ∀ x, ‖g x‖ ≤ B) (hL : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : ∀ x y, ‖g x - g y‖ ≤ (2 * B + L) * ‖x - y‖ ^ β := by
  intro x y
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  set r := ‖x - y‖
  have hr : 0 ≤ r := norm_nonneg _
  rcases le_or_gt r 1 with h1 | h1
  · have : r ≤ r ^ β := by
      rcases eq_or_lt_of_le hr with h0 | h0
      · rw [← h0]; rcases eq_or_lt_of_le hβ0 with hb | hb
        · rw [← hb]; simp
        · rw [Real.zero_rpow hb.ne']
      · calc r = r ^ (1:ℝ) := (Real.rpow_one r).symm
          _ ≤ r ^ β := Real.rpow_le_rpow_of_exponent_ge h0 h1 hβ1
    calc ‖g x - g y‖ ≤ L * r := hL x y
      _ ≤ L * r ^ β := mul_le_mul_of_nonneg_left this hL0
      _ ≤ (2 * B + L) * r ^ β := by
          have : 0 ≤ r ^ β := Real.rpow_nonneg hr _
          nlinarith
  · have h1' : 1 ≤ r ^ β := Real.one_le_rpow h1.le hβ0
    calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB x, hB y]
      _ ≤ (2 * B + L) * r ^ β := by nlinarith

/-- A periodic `C¹` function is bounded and Lipschitz. -/
lemma periodic_C1_lip_bdd {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Pt d → E) (hg : ContDiff ℝ 1 g) (hp : IsPeriodic g) :
    ∃ B L, 0 ≤ L ∧ (∀ x, ‖g x‖ ≤ B) ∧ ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨B, hB⟩ := periodic_bdd g hg.continuous hp
  have hfp : IsPeriodic (fderiv ℝ g) := by
    intro x n
    have : g = fun y => g (y + intVec n) := funext fun y => (hp y n).symm
    conv_rhs => rw [this]
    rw [fderiv_comp_add_right]
  obtain ⟨L, hL⟩ := periodic_bdd _ (hg.continuous_fderiv one_ne_zero) hfp
  refine ⟨B, max L 0, le_max_right _ _, hB, fun x y => ?_⟩
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hg.differentiable one_ne_zero) z) (fun z _ => (hL z).trans (le_max_left L 0))
    (mem_univ y) (mem_univ x)
  simpa using this

/-- A smooth periodic function is `C^{2+β}` for `0 < β ≤ 1`. -/
lemma holderC2_of_smooth_periodic {d : ℕ} (h : Pt d → ℝ) (hh : ContDiff ℝ ∞ h)
    (hp : IsPeriodic h) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : IsHolderC2 β h := by
  refine ⟨hh.of_le (WithTop.coe_le_coe.2 le_top), ?_⟩
  have key : ∀ i j : Fin d, ∃ C, ∀ x y, ‖pd i (pd j h) x - pd i (pd j h) y‖ ≤ C * ‖x - y‖ ^ β := by
    intro i j
    have h3 : ContDiff ℝ 3 h := hh.of_le (WithTop.coe_le_coe.2 le_top)
    have h2 : ContDiff ℝ 2 (pd j h) :=
      (h3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
    have hg : ContDiff ℝ 1 (pd i (pd j h)) := contDiff_pd_of_C2 _ h2 i
    obtain ⟨B, L, hL0, hB, hL⟩ := periodic_C1_lip_bdd _ hg
      (isPeriodic_pd _ (isPeriodic_pd h hp j) i)
    exact ⟨_, holder_of_lip_bdd _ hL0 hB hL hβ0 hβ1⟩
  choose C hC using key
  refine ⟨∑ i, ∑ j, |C i j|, fun i j x y => (hC i j x y).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))⟩
  calc C i j ≤ |C i j| := le_abs_self _
    _ ≤ ∑ j', |C i j'| := Finset.single_le_sum (f := fun j' => |C i j'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |C i' j'| := Finset.single_le_sum (f := fun i' => ∑ j', |C i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- The zero drift is in `C^{β/2,1+β}`. -/
lemma parabolicC01_zero {d : ℕ} (T β : ℝ) : IsParabolicC01 T β (fun (_ : ℝ) (_ : Pt d) => (0 : Pt d)) := by
  refine ⟨fun _ _ => contDiff_const, ⟨0, fun _ _ _ => by simp⟩, ⟨0, fun _ _ _ _ _ => by simp⟩,
    fun i => ⟨0, fun _ _ _ => by simp [pd]⟩, fun i => ⟨0, fun _ _ _ _ _ _ => by simp [pd]⟩⟩

/-- Existence on a single stage, from External Result 1.6 (with `β = 1/2`). -/
lemma stage_exists (hSc : ExternalScalar) {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (v : ℝ → Pt 2 → Pt 2) (hvper : ∀ t ∈ Icc 0 T, IsPeriodic (v t))
    (hvreg : IsParabolicC01 T (1 / 2) v) (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (hp : IsPeriodic θ₀) (hθ₀ : IsHolderC2 (1 / 2) θ₀) :
    ∃ θ, IsParabolicC12 T (1 / 2) θ ∧ IsClassicalScalar T ν v θ₀ θ := by
  obtain ⟨θ, h1, h2, -⟩ := hSc T ν (1 / 2) hT hν (by norm_num) (by norm_num) v hvper hvreg hvdiv
    θ₀ hp hθ₀
  exact ⟨θ, h1, h2⟩

/-! ### Staged problems -/

/-- `θb` solves the staged problem on `[0, T_N]`: it starts from `θ₀` and, for `1 ≤ j ≤ N`,
solves the advection–diffusion equation with drift `D j` (in local time) on `I_j` and the heat
equation on `J_j`. -/
def IsStaged (N : ℕ) (ν : ℝ) (D : ℕ → ℝ → Pt 2 → Pt 2) (θ₀ : Pt 2 → ℝ)
    (θb : ℝ → Pt 2 → ℝ) : Prop :=
  θb 0 = θ₀ ∧ ∀ j, 1 ≤ j → j ≤ N →
    IsClassicalScalar (δs j) ν (D j) (θb (sj j)) (fun t => θb (sj j + t)) ∧
    IsClassicalScalar (ηs j) ν (fun _ _ => 0) (θb (sj j + δs j)) (fun t => θb (sj j + δs j + t))

/-- Propagating a property along the stages. -/
lemma staged_induction (N : ℕ) (Q : ℝ → Prop) (h0 : Q 0)
    (hI : ∀ j, 1 ≤ j → j ≤ N → Q (sj j) → ∀ τ ∈ Icc 0 (δs j), Q (sj j + τ))
    (hJ : ∀ j, 1 ≤ j → j ≤ N → Q (sj j + δs j) → ∀ τ ∈ Icc 0 (ηs j), Q (sj j + δs j + τ)) :
    ∀ t ∈ Icc 0 (TN N), Q t := by
  have key : ∀ j, 1 ≤ j → j ≤ N + 1 → ∀ t ∈ Icc 0 (sj j), Q t := by
    intro j hj hjN
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_or_ge j 1 with h | h
      · obtain rfl : j = 0 := by omega
        intro t ht
        rw [sj_one] at ht
        obtain rfl : t = 0 := le_antisymm ht.2 ht.1
        exact h0
      · have IH := ih h (by omega)
        intro t ht
        rw [sj_succ j h] at ht
        have hs0 := (sj_bounds j).1
        have hQs : Q (sj j) := IH (sj j) ⟨hs0, le_rfl⟩
        rcases le_or_gt t (sj j) with h1 | h1
        · exact IH t ⟨ht.1, h1⟩
        rcases le_or_gt t (sj j + δs j) with h2 | h2
        · have := hI j h (by omega) hQs (t - sj j) ⟨by linarith, by linarith⟩
          simpa using this
        · have hQd : Q (sj j + δs j) := hI j h (by omega) hQs (δs j) ⟨(δs_pos j h).le, le_rfl⟩
          have := hJ j h (by omega) hQd (t - sj j - δs j) ⟨by linarith, by linarith [ht.2]⟩
          simpa using this
  exact key (N + 1) (by omega) le_rfl

/-- The maximum principle for a single classical solution. -/
lemma IsClassicalScalar.abs_le {T ν : ℝ} (hν : 0 ≤ ν) {v : ℝ → Pt 2 → Pt 2} {θ₀ : Pt 2 → ℝ}
    {θ : ℝ → Pt 2 → ℝ} (hθ : IsClassicalScalar T ν v θ₀ θ) {M : ℝ} (hM : ∀ x, |θ₀ x| ≤ M) :
    ∀ t ∈ Icc 0 T, ∀ x, |θ t x| ≤ M := by
  obtain ⟨β, -, -, reg⟩ := hθ.regular
  exact max_principle_abs T ν hν v θ reg.continuousOn hθ.periodic reg.smooth_x reg.diff_t
    hθ.eqn M (by rw [hθ.init]; exact hM)

/-- Uniqueness of the staged solution on `[0, T_N]`. -/
theorem staged_unique {N : ℕ} {ν : ℝ} (hν : 0 ≤ ν) {D : ℕ → ℝ → Pt 2 → Pt 2}
    {θ₀ : Pt 2 → ℝ} {θb θb' : ℝ → Pt 2 → ℝ} (h : IsStaged N ν D θ₀ θb)
    (h' : IsStaged N ν D θ₀ θb') : ∀ t ∈ Icc 0 (TN N), θb t = θb' t := by
  refine staged_induction N (fun t => θb t = θb' t) (by show θb 0 = θb' 0; rw [h.1, h'.1]) ?_ ?_
  · intro j hj hjN hQ τ hτ
    have h2 := (h'.2 j hj hjN).1
    rw [← hQ] at h2
    exact classical_scalar_unique _ ν hν _ _ _ _ (h.2 j hj hjN).1 h2 τ hτ
  · intro j hj hjN hQ τ hτ
    have h2 := (h'.2 j hj hjN).2
    rw [← hQ] at h2
    exact classical_scalar_unique _ ν hν _ _ _ _ (h.2 j hj hjN).2 h2 τ hτ

/-- The maximum principle for the staged solution on `[0, T_N]`. -/
theorem staged_abs_le {N : ℕ} {ν : ℝ} (hν : 0 ≤ ν) {D : ℕ → ℝ → Pt 2 → Pt 2}
    {θ₀ : Pt 2 → ℝ} {θb : ℝ → Pt 2 → ℝ} (h : IsStaged N ν D θ₀ θb) {M : ℝ}
    (hM : ∀ x, |θ₀ x| ≤ M) : ∀ t ∈ Icc 0 (TN N), ∀ x, |θb t x| ≤ M := by
  refine staged_induction N (fun t => ∀ x, |θb t x| ≤ M)
    (by show ∀ x, |θb 0 x| ≤ M; rw [h.1]; exact hM) ?_ ?_
  · intro j hj hjN hQ τ hτ
    exact (h.2 j hj hjN).1.abs_le hν hQ τ hτ
  · intro j hj hjN hQ τ hτ
    exact (h.2 j hj hjN).2.abs_le hν hQ τ hτ

/-! ### The energy identity along the stages -/

/-- Functions that are continuous in space and Hölder in time (uniformly in space) are jointly
continuous on `[0,T] × ℝ^d`. -/
lemma continuousOn_of_timeHolder {d : ℕ} {E : Type*} [NormedAddCommGroup E] {T γ : ℝ}
    (hγ : 0 < γ) {g : ℝ → Pt d → E} (hc : ∀ t ∈ Icc 0 T, Continuous (g t))
    (hg : TimeHolder T γ g) :
    ContinuousOn (fun p : ℝ × Pt d => g p.1 p.2) (Icc 0 T ×ˢ univ) := by
  obtain ⟨C, hC⟩ := hg
  rintro ⟨s, y⟩ ⟨hs, -⟩
  have hcy : ContinuousAt (g s) y := (hc s hs).continuousAt
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun p : ℝ × Pt d => |C| * |p.1 - s| ^ γ + ‖g s p.2 - g s y‖)
      (𝓝[Icc 0 T ×ˢ univ] (s, y)) (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ × Pt d => |C| * |p.1 - s| ^ γ) (𝓝 (s, y)) (𝓝 0) := by
      have : Continuous (fun p : ℝ × Pt d => |C| * |p.1 - s| ^ γ) :=
        continuous_const.mul ((Real.continuous_rpow_const hγ.le).comp (by fun_prop))
      have h := this.tendsto (s, y)
      simp only [sub_self, abs_zero, Real.zero_rpow hγ.ne', mul_zero] at h
      exact h
    have h2 : Tendsto (fun p : ℝ × Pt d => ‖g s p.2 - g s y‖) (𝓝 (s, y)) (𝓝 0) := by
      have := (hcy.tendsto.comp (continuous_snd.tendsto (s, y)))
      rw [tendsto_iff_norm_sub_tendsto_zero] at this
      exact this
    simpa using (h1.add h2).mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with p hp
  calc ‖g p.1 p.2 - g s y‖ = ‖(g p.1 p.2 - g s p.2) + (g s p.2 - g s y)‖ := by abel_nf
    _ ≤ ‖g p.1 p.2 - g s p.2‖ + ‖g s p.2 - g s y‖ := norm_add_le _ _
    _ ≤ |C| * |p.1 - s| ^ γ + ‖g s p.2 - g s y‖ := by
        gcongr
        exact (hC p.1 hp.1 s hs p.2).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (abs_nonneg _) _))

/-- Integrals over the cell of jointly continuous functions depend continuously on time. -/
lemma continuousOn_integral_cell {T : ℝ} (hT : 0 ≤ T) (G : ℝ → Pt 2 → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Pt 2 => G p.1 p.2) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun s => ∫ x in cell 2, G s x) (Icc 0 T) := by
  set G' : ℝ → Pt 2 → ℝ := fun s x => G (projIcc 0 T hT s) x
  have hG' : Continuous (Function.uncurry G') := by
    have : Continuous (fun p : ℝ × Pt 2 => ((projIcc 0 T hT p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
    exact hG.comp_continuous this (fun p => ⟨Subtype.mem _, mem_univ _⟩)
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hG' (isCompact_Icc
    (a := (0 : Pt 2)) (b := 1))
  refine hc.continuousOn.congr fun s hs => ?_
  simp only [G', projIcc_of_mem hT hs]
  rfl

/-- The dissipation rate `t ↦ ‖∇θ(t)‖₂²` of a classical solution is continuous on `[0,T]`. -/
lemma IsParabolicC12.continuousOn_gradSq {T β : ℝ} (hT : 0 ≤ T) (hβ : 0 < β)
    {θ : ℝ → Pt 2 → ℝ} (hθ : IsParabolicC12 T β θ) :
    ContinuousOn (fun s => ∫ x in cell 2, gradSq (θ s) x) (Icc 0 T) := by
  refine continuousOn_integral_cell hT _ ?_
  unfold gradSq
  refine continuousOn_finset_sum _ fun i _ => ?_
  refine ContinuousOn.pow ?_ 2
  exact continuousOn_of_timeHolder (by positivity) (g := fun t => pd i (θ t))
    (fun t ht => continuous_pd_of_C1 _ ((hθ.smooth_x t ht).of_le (by norm_num)) i)
    (hθ.holder_d1_time i)

/-- One step of the energy bookkeeping: a stage on `[a, a+T]`. -/
lemma energy_step {T ν a : ℝ} (hT : 0 ≤ T) (v : ℝ → Pt 2 → Pt 2)
    (hvper : ∀ t ∈ Icc 0 T, IsPeriodic (v t)) (hvC1 : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (v t))
    (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0) (θ₀ : Pt 2 → ℝ)
    (θb : ℝ → Pt 2 → ℝ)
    (hcl : IsClassicalScalar T ν v (θb a) (fun t => θb (a + t)))
    (hQ : IntervalIntegrable (fun s => ∫ x in cell 2, gradSq (θb s) x) volume 0 a ∧
      l2sq (θb a) / 2 + dissipation ν θb a = l2sq θ₀ / 2) :
    ∀ τ ∈ Icc 0 T,
      IntervalIntegrable (fun s => ∫ x in cell 2, gradSq (θb s) x) volume 0 (a + τ) ∧
      l2sq (θb (a + τ)) / 2 + dissipation ν θb (a + τ) = l2sq θ₀ / 2 := by
  intro τ hτ
  obtain ⟨β, hβ0, -, reg⟩ := hcl.regular
  set f : ℝ → ℝ := fun s => ∫ x in cell 2, gradSq (θb s) x with hf
  have hg := reg.continuousOn_gradSq hT hβ0
  have hfc : ContinuousOn f (Icc a (a + τ)) := by
    have : ContinuousOn (fun s => (fun r => ∫ x in cell 2, gradSq (θb (a + r)) x) (s - a))
        (Icc a (a + τ)) :=
      (hg.mono (Icc_subset_Icc_right hτ.2)).comp (by fun_prop)
        (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    refine this.congr fun s _ => ?_
    simp [hf]
  have hint : IntervalIntegrable f volume a (a + τ) := by
    refine hfc.intervalIntegrable_of_Icc ?_
    linarith [hτ.1]
  have hE := energy_identity_core T ν v hvper hvC1 hvdiv (θb a) (fun t => θb (a + t)) hcl τ hτ
  have hshift : ∫ s in (0:ℝ)..τ, ∫ x in cell 2, gradSq (θb (a + s)) x = ∫ s in a..a + τ, f s := by
    rw [intervalIntegral.integral_comp_add_left (fun s => ∫ x in cell 2, gradSq (θb s) x) a,
      add_zero]
  refine ⟨hQ.1.trans hint, ?_⟩
  unfold dissipation at hE hQ ⊢
  simp only at hE
  rw [hshift] at hE
  rw [← intervalIntegral.integral_add_adjacent_intervals hQ.1 hint]
  linarith [hQ.2]

/-- The energy identity for the staged solution on `[0, T_N]`. -/
theorem staged_energy {N : ℕ} {ν : ℝ} {D : ℕ → ℝ → Pt 2 → Pt 2}
    (hD : ∀ j, 1 ≤ j → j ≤ N → (∀ t ∈ Icc 0 (δs j), IsPeriodic (D j t)) ∧
      (∀ t ∈ Icc 0 (δs j), ContDiff ℝ 1 (D j t)) ∧
      (∀ t ∈ Icc 0 (δs j), ∀ x, divergence (D j t) x = 0))
    {θ₀ : Pt 2 → ℝ} {θb : ℝ → Pt 2 → ℝ} (h : IsStaged N ν D θ₀ θb) :
    ∀ t ∈ Icc 0 (TN N), l2sq (θb t) / 2 + dissipation ν θb t = l2sq θ₀ / 2 := by
  have key := staged_induction N (fun t =>
      IntervalIntegrable (fun s => ∫ x in cell 2, gradSq (θb s) x) volume 0 t ∧
      l2sq (θb t) / 2 + dissipation ν θb t = l2sq θ₀ / 2)
    ⟨IntervalIntegrable.refl, by simp [dissipation, h.1]⟩ ?_ ?_
  · exact fun t ht => (key t ht).2
  · intro j hj hjN hQ τ hτ
    obtain ⟨h1, h2, h3⟩ := hD j hj hjN
    exact energy_step (δs_pos j hj).le (D j) h1 h2 h3 θ₀ θb
      (h.2 j hj hjN).1 hQ τ hτ
  · intro j hj hjN hQ τ hτ
    exact energy_step (ηs_pos j hj).le (fun _ _ => 0) (fun _ _ _ _ => rfl) (fun _ _ => contDiff_const)
      (fun _ _ _ => by simp [divergence, pd]) θ₀ θb (h.2 j hj hjN).2 hQ τ hτ

/-! ### Existence of the staged solution -/

section existence

variable (ν : ℝ) (D : ℕ → ℝ → Pt 2 → Pt 2) (θ₀ : Pt 2 → ℝ)

/-- A chosen solution on a single stage (with `β = 1/2`). -/
def stageSol (T : ℝ) (v : ℝ → Pt 2 → Pt 2) (h : Pt 2 → ℝ) : ℝ → Pt 2 → ℝ :=
  Classical.epsilon fun θ => IsParabolicC12 T (1 / 2) θ ∧ IsClassicalScalar T ν v h θ

/-- The data at the start `s_j` of stage `j`. -/
def stageData : ℕ → Pt 2 → ℝ
  | 0 => θ₀
  | j + 1 => if j = 0 then θ₀ else
      stageSol ν (ηs j) (fun _ _ => 0) (stageSol ν (δs j) (D j) (stageData j) (δs j)) (ηs j)

/-- The pulse-stage solution of stage `j`. -/
def stageP (j : ℕ) : ℝ → Pt 2 → ℝ := stageSol ν (δs j) (D j) (stageData ν D θ₀ j)

/-- The heat-stage solution of stage `j`. -/
def stageQ (j : ℕ) : ℝ → Pt 2 → ℝ := stageSol ν (ηs j) (fun _ _ => 0) (stageP ν D θ₀ j (δs j))

open Classical in
/-- The glued staged solution. -/
def stagedSol (N : ℕ) (t : ℝ) : Pt 2 → ℝ :=
  let J := Nat.findGreatest (fun j => sj j ≤ t) N
  if t < sj J + δs J then stageP ν D θ₀ J (t - sj J) else stageQ ν D θ₀ J (t - sj J - δs J)

end existence

lemma stageSol_spec (hSc : ExternalScalar) {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (v : ℝ → Pt 2 → Pt 2) (hvper : ∀ t ∈ Icc 0 T, IsPeriodic (v t))
    (hvreg : IsParabolicC01 T (1 / 2) v) (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0)
    (h : Pt 2 → ℝ) (hp : IsPeriodic h) (hh : IsHolderC2 (1 / 2) h) :
    IsParabolicC12 T (1 / 2) (stageSol ν T v h) ∧ IsClassicalScalar T ν v h (stageSol ν T v h) :=
  Classical.epsilon_spec (stage_exists hSc hT hν v hvper hvreg hvdiv h hp hh)

lemma sj_lt_succ (j : ℕ) (hj : 1 ≤ j) : sj j + δs j < sj (j + 1) := by
  rw [sj_succ j hj]; linarith [ηs_pos j hj]

lemma findGreatest_stage {N j : ℕ} (hjN : j ≤ N) {t : ℝ} (ht : sj j ≤ t)
    (ht' : j < N → t < sj (j + 1)) :
    Nat.findGreatest (fun k => sj k ≤ t) N = j := by
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hjN, fun _ => ht, fun k hk hkN => ?_⟩
  have h1 := ht' (by omega)
  have h2 : sj (j + 1) ≤ sj k := sj_mono (by omega)
  simp only [not_le]
  linarith

/-- Existence of the staged solution, from External Result 1.6. -/
theorem staged_exists (hSc : ExternalScalar) (N : ℕ) {ν : ℝ} (hν : 0 < ν)
    (D : ℕ → ℝ → Pt 2 → Pt 2)
    (hD : ∀ j, 1 ≤ j → j ≤ N → (∀ t ∈ Icc 0 (δs j), IsPeriodic (D j t)) ∧
      IsParabolicC01 (δs j) (1 / 2) (D j) ∧ (∀ t ∈ Icc 0 (δs j), ∀ x, divergence (D j t) x = 0))
    (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) :
    ∃ θb, IsStaged N ν D θ₀ θb := by
  -- regularity of the data and specification of the stage solutions
  have hgood : ∀ j, 1 ≤ j → j ≤ N →
      (IsPeriodic (stageData ν D θ₀ j) ∧ IsHolderC2 (1 / 2) (stageData ν D θ₀ j)) ∧
      (IsParabolicC12 (δs j) (1 / 2) (stageP ν D θ₀ j) ∧
        IsClassicalScalar (δs j) ν (D j) (stageData ν D θ₀ j) (stageP ν D θ₀ j)) ∧
      (IsParabolicC12 (ηs j) (1 / 2) (stageQ ν D θ₀ j) ∧
        IsClassicalScalar (ηs j) ν (fun _ _ => 0) (stageP ν D θ₀ j (δs j)) (stageQ ν D θ₀ j)) := by
    intro j hj hjN
    induction j with
    | zero => omega
    | succ j ih =>
      have hdata : IsPeriodic (stageData ν D θ₀ (j + 1)) ∧
          IsHolderC2 (1 / 2) (stageData ν D θ₀ (j + 1)) := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          simp only [stageData, if_true]
          exact ⟨hp, holderC2_of_smooth_periodic θ₀ hθ₀ hp (by norm_num) (by norm_num)⟩
        · obtain ⟨-, -, hQ1, hQ2⟩ := ih h0 (by omega)
          have e : stageData ν D θ₀ (j + 1) = stageQ ν D θ₀ j (ηs j) := by
            simp only [stageData, if_neg (show j ≠ 0 by omega)]; rfl
          rw [e]
          have hm : ηs j ∈ Icc 0 (ηs j) := ⟨(ηs_pos j h0).le, le_rfl⟩
          exact ⟨hQ2.periodic _ hm, hQ1.holderC2_slice (by norm_num) hm⟩
      obtain ⟨hD1, hD2, hD3⟩ := hD (j + 1) hj hjN
      have hP := stageSol_spec hSc hν (δs_pos (j + 1) hj) (D (j + 1)) hD1 hD2 hD3 _ hdata.1
        hdata.2
      have hm : δs (j + 1) ∈ Icc 0 (δs (j + 1)) := ⟨(δs_pos (j + 1) hj).le, le_rfl⟩
      have hQ := stageSol_spec hSc hν (ηs_pos (j + 1) hj) (fun _ _ => 0) (fun _ _ _ _ => rfl)
        (parabolicC01_zero _ _) (fun _ _ _ => by simp [divergence, pd]) _
        (hP.2.periodic _ hm) (hP.1.holderC2_slice (by norm_num) hm)
      exact ⟨hdata, hP, hQ⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact ⟨fun _ => θ₀, rfl, fun j hj hjN => by omega⟩
  refine ⟨stagedSol ν D θ₀ N, ?_, fun j hj hjN => ?_⟩
  · -- the initial value
    have hJ : Nat.findGreatest (fun k => sj k ≤ 0) N = 1 := by
      refine findGreatest_stage hN (by rw [sj_one]) fun _ => ?_
      rw [sj_succ 1 le_rfl, sj_one]; linarith [δs_pos 1 le_rfl, ηs_pos 1 le_rfl]
    have hP := (hgood 1 le_rfl hN).2.1.2
    simp only [stagedSol, hJ, sj_one, zero_add, sub_zero, if_pos (δs_pos 1 le_rfl)]
    rw [hP.init]
    simp [stageData]
  · obtain ⟨-, ⟨hP1, hP2⟩, ⟨hQ1, hQ2⟩⟩ := hgood j hj hjN
    have hδ := δs_pos j hj
    have hη := ηs_pos j hj
    have hlt := sj_lt_succ j hj
    -- values on the pulse stage
    have hI : ∀ τ ∈ Icc 0 (δs j), stagedSol ν D θ₀ N (sj j + τ) = stageP ν D θ₀ j τ := by
      intro τ hτ
      have hJ := findGreatest_stage (t := sj j + τ) hjN (by linarith [hτ.1])
        (fun _ => by linarith [hτ.2])
      rcases eq_or_lt_of_le hτ.2 with h | h
      · subst h
        simp only [stagedSol, hJ, lt_irrefl, if_false, add_sub_cancel_left, sub_self]
        rw [hQ2.init]
      · simp only [stagedSol, hJ, add_lt_add_iff_left, h, if_true, add_sub_cancel_left]
    have hJv : ∀ τ ∈ Icc 0 (ηs j),
        stagedSol ν D θ₀ N (sj j + δs j + τ) = stageQ ν D θ₀ j τ := by
      intro τ hτ
      rcases eq_or_lt_of_le hτ.2 with h | h
      · subst h
        rw [← sj_succ j hj]
        have hnlt : ¬ (sj (j + 1) < sj j + δs j) := not_lt.2 hlt.le
        rcases eq_or_lt_of_le hjN with hN' | hN'
        · have hJ : Nat.findGreatest (fun k => sj k ≤ sj (j + 1)) N = j :=
            findGreatest_stage hjN (sj_mono (by omega)) (fun h => absurd h (by omega))
          simp only [stagedSol, hJ, hnlt, if_false]
          congr 1
          rw [sj_succ j hj]; ring
        · have hJ : Nat.findGreatest (fun k => sj k ≤ sj (j + 1)) N = j + 1 :=
            findGreatest_stage hN' le_rfl (fun _ => by
              linarith [sj_lt_succ (j + 1) (by omega), δs_pos (j + 1) (by omega)])
          have hP' := (hgood (j + 1) (by omega) hN').2.1.2
          simp only [stagedSol, hJ, sub_self, lt_add_iff_pos_right,
            if_pos (δs_pos (j + 1) (by omega))]
          rw [hP'.init]
          simp [stageData, show j ≠ 0 by omega, stageQ, stageP]
      · have hJ := findGreatest_stage (t := sj j + δs j + τ) hjN (by linarith [hτ.1])
          (fun _ => by rw [sj_succ j hj]; linarith)
        have : ¬ (sj j + δs j + τ < sj j + δs j) := by linarith [hτ.1]
        simp only [stagedSol, hJ, this, if_false]
        congr 1; ring
    have hinit : stagedSol ν D θ₀ N (sj j) = stageData ν D θ₀ j := by
      have := hI 0 ⟨le_rfl, hδ.le⟩
      rw [add_zero] at this
      rw [this, hP2.init]
    have hmid : stagedSol ν D θ₀ N (sj j + δs j) = stageP ν D θ₀ j (δs j) :=
      hI (δs j) ⟨hδ.le, le_rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hinit]; exact hP2.congr hδ.le hI
    · rw [hmid]; exact hQ2.congr hη.le hJv

end AnomDiss
