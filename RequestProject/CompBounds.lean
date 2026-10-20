module

public import Mathlib

/-!
# Higher derivative bounds for long compositions of near-identity maps

A quantitative Faà di Bruno estimate and its consequence: a composition of `n` maps whose
derivatives satisfy `‖Df‖ ≤ 1 + δ`, `‖D^r f‖ ≤ δ b` (`2 ≤ r ≤ m`) with `n δ ≤ c` has all
derivatives of order `1 … m` bounded by a constant depending only on `m`, `b`, `c`.
-/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative Faà di Bruno. -/
theorem norm_iteratedFDeriv_comp_le_faa {g f : E → E} {m : ℕ} (hg : ContDiff ℝ m g)
    (hf : ContDiff ℝ m f) (x : E) {k : ℕ} (hk : k ≤ m) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ ∑ c : OrderedFinpartition k,
      ‖iteratedFDeriv ℝ c.length g (f x)‖ * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) f x‖ := by
  rw [iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt (by exact_mod_cast hk)]
  unfold FormalMultilinearSeries.taylorComp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  exact c.norm_compAlongOrderedFinpartition_le _ _


lemma _root_.OrderedFinpartition.sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  have := c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
  simpa using this

lemma _root_.OrderedFinpartition.eq_atomic {n : ℕ} (c : OrderedFinpartition n)
    (h : ∀ i, c.partSize i = 1) : c = OrderedFinpartition.atomic n := by
  have hsum := c.sum_partSize
  obtain ⟨len, size, pos, emb, mono, pmono, disj, cover⟩ := c
  simp only at h hsum
  obtain rfl : size = fun _ => 1 := funext h
  simp at hsum
  subst hsum
  have hid : (fun m => emb m ⟨0, Nat.zero_lt_one⟩) = id := by
    have pm : StrictMono (fun m => emb m ⟨0, Nat.zero_lt_one⟩) := pmono
    have hs := Finite.injective_iff_surjective.1 pm.injective
    have h2 : StrictMono.orderIsoOfSurjective _ pm hs = OrderIso.refl _ := Subsingleton.elim _ _
    funext i
    exact congrArg (fun e : Fin len ≃o Fin len => e i) h2
  have key : ∀ m r, emb m r = m := by
    intro m r
    have hr : r = ⟨0, Nat.zero_lt_one⟩ := Subsingleton.elim _ _
    subst hr
    exact congrFun hid m
  have : emb = fun m _ => m := funext fun m => funext fun r => key m r
  subst this
  rfl

/-- A non-atomic ordered finpartition has a part of size at least `2` and fewer parts. -/
lemma _root_.OrderedFinpartition.length_lt_of_ne_atomic {n : ℕ} (c : OrderedFinpartition n)
    (hc : c ≠ OrderedFinpartition.atomic n) :
    c.length < n ∧ ∃ i, 2 ≤ c.partSize i := by
  have hex : ∃ i, 2 ≤ c.partSize i := by
    by_contra hne
    push_neg at hne
    exact hc (c.eq_atomic fun i => by have := c.partSize_pos i; have := hne i; omega)
  refine ⟨?_, hex⟩
  obtain ⟨i, hi⟩ := hex
  have hsum := c.sum_partSize
  have : ∑ j, c.partSize j = c.partSize i + ∑ j ∈ Finset.univ.erase i, c.partSize j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have h2 : (Finset.univ.erase i).card ≤ ∑ j ∈ Finset.univ.erase i, c.partSize j := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun j _ => c.partSize_pos j
  have h3 : (Finset.univ.erase i).card = c.length - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have : 0 < c.length := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  omega

/-- Each part of an ordered finpartition with at least two parts is a proper subset. -/
lemma _root_.OrderedFinpartition.partSize_lt_of_two_le {n : ℕ} (c : OrderedFinpartition n)
    (hc : 2 ≤ c.length) (i : Fin c.length) : c.partSize i < n := by
  have hsum := c.sum_partSize
  have : ∑ j, c.partSize j = c.partSize i + ∑ j ∈ Finset.univ.erase i, c.partSize j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  obtain ⟨j, hj⟩ : ∃ j : Fin c.length, j ≠ i := by
    by_cases h : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  have : c.partSize j ≤ ∑ j ∈ Finset.univ.erase i, c.partSize j :=
    Finset.single_le_sum (f := c.partSize) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
  have := c.partSize_pos j
  omega

/-- Product bound: all factors at most `A ≥ 1`, one factor at most `a`. -/
lemma prod_le_of_one_small {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (hu0 : ∀ i, 0 ≤ u i) {A a : ℝ} (hA : 1 ≤ A) (huA : ∀ i, u i ≤ A) (i₀ : ι) (hi₀ : u i₀ ≤ a)
    {N : ℕ} (hN : Fintype.card ι ≤ N) : ∏ i, u i ≤ a * A ^ N := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  have ha : 0 ≤ a := (hu0 i₀).trans hi₀
  refine mul_le_mul hi₀ ?_ (Finset.prod_nonneg fun i _ => hu0 i) ha
  calc ∏ i ∈ Finset.univ.erase i₀, u i ≤ A ^ (Finset.univ.erase i₀).card :=
        (Finset.prod_le_prod₀ (fun i _ => hu0 i) (fun i _ => huA i)).trans_eq (Finset.prod_const _)
    _ ≤ A ^ N := pow_le_pow_right₀ hA (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega)

/-- Product bound: all factors at most `A ≥ 1`. -/
lemma prod_le_pow_of_le {ι : Type*} [Fintype ι] (u : ι → ℝ) (hu0 : ∀ i, 0 ≤ u i) {A : ℝ}
    (hA : 1 ≤ A) (huA : ∀ i, u i ≤ A) {N : ℕ} (hN : Fintype.card ι ≤ N) : ∏ i, u i ≤ A ^ N :=
  calc ∏ i, u i ≤ A ^ (Finset.univ : Finset ι).card :=
        (Finset.prod_le_prod₀ (fun i _ => hu0 i) (fun i _ => huA i)).trans_eq (Finset.prod_const _)
    _ ≤ A ^ N := pow_le_pow_right₀ hA (by rw [Finset.card_univ]; exact hN)

/-- The elementary recursion `X_{j+1} ≤ (1+δ)^q X_j + δ D`. -/
lemma rec_bound_step {δ D : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (q j : ℕ) :
    (1 + δ) ^ q * ((1 + j * δ * D) * (1 + δ) ^ (q * j)) + δ * D ≤
      (1 + (j + 1 : ℕ) * δ * D) * (1 + δ) ^ (q * (j + 1)) := by
  have h1 : 1 ≤ (1 + δ) ^ (q * (j + 1)) := one_le_pow₀ (by linarith)
  have e : (1 + δ) ^ q * (1 + δ) ^ (q * j) = (1 + δ) ^ (q * (j + 1)) := by
    rw [← pow_add]; ring_nf
  push_cast
  have : (1 + δ) ^ q * ((1 + j * δ * D) * (1 + δ) ^ (q * j)) =
      (1 + j * δ * D) * (1 + δ) ^ (q * (j + 1)) := by rw [← e]; ring
  rw [this]
  nlinarith [mul_nonneg hδ hD]

lemma rec_bound_final {δ D c : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (q j : ℕ) (hj : j * δ ≤ c) :
    (1 + j * δ * D) * (1 + δ) ^ (q * j) ≤ (1 + c * D) * Real.exp (q * c) := by
  have hc : 0 ≤ c := (mul_nonneg (Nat.cast_nonneg j) hδ).trans hj
  refine mul_le_mul (by nlinarith) ?_ (by positivity) (by positivity)
  calc (1 + δ) ^ (q * j) ≤ Real.exp δ ^ (q * j) := by
          gcongr; linarith [Real.add_one_le_exp δ]
    _ = Real.exp (q * (j * δ)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ Real.exp (q * c) := by gcongr

/-- Composition appending maps on the right: `compR f (j+1) = compR f j ∘ f (j+1)`. -/
def compR (f : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | j + 1 => compR f j ∘ f (j + 1)

/-- Composition appending maps on the left: `compL f (j+1) = f (j+1) ∘ compL f j`. -/
def compL (f : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | j + 1 => f (j + 1) ∘ compL f j

lemma norm_iteratedFDeriv_id_le (x : E) {r : ℕ} (hr : 1 ≤ r) :
    ‖iteratedFDeriv ℝ r (id : E → E) x‖ ≤ 1 := by
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    rw [norm_iteratedFDeriv_one, fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  · have : iteratedFDeriv ℝ r (id : E → E) x = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp [iteratedFDeriv_const_of_ne]
    rw [this, norm_zero]; exact zero_le_one

/-- One step of the right composition estimate. -/
lemma comp_right_step {G f : E → E} {m R : ℕ} (hRm : R ≤ m)
    (hG : ContDiff ℝ m G) (hf : ContDiff ℝ m f) {δ b c Y S : ℝ} (hδ : 0 ≤ δ) (hδc : δ ≤ c)
    (hb : 0 ≤ b) (hY : 1 ≤ Y)
    (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ 1 + δ)
    (hfr : ∀ x r, 2 ≤ r → r ≤ m → ‖iteratedFDeriv ℝ r f x‖ ≤ δ * b)
    (hGlow : ∀ y l, 1 ≤ l → l < R → ‖iteratedFDeriv ℝ l G y‖ ≤ Y)
    (hGR : ∀ y, ‖iteratedFDeriv ℝ R G y‖ ≤ S) (x : E) :
    ‖iteratedFDeriv ℝ R (G ∘ f) x‖ ≤ (1 + δ) ^ R * S +
      δ * (Fintype.card (OrderedFinpartition R) * (Y * b * (1 + c + c * b) ^ R)) := by
  classical
  have hc : 0 ≤ c := hδ.trans hδc
  set A := 1 + c + c * b with hA
  have hA1 : 1 ≤ A := by nlinarith
  have hfA : ∀ s, 1 ≤ s → s ≤ m → ‖iteratedFDeriv ℝ s f x‖ ≤ A := by
    intro s hs1 hsm
    rcases Nat.lt_or_ge s 2 with h | h
    · obtain rfl : s = 1 := by omega
      rw [norm_iteratedFDeriv_one]; refine (hf1 x).trans ?_; nlinarith
    · refine (hfr x s h hsm).trans ?_; nlinarith
  refine (norm_iteratedFDeriv_comp_le_faa hG hf x hRm).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (OrderedFinpartition.atomic R))]
  refine add_le_add ?_ ?_
  · -- the atomic term
    change ‖iteratedFDeriv ℝ R G (f x)‖ *
      (∏ _i : Fin R, ‖iteratedFDeriv ℝ 1 f x‖) ≤ (1 + δ) ^ R * S
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_iteratedFDeriv_one, mul_comm]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hf1 x) R) (hGR _) (norm_nonneg _)
      (by positivity)
  · -- the non-atomic terms
    have hterm : ∀ c' ∈ Finset.univ.erase (OrderedFinpartition.atomic R),
        ‖iteratedFDeriv ℝ c'.length G (f x)‖ * ∏ i, ‖iteratedFDeriv ℝ (c'.partSize i) f x‖ ≤
          δ * (Y * b * A ^ R) := by
      intro c' hc'
      obtain ⟨hlen, i₀, hi₀⟩ := c'.length_lt_of_ne_atomic (Finset.ne_of_mem_erase hc')
      have hl1 : 1 ≤ c'.length := Nat.lt_of_le_of_lt (Nat.zero_le _) i₀.2
      have h1 := hGlow (f x) c'.length hl1 hlen
      have h2 : ∏ i, ‖iteratedFDeriv ℝ (c'.partSize i) f x‖ ≤ (δ * b) * A ^ R :=
        prod_le_of_one_small _ (fun i => norm_nonneg _) hA1
          (fun i => hfA _ (c'.partSize_pos i) ((c'.partSize_le i).trans hRm)) i₀
          (hfr x _ hi₀ ((c'.partSize_le i₀).trans hRm))
          (by rw [Fintype.card_fin]; exact hlen.le)
      calc _ ≤ Y * ((δ * b) * A ^ R) :=
            mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => norm_nonneg _) (by linarith)
        _ = δ * (Y * b * A ^ R) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.erase (OrderedFinpartition.atomic R)).card : ℝ) ≤
        Fintype.card (OrderedFinpartition R) := by
      exact_mod_cast (Finset.card_erase_le).trans (by rw [Finset.card_univ])
    have : 0 ≤ δ * (Y * b * A ^ R) := by positivity
    nlinarith

lemma iteratedFDeriv_sub_id {g : E → E} {m : ℕ} (hg : ContDiff ℝ m g) (x : E) {r : ℕ}
    (hr2 : 2 ≤ r) (hrm : r ≤ m) :
    iteratedFDeriv ℝ r (fun y => g y - y) x = iteratedFDeriv ℝ r g x := by
  have h1 : ContDiffAt ℝ r g x := (hg.of_le (by exact_mod_cast hrm)).contDiffAt
  have hid : iteratedFDeriv ℝ r (id : E → E) x = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [iteratedFDeriv_const_of_ne]
  have e : (fun y => g y - y) = g + (-id) := by funext y; simp [sub_eq_add_neg]
  have h3 : ContDiffAt ℝ r (-id : E → E) x := by exact contDiff_neg.contDiffAt
  rw [e, iteratedFDeriv_add_apply h1 h3, iteratedFDeriv_neg_apply, hid,
    neg_zero, add_zero]

/-- One step of the left composition estimate. -/
lemma comp_left_step {g H : E → E} {m R : ℕ} (hR1 : 1 ≤ R) (hRm : R ≤ m)
    (hg : ContDiff ℝ m g) (hH : ContDiff ℝ m H) {δ b Y S : ℝ} (hδ : 0 ≤ δ)
    (hb : 0 ≤ b) (hY : 1 ≤ Y) (hS : 0 ≤ S)
    (hg1 : ∀ x, ‖fderiv ℝ g x - ContinuousLinearMap.id ℝ E‖ ≤ δ)
    (hgr : ∀ x r, 2 ≤ r → r ≤ m → ‖iteratedFDeriv ℝ r g x‖ ≤ δ * b)
    (hHlow : ∀ y l, 1 ≤ l → l < R → ‖iteratedFDeriv ℝ l H y‖ ≤ Y)
    (hHR : ∀ y, ‖iteratedFDeriv ℝ R H y‖ ≤ S) (x : E) :
    ‖iteratedFDeriv ℝ R (g ∘ H) x‖ ≤ (1 + δ) ^ Fintype.card (OrderedFinpartition R) * S +
      δ * (Fintype.card (OrderedFinpartition R) * (b * Y ^ R)) := by
  classical
  set N := Fintype.card (OrderedFinpartition R)
  set u : E → E := fun y => g y - y with hu
  have hum : ContDiff ℝ m u := hg.sub contDiff_id
  have hsplit : g ∘ H = fun y => H y + (u ∘ H) y := by
    funext y; simp [hu]
  have hRm' : (R : WithTop ℕ∞) ≤ m := by exact_mod_cast hRm
  rw [hsplit]
  change ‖iteratedFDeriv ℝ R (H + u ∘ H) x‖ ≤ _
  rw [iteratedFDeriv_add_apply ((hH.of_le hRm').contDiffAt)
    (((hum.comp hH).of_le hRm').contDiffAt)]
  have hu1 : ∀ y, ‖iteratedFDeriv ℝ 1 u y‖ ≤ δ := by
    intro y
    rw [norm_iteratedFDeriv_one]
    have hgd : Differentiable ℝ g := hg.differentiable (by exact_mod_cast (by omega : m ≠ 0))
    have : fderiv ℝ u y = fderiv ℝ g y - ContinuousLinearMap.id ℝ E :=
      ((hgd y).hasFDerivAt.sub (hasFDerivAt_id y)).fderiv
    rw [this]; exact hg1 y
  have hur : ∀ y r, 2 ≤ r → r ≤ m → ‖iteratedFDeriv ℝ r u y‖ ≤ δ * b := by
    intro y r hr2 hrm
    rw [iteratedFDeriv_sub_id hg y hr2 hrm]; exact hgr y r hr2 hrm
  have hcomp : ‖iteratedFDeriv ℝ R (u ∘ H) x‖ ≤ N * (δ * S + δ * (b * Y ^ R)) := by
    refine (norm_iteratedFDeriv_comp_le_faa hum hH x hRm).trans ?_
    have hterm : ∀ c : OrderedFinpartition R,
        ‖iteratedFDeriv ℝ c.length u (H x)‖ * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) H x‖ ≤
          δ * S + δ * (b * Y ^ R) := by
      intro c
      have hl1 : 1 ≤ c.length := c.length_pos (by omega)
      rcases Nat.lt_or_ge c.length 2 with hl | hl
      · have hl' : c.length = 1 := by omega
        have hsum := c.sum_partSize
        have hprod : ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) H x‖ ≤ S := by
          have e : ∀ i : Fin c.length, c.partSize i = R := by
            intro i
            have : (Finset.univ : Finset (Fin c.length)) = {i} := by
              ext j; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
              exact Fin.ext (by omega)
            rw [this, Finset.sum_singleton] at hsum; exact hsum
          have : (Finset.univ : Finset (Fin c.length)) = {⟨0, by omega⟩} := by
            ext j; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
            exact Fin.ext (by omega)
          rw [this, Finset.prod_singleton, e]; exact hHR x
        have h1 : ‖iteratedFDeriv ℝ c.length u (H x)‖ ≤ δ := by rw [hl']; exact hu1 _
        have : 0 ≤ δ * (b * Y ^ R) := by positivity
        calc _ ≤ δ * S := mul_le_mul h1 hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) hδ
          _ ≤ _ := by linarith
      · have h1 := hur (H x) c.length hl (c.length_le.trans hRm)
        have hprod : ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) H x‖ ≤ Y ^ R :=
          prod_le_pow_of_le _ (fun _ => norm_nonneg _) hY
            (fun i => hHlow _ _ (c.partSize_pos i) (c.partSize_lt_of_two_le hl i))
            (by rw [Fintype.card_fin]; exact c.length_le)
        have : 0 ≤ δ * S := by positivity
        calc _ ≤ (δ * b) * Y ^ R :=
              mul_le_mul h1 hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
          _ ≤ _ := by nlinarith
    refine (Finset.sum_le_sum fun c _ => hterm c).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (hHR x) hcomp).trans ?_
  have hb' : 1 + (N : ℝ) * δ ≤ (1 + δ) ^ N := one_add_mul_le_pow (by linarith) N
  nlinarith

/-- A `C^m` map whose derivative is within `δ` of the identity and whose derivatives of orders
`2 … m` are at most `δ b`. -/
structure NearId (m : ℕ) (δ b : ℝ) (f : E → E) : Prop where
  smooth : ContDiff ℝ m f
  d1 : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ δ
  dr : ∀ x r, 2 ≤ r → r ≤ m → ‖iteratedFDeriv ℝ r f x‖ ≤ δ * b

lemma NearId.norm_fderiv_le {m : ℕ} {δ b : ℝ} {f : E → E} (h : NearId m δ b f) (x : E) :
    ‖fderiv ℝ f x‖ ≤ 1 + δ := by
  have := h.d1 x
  calc ‖fderiv ℝ f x‖ = ‖(fderiv ℝ f x - ContinuousLinearMap.id ℝ E) +
        ContinuousLinearMap.id ℝ E‖ := by rw [sub_add_cancel]
    _ ≤ δ + 1 := (norm_add_le _ _).trans (add_le_add this ContinuousLinearMap.norm_id_le)
    _ = 1 + δ := add_comm _ _

lemma contDiff_compR {m : ℕ} {f : ℕ → E → E} (hf : ∀ i, ContDiff ℝ m (f i)) (j : ℕ) :
    ContDiff ℝ m (compR f j) := by
  induction j with
  | zero => exact contDiff_id
  | succ j ih => exact ih.comp (hf _)

lemma contDiff_compL {m : ℕ} {f : ℕ → E → E} (hf : ∀ i, ContDiff ℝ m (f i)) (j : ℕ) :
    ContDiff ℝ m (compL f j) := by
  induction j with
  | zero => exact contDiff_id
  | succ j ih => exact (hf _).comp ih

/-- **Uniform derivative bounds for right compositions** `f₁ ∘ ⋯ ∘ fⱼ`. -/
theorem compR_bounds (m : ℕ) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ C, ∀ (δ : ℝ) (n : ℕ), 0 ≤ δ → n * δ ≤ c → ∀ f : ℕ → E → E,
      (∀ i, NearId m δ b (f i)) → ∀ j ≤ n, ∀ x r, 1 ≤ r → r ≤ m →
        ‖iteratedFDeriv ℝ r (compR f j) x‖ ≤ C := by
  suffices H : ∀ k, k ≤ m → ∃ C, 1 ≤ C ∧ ∀ (δ : ℝ) (n : ℕ), 0 ≤ δ → n * δ ≤ c →
      ∀ f : ℕ → E → E, (∀ i, NearId m δ b (f i)) → ∀ j ≤ n, ∀ x r, 1 ≤ r → r ≤ k →
        ‖iteratedFDeriv ℝ r (compR f j) x‖ ≤ C by
    obtain ⟨C, -, hC⟩ := H m le_rfl
    exact ⟨C, hC⟩
  intro k
  induction k with
  | zero => intro _; exact ⟨1, le_rfl, fun _ _ _ _ _ _ _ _ _ r h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro hkm
    obtain ⟨Y, hY, hYb⟩ := ih (by omega)
    set R := k + 1 with hR
    set D := (Fintype.card (OrderedFinpartition R) : ℝ) * (Y * b * (1 + c + c * b) ^ R) with hD
    have hD0 : 0 ≤ D := by positivity
    refine ⟨max Y ((1 + c * D) * Real.exp (R * c)), le_max_of_le_left hY, ?_⟩
    intro δ n hδ hn f hf j hj x r hr1 hrk
    rcases Nat.lt_or_ge r R with hrR | hrR
    · exact (hYb δ n hδ hn f hf j hj x r hr1 (by omega)).trans (le_max_left _ _)
    obtain rfl : r = R := by omega
    refine le_max_of_le_right ?_
    have hcomp := fun j => contDiff_compR (fun i => (hf i).smooth) j
    have key : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ R (compR f j) x‖ ≤
        (1 + j * δ * D) * (1 + δ) ^ (R * j) := by
      intro j
      induction j with
      | zero =>
        intro _ x
        simp only [compR, Nat.cast_zero, zero_mul, add_zero, mul_zero, pow_zero, one_mul]
        exact norm_iteratedFDeriv_id_le x (by omega)
      | succ j ihj =>
        intro hj x
        have hδc : δ ≤ c := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          nlinarith
        refine (comp_right_step hkm (hcomp j) (hf (j + 1)).smooth hδ hδc hb hY
          (hf (j + 1)).norm_fderiv_le (hf (j + 1)).dr
          (fun y l hl1 hlR => hYb δ n hδ hn f hf j (by omega) y l hl1 (by omega))
          (ihj (by omega)) x).trans ?_
        exact rec_bound_step hδ hD0 R j
    refine (key j hj x).trans (rec_bound_final hδ hD0 R j ?_)
    calc (j : ℝ) * δ ≤ n * δ := by gcongr
      _ ≤ c := hn

/-- **Uniform derivative bounds for left compositions** `fⱼ ∘ ⋯ ∘ f₁`. -/
theorem compL_bounds (m : ℕ) {b : ℝ} (c : ℝ) (hb : 0 ≤ b) :
    ∃ C, ∀ (δ : ℝ) (n : ℕ), 0 ≤ δ → n * δ ≤ c → ∀ f : ℕ → E → E,
      (∀ i, NearId m δ b (f i)) → ∀ j ≤ n, ∀ x r, 1 ≤ r → r ≤ m →
        ‖iteratedFDeriv ℝ r (compL f j) x‖ ≤ C := by
  suffices H : ∀ k, k ≤ m → ∃ C, 1 ≤ C ∧ ∀ (δ : ℝ) (n : ℕ), 0 ≤ δ → n * δ ≤ c →
      ∀ f : ℕ → E → E, (∀ i, NearId m δ b (f i)) → ∀ j ≤ n, ∀ x r, 1 ≤ r → r ≤ k →
        ‖iteratedFDeriv ℝ r (compL f j) x‖ ≤ C by
    obtain ⟨C, -, hC⟩ := H m le_rfl
    exact ⟨C, hC⟩
  intro k
  induction k with
  | zero => intro _; exact ⟨1, le_rfl, fun _ _ _ _ _ _ _ _ _ r h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro hkm
    obtain ⟨Y, hY, hYb⟩ := ih (by omega)
    set R := k + 1 with hR
    set N := Fintype.card (OrderedFinpartition R)
    set D := (N : ℝ) * (b * Y ^ R) with hD
    have hD0 : 0 ≤ D := by positivity
    refine ⟨max Y ((1 + c * D) * Real.exp (N * c)), le_max_of_le_left hY, ?_⟩
    intro δ n hδ hn f hf j hj x r hr1 hrk
    rcases Nat.lt_or_ge r R with hrR | hrR
    · exact (hYb δ n hδ hn f hf j hj x r hr1 (by omega)).trans (le_max_left _ _)
    obtain rfl : r = R := by omega
    refine le_max_of_le_right ?_
    have hcomp := fun j => contDiff_compL (fun i => (hf i).smooth) j
    have key : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ R (compL f j) x‖ ≤
        (1 + j * δ * D) * (1 + δ) ^ (N * j) := by
      intro j
      induction j with
      | zero =>
        intro _ x
        simp only [compL, Nat.cast_zero, zero_mul, add_zero, mul_zero, pow_zero, one_mul]
        exact norm_iteratedFDeriv_id_le x (by omega)
      | succ j ihj =>
        intro hj x
        have hS : 0 ≤ (1 + j * δ * D) * (1 + δ) ^ (N * j) := by positivity
        refine (comp_left_step (by omega) hkm (hf (j + 1)).smooth (hcomp j) hδ hb hY hS
          (hf (j + 1)).d1 (hf (j + 1)).dr
          (fun y l hl1 hlR => hYb δ n hδ hn f hf j (by omega) y l hl1 (by omega))
          (ihj (by omega)) x).trans ?_
        exact rec_bound_step hδ hD0 N j
    refine (key j hj x).trans (rec_bound_final hδ hD0 N j ?_)
    calc (j : ℝ) * δ ≤ n * δ := by gcongr
      _ ≤ c := hn

end AnomDiss
