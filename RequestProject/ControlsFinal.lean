module

public import RequestProject.ControlsAssembly

/-!
# Lemma 2.13: the terminal map and the control family

The controls of `ControlsAssembly` are the concatenation of `4L` shear pieces followed by four
zero-integral corrections; their flow is computed piece by piece.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable (L M : ℕ)

/-- The coordinate corrected by the `k`-th piece (for `4L ≤ k < 4L + 4`). -/
def idxP (k : ℕ) : Fin 4 := ⟨(k - 4 * L) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The scalar control of the `k`-th piece. -/
def cP (w : Fin L → Bool × Pt 2) (k : ℕ) (s : ℝ) : ℝ :=
  if k < 4 * L then sgnK k * profK L M k s
  else if k < 4 * L + 4 then corrH M (idxP L k) (corrTot L M w (idxP L k)) s else 0

/-- The vector field of the `k`-th piece. -/
def XP (w : Fin L → Bool × Pt 2) (k : ℕ) : Pt 2 → Pt 2 :=
  if k < 4 * L then eField (vK w k) else eBasis (idxP L k)

/-- Start of the time window of the `k`-th piece. -/
def αP (k : ℕ) : ℝ :=
  if k < 4 * L then 1 / 8 + epsC L M * k else if k < 4 * L + 4 then winA (idxP L k) else 1

/-- End of the time window of the `k`-th piece. -/
def βP (k : ℕ) : ℝ :=
  if k < 4 * L then 1 / 8 + epsC L M * (k + 1)
  else if k < 4 * L + 4 then winA (idxP L k) + 1 / 10 else 1

lemma continuous_cP (w : Fin L → Bool × Pt 2) (k : ℕ) : Continuous (cP L M w k) := by
  unfold cP
  split_ifs
  · exact continuous_const.mul (contDiff_profK L M k).continuous
  · exact continuous_corrH M _ _
  · exact continuous_const

lemma cP_supp (w : Fin L → Bool × Pt 2) (k : ℕ) (s : ℝ) (hs : s ∉ Ioo (αP L M k) (βP L M k)) :
    cP L M w k s = 0 := by
  unfold cP
  unfold αP βP at hs
  split_ifs at hs ⊢ with h1 h2
  · rw [profK_eq_zero L M k hs, mul_zero]
  · exact corrH_eq_zero M _ _ hs
  · rfl

lemma idxP_val (k : ℕ) (h1 : 4 * L ≤ k) (h2 : k < 4 * L + 4) : ((idxP L k : ℕ) : ℝ) = k - 4 * L := by
  simp only [idxP]
  rw [Nat.mod_eq_of_lt (by omega)]
  push_cast [Nat.cast_sub h1]
  ring

lemma βP_le_one (k : ℕ) : βP L M k ≤ 1 := by
  unfold βP
  have hb := epsC_mul_le L M
  have hε := epsC_pos L M
  split_ifs with h1 h2
  · have : (k : ℝ) + 1 ≤ 4 * L := by exact_mod_cast h1
    nlinarith
  · linarith [winA_le (idxP L k)]
  · rfl

lemma αP_pos (k : ℕ) : 0 < αP L M k := by
  unfold αP
  have hε := epsC_pos L M
  split_ifs
  · positivity
  · linarith [winA_ge (idxP L k)]
  · norm_num

lemma ord_P (j k : ℕ) (hjk : j < k) : βP L M j ≤ αP L M k := by
  have hb := epsC_mul_le L M
  have hε := epsC_pos L M
  unfold αP βP
  by_cases hk1 : k < 4 * L
  · rw [if_pos (by omega), if_pos hk1]
    have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    nlinarith
  rw [if_neg hk1]
  by_cases hk2 : k < 4 * L + 4
  · rw [if_pos hk2]
    by_cases hj1 : j < 4 * L
    · rw [if_pos hj1]
      have : (j : ℝ) + 1 ≤ 4 * L := by exact_mod_cast hj1
      have := winA_ge (idxP L k)
      nlinarith
    · rw [if_neg hj1, if_pos (by omega)]
      unfold winA
      rw [idxP_val L j (by omega) (by omega), idxP_val L k (by omega) hk2]
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
      linarith
  · rw [if_neg hk2]
    have := βP_le_one L M j
    unfold βP at this
    exact this

lemma XP_differentiable (w : Fin L → Bool × Pt 2) (k : ℕ) : Differentiable ℝ (XP L w k) := by
  unfold XP
  split_ifs
  · exact (contDiff_eField _).differentiable (by simp)
  · exact (contDiff_eBasis _).differentiable (by simp)

lemma XP_shear (w : Fin L → Bool × Pt 2) (k : ℕ) : IsShearField (XP L w k) := by
  unfold XP
  split_ifs with h
  · unfold vK
    split_ifs
    · exact isShearField_vecH _ _
    · exact isShearField_vecV _ _
    · exact isShearField_x 0 rfl rfl
  · exact isShearField_eBasis _


lemma idxP_add (j : ℕ) (hj : j < 4) : idxP L (4 * L + j) = ⟨j, hj⟩ := by
  ext; simp only [idxP]; rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hj]

lemma seqField_eq (w : Fin L → Bool × Pt 2) (s : ℝ) (p : Pt 2) :
    seqField (cP L M w) (XP L w) (4 * L + 4) s p = eField (coefC L M w s) p := by
  rw [coefC_eq_split, eField_add, eField_sum, eField_sum]
  unfold seqField
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    simp only [cP, XP, if_pos hk', eField_smul]
  · rw [Finset.sum_range (fun j => cP L M w (4 * L + j) s • XP L w (4 * L + j) p)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.2
    simp only [cP, XP, if_neg (show ¬ (4 * L + (j : ℕ) < 4 * L) by omega),
      if_pos (show 4 * L + (j : ℕ) < 4 * L + 4 by omega), idxP_add L j hj, eField_smul,
      ← eBasis_eq_eField]


/-- The flow of the controls: the concatenated shear flow. -/
def flowC (w : Fin L → Bool × Pt 2) (s : ℝ) (x : Pt 2) : Pt 2 :=
  seqFlow (cP L M w) (XP L w) (αP L M) (4 * L + 4) s x

lemma seqFlow_zero_time (w : Fin L → Bool × Pt 2) :
    ∀ K x, seqFlow (cP L M w) (XP L w) (αP L M) K 0 x = x := by
  intro K
  induction K with
  | zero => intro x; rfl
  | succ K ih =>
    intro x
    simp only [seqFlow, ih, cumC_of_le (β := βP L M) (cP_supp L M w) (αP_pos L M K).le,
      zero_smul, add_zero]

theorem flowC_isFlow (w : Fin L → Bool × Pt 2) :
    IsFlowOf (fun s => eField (coefC L M w s)) (flowC L M w) := by
  refine ⟨fun x => seqFlow_zero_time L M w _ x, fun s x => ?_⟩
  have := seqFlow_hasDerivAt (β := βP L M) (continuous_cP L M w) (cP_supp L M w) (ord_P L M)
    (XP_differentiable L w) (XP_shear L w) (4 * L + 4) s x
  rw [seqField_eq] at this
  exact this

lemma cumC_corr (w : Fin L → Bool × Pt 2) (k : ℕ) (hk : 4 * L ≤ k) :
    cumC (cP L M w) (αP L M) k 1 = 0 := by
  rw [cumC_of_ge (cP_supp L M w) (continuous_cP L M w) (βP_le_one L M k)]
  by_cases hk2 : k < 4 * L + 4
  · simp only [αP, βP, cP, if_neg (show ¬ k < 4 * L by omega), if_pos hk2]
    rw [← integral_eq_window _ fun s hs => corrH_eq_zero M _ _ hs, integral_corrH]
  · simp [cP, if_neg (show ¬ k < 4 * L by omega), if_neg hk2]

lemma cumC_shear (w : Fin L → Bool × Pt 2) (k : ℕ) (hk : k < 4 * L) :
    cumC (cP L M w) (αP L M) k 1 = sgnK k := by
  rw [cumC_of_ge (cP_supp L M w) (continuous_cP L M w) (βP_le_one L M k)]
  have hε := epsC_pos L M
  have hab : αP L M k ≤ βP L M k := by
    simp only [αP, βP, if_pos hk]; nlinarith
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · simp only [cP, if_pos hk]
    rw [integral_const_mul, integral_profK, mul_one]
  · intro s hs
    by_contra h
    exact hs (cP_supp L M w k s fun h' => h (Ioo_subset_Ioc_self h'))

lemma seqFlow_after (w : Fin L → Bool × Pt 2) (x : Pt 2) :
    ∀ j, seqFlow (cP L M w) (XP L w) (αP L M) (4 * L + j) 1 x =
      seqFlow (cP L M w) (XP L w) (αP L M) (4 * L) 1 x := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc]
    simp only [seqFlow, ih, cumC_corr L M w (4 * L + j) (by omega), zero_smul, add_zero]

lemma seqFlow_step (w : Fin L → Bool × Pt 2) (x : Pt 2) (k : ℕ) (hk : k < 4 * L) :
    seqFlow (cP L M w) (XP L w) (αP L M) (k + 1) 1 x =
      seqFlow (cP L M w) (XP L w) (αP L M) k 1 x +
        sgnK k • eField (vK w k) (seqFlow (cP L M w) (XP L w) (αP L M) k 1 x) := by
  simp only [seqFlow, cumC_shear L M w k hk, XP, if_pos hk]

lemma seqFlow_block (w : Fin L → Bool × Pt 2) (x : Pt 2) (l : ℕ) (hl : l < L) :
    seqFlow (cP L M w) (XP L w) (αP L M) (4 * l + 4) 1 x =
      mapG (w ⟨l, hl⟩).1 (w ⟨l, hl⟩).2 (seqFlow (cP L M w) (XP L w) (αP L M) (4 * l) 1 x) := by
  obtain ⟨h0, h1, h2, h3⟩ := vK_four w l hl
  obtain ⟨s0, s1, s2, s3⟩ := sgnK_four l
  rw [show 4 * l + 4 = 4 * l + 3 + 1 by ring, seqFlow_step L M w x _ (by omega),
    show 4 * l + 3 = 4 * l + 2 + 1 by ring, seqFlow_step L M w x _ (by omega),
    show 4 * l + 2 = 4 * l + 1 + 1 by ring, seqFlow_step L M w x _ (by omega),
    seqFlow_step L M w x _ (by omega)]
  rw [show 4 * l + 1 + 1 = 4 * l + 2 by ring, show 4 * l + 2 + 1 = 4 * l + 3 by ring,
    h0, h1, h2, h3, s0, s1, s2, s3, mapG_eq_steps]
  simp only [one_smul, neg_one_smul, ← sub_eq_add_neg]

lemma seqFlow_prefix (w : Fin L → Bool × Pt 2) (x : Pt 2) :
    ∀ l, l ≤ L → seqFlow (cP L M w) (XP L w) (αP L M) (4 * l) 1 x =
      ((List.ofFn w).take l).foldl (fun y p => mapG p.1 p.2 y) x := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l ih =>
    intro hl
    rw [show 4 * (l + 1) = 4 * l + 4 by ring, seqFlow_block L M w x l (by omega), ih (by omega),
      List.take_add_one, List.getElem?_ofFn, dif_pos (by omega)]
    simp

theorem flowC_one (w : Fin L → Bool × Pt 2) (x : Pt 2) : flowC L M w 1 x = blockMap w x := by
  unfold flowC blockMap
  rw [seqFlow_after L M w x 4, seqFlow_prefix L M w x L le_rfl,
    List.take_of_length_le (by simp)]


/-- The control family for `M` vanishing moments. -/
def controlFamily : ControlFamily L M (boundS L) where
  coef := coefC L M
  a₀ := 1 / 8
  b₀ := 9 / 10
  ha₀ := by norm_num
  hab₀ := by norm_num
  hb₀ := by norm_num
  support w s hs := coefC_eq_zero L M w fun h => hs (Ioo_subset_Icc_self h)
  smooth := coefC_smooth L M
  terminal w := ⟨flowC L M w, flowC_isFlow L M w, funext (flowC_one L M w)⟩
  moments w r hr := coefC_moments L M w r hr
  bound a w := coefC_bound L M a w
  bound_grad w := coefC_bound_grad L M w
  mixed r := coefC_mixed L M r

/-- **Lemma 2.13** (controls).  The spatial bounds `S a` can be fixed before the number `M` of
vanishing moments is chosen; for every `M ≥ 1` there is a family of controls as above.
(The construction works for every `M`; the hypothesis `1 ≤ M` of the paper is not needed.) -/
theorem controls_exist (L : ℕ) : ∃ S : ℕ → ℝ, (∀ a, 0 ≤ S a) ∧
    ∀ M : ℕ, 1 ≤ M → Nonempty (ControlFamily L M S) :=
  ⟨boundS L, boundS_nonneg L, fun M _ => ⟨controlFamily L M⟩⟩

end AnomDiss
