module

public import RequestProject.ControlsBuild

/-!
# Lemma 2.13: assembly of the controls

The shear pieces, their moment corrections and the resulting control family.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-! ### Algebraic preliminaries -/

lemma sum_range_four_mul {E : Type*} [AddCommMonoid E] (f : ℕ → E) (L : ℕ) :
    ∑ k ∈ Finset.range (4 * L), f k =
      ∑ l ∈ Finset.range L, (f (4 * l) + f (4 * l + 1) + f (4 * l + 2) + f (4 * l + 3)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show 4 * (L + 1) = 4 * L + 3 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    abel

lemma eField_add (c d : Fin 4 → ℝ) (x : Pt 2) : eField (c + d) x = eField c x + eField d x := by
  simp [eField, add_smul, Finset.sum_add_distrib]

lemma eField_smul (a : ℝ) (c : Fin 4 → ℝ) (x : Pt 2) : eField (a • c) x = a • eField c x := by
  simp [eField, Finset.smul_sum, smul_smul]

lemma eField_zero (x : Pt 2) : eField 0 x = 0 := by simp [eField]

lemma eField_sum {ι : Type*} (t : Finset ι) (c : ι → Fin 4 → ℝ) (x : Pt 2) :
    eField (∑ k ∈ t, c k) x = ∑ k ∈ t, eField (c k) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [eField_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, eField_add, ih]

lemma contDiff_eField (c : Fin 4 → ℝ) : ContDiff ℝ ∞ (eField c) := (eigenspace_properties c).1

/-! ### Coefficients of the elementary shears -/

lemma pi_inv_bound {t : ℝ} (ht : |t| ≤ 1) : |π|⁻¹ * 2⁻¹ * |t| ≤ 1 := by
  rw [abs_of_pos Real.pi_pos]
  have h1 : π⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have h2 : 0 ≤ π⁻¹ := by positivity
  calc π⁻¹ * 2⁻¹ * |t| ≤ 1 * 2⁻¹ * 1 := by gcongr
    _ ≤ 1 := by norm_num

lemma abs_vecH_le (ι : Bool) (z : Pt 2) (i : Fin 4) : |vecH ι z i| ≤ 1 := by
  cases ι <;> fin_cases i <;> simp [vecH] <;>
    first
    | simpa only [abs_of_pos Real.pi_pos] using pi_inv_bound (Real.abs_cos_le_one _)
    | simpa only [abs_of_pos Real.pi_pos] using pi_inv_bound (Real.abs_sin_le_one _)

lemma abs_vecV_le (ι : Bool) (z : Pt 2) (i : Fin 4) : |vecV ι z i| ≤ 1 := by
  cases ι <;> fin_cases i <;> simp [vecV] <;>
    first
    | simpa only [abs_of_pos Real.pi_pos] using pi_inv_bound (Real.abs_cos_le_one _)
    | simpa only [abs_of_pos Real.pi_pos] using pi_inv_bound (Real.abs_sin_le_one _)

lemma contDiff_vecH (ι : Bool) : ContDiff ℝ ∞ (vecH ι) := by
  refine contDiff_pi.2 fun i => ?_
  cases ι <;> fin_cases i <;> simp [vecH] <;> fun_prop

lemma contDiff_vecV (ι : Bool) : ContDiff ℝ ∞ (vecV ι) := by
  refine contDiff_pi.2 fun i => ?_
  cases ι <;> fin_cases i <;> simp [vecV] <;> fun_prop

variable {L : ℕ}

/-- The coefficient vector of the `k`-th elementary shear (`k = 4l + j`): horizontal for even
`j`, vertical for odd `j`, built from the `l`-th parameter. -/
def vK (w : Fin L → Bool × Pt 2) (k : ℕ) : Fin 4 → ℝ :=
  if h : k / 4 < L then
    (if k % 2 = 0 then vecH (w ⟨k / 4, h⟩).1 (w ⟨k / 4, h⟩).2
      else vecV (w ⟨k / 4, h⟩).1 (w ⟨k / 4, h⟩).2)
  else 0

/-- The sign of the `k`-th elementary shear. -/
def sgnK (k : ℕ) : ℝ := if k % 4 < 2 then 1 else -1

lemma abs_vK_le (w : Fin L → Bool × Pt 2) (k : ℕ) (i : Fin 4) : |vK w k i| ≤ 1 := by
  unfold vK
  split_ifs
  · exact abs_vecH_le _ _ _
  · exact abs_vecV_le _ _ _
  · simp

lemma norm_vK_le (w : Fin L → Bool × Pt 2) (k : ℕ) : ‖vK w k‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    rw [Real.norm_eq_abs]; exact abs_vK_le w k i

lemma abs_sgnK (k : ℕ) : |sgnK k| = 1 := by unfold sgnK; split_ifs <;> simp

lemma vK_four (w : Fin L → Bool × Pt 2) (l : ℕ) (hl : l < L) :
    vK w (4 * l) = vecH (w ⟨l, hl⟩).1 (w ⟨l, hl⟩).2 ∧
    vK w (4 * l + 1) = vecV (w ⟨l, hl⟩).1 (w ⟨l, hl⟩).2 ∧
    vK w (4 * l + 2) = vecH (w ⟨l, hl⟩).1 (w ⟨l, hl⟩).2 ∧
    vK w (4 * l + 3) = vecV (w ⟨l, hl⟩).1 (w ⟨l, hl⟩).2 := by
  have e0 : 4 * l / 4 = l := by omega
  have e1 : (4 * l + 1) / 4 = l := by omega
  have e2 : (4 * l + 2) / 4 = l := by omega
  have e3 : (4 * l + 3) / 4 = l := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold vK
  · rw [dif_pos (by omega), if_pos (by omega)]; simp only [e0]
  · rw [dif_pos (by omega), if_neg (by omega)]; simp only [e1]
  · rw [dif_pos (by omega), if_pos (by omega)]; simp only [e2]
  · rw [dif_pos (by omega), if_neg (by omega)]; simp only [e3]

lemma sgnK_four (l : ℕ) : sgnK (4 * l) = 1 ∧ sgnK (4 * l + 1) = 1 ∧ sgnK (4 * l + 2) = -1 ∧
    sgnK (4 * l + 3) = -1 := by
  unfold sgnK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [if_pos (by omega)]
  · rw [if_pos (by omega)]
  · rw [if_neg (by omega)]
  · rw [if_neg (by omega)]

/-- The four shears of a block cancel: `∑ σ_k v_k = 0`. -/
lemma sum_sgnK_vK (w : Fin L → Bool × Pt 2) :
    ∑ k ∈ Finset.range (4 * L), sgnK k • vK w k = 0 := by
  rw [sum_range_four_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  obtain ⟨h0, h1, h2, h3⟩ := vK_four w l (Finset.mem_range.1 hl)
  obtain ⟨s0, s1, s2, s3⟩ := sgnK_four l
  rw [h0, h1, h2, h3, s0, s1, s2, s3]
  simp


/-! ### The time profiles of the pieces -/

variable (L) (M : ℕ)

/-- The time scale of the shear pieces. -/
def epsC : ℝ := 1 / (64 * ((L : ℝ) + 1) * (∑ i, |corrConst M i| + 1))

lemma epsC_pos : 0 < epsC L M := by
  unfold epsC
  have : 0 ≤ ∑ i, |corrConst M i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  positivity

lemma epsC_mul_le : (4 * (L : ℝ) + 4) * epsC L M ≤ 1 / 16 := by
  unfold epsC
  have h : 0 ≤ ∑ i, |corrConst M i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma corrConst_mul_le (i : Fin 4) : |corrConst M i| * (4 * L * epsC L M) ≤ 1 / 16 := by
  unfold epsC
  have h : 0 ≤ ∑ i, |corrConst M i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hi : |corrConst M i| ≤ ∑ i, |corrConst M i| :=
    Finset.single_le_sum (f := fun i => |corrConst M i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  rw [mul_one_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  have h0 : 0 ≤ |corrConst M i| := abs_nonneg _
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith [mul_nonneg h0 hL]

/-- The center of the `k`-th shear piece. -/
def centerK (k : ℕ) : ℝ := 1 / 8 + epsC L M * (k + 1 / 2)

/-- The time profile of the `k`-th shear piece, supported in `(1/8 + ε k, 1/8 + ε (k+1))`. -/
def profK (k : ℕ) : ℝ → ℝ := bumpAt (epsC L M) (centerK L M k)

/-- The time moments of the `k`-th profile. -/
def momK (k p : ℕ) : ℝ := ∫ s, s ^ p * profK L M k s

/-- The moments to be corrected for the `k`-th piece. -/
def muK (k : ℕ) : Fin (M - 1) → ℝ := fun r => sgnK k * momK L M k (r + 1) / ((r : ℝ) + 1)

/-- The scalar profile multiplying `vᵢ eᵢ` for the `k`-th piece: the shear profile plus its
moment correction. -/
def gK (k : ℕ) (i : Fin 4) (s : ℝ) : ℝ := sgnK k * profK L M k s + corrH M i (muK L M k) s

/-- The controls: `∑_k ∑_i v_{k,i}(ω) g_{k,i}(s) eᵢ`. -/
def coefC (w : Fin L → Bool × Pt 2) (s : ℝ) : Fin 4 → ℝ :=
  ∑ k ∈ Finset.range (4 * L), ∑ i, (vK w k i * gK L M k i s) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)

lemma contDiff_profK (k : ℕ) : ContDiff ℝ ∞ (profK L M k) := contDiff_bumpAt _ _

lemma contDiff_gK (k : ℕ) (i : Fin 4) : ContDiff ℝ ∞ (gK L M k i) :=
  (contDiff_const.mul (contDiff_profK L M k)).add (contDiff_corrH M i _)

lemma profK_eq_zero (k : ℕ) {s : ℝ}
    (hs : s ∉ Ioo (1 / 8 + epsC L M * k) (1 / 8 + epsC L M * (k + 1))) : profK L M k s = 0 := by
  have hε := epsC_pos L M
  refine bumpAt_eq_zero hε fun h => hs ⟨?_, ?_⟩
  · have := h.1; unfold centerK at this; nlinarith
  · have := h.2; unfold centerK at this; nlinarith

lemma integral_profK (k : ℕ) : ∫ s, profK L M k s = 1 := integral_bumpAt (epsC_pos L M) _

lemma profK_nonneg (k : ℕ) (s : ℝ) : 0 ≤ profK L M k s := bumpAt_nonneg (epsC_pos L M) _ _

lemma centerK_add_two (k : ℕ) : centerK L M (k + 2) = centerK L M k + 2 * epsC L M := by
  unfold centerK; push_cast; ring

/-- Moments of two shear pieces two slots apart differ by `O(ε)`. -/
lemma abs_muK_add_le (k : ℕ) (hk : k + 2 < 4 * L) (r : Fin (M - 1)) :
    |muK L M k r * sgnK k + muK L M (k + 2) r * sgnK k| ≤ 2 * epsC L M := by
  have hε := epsC_pos L M
  have hb := epsC_mul_le L M
  have hk' : (k : ℝ) + 2 < 4 * L := by exact_mod_cast hk
  have hσ : sgnK (k + 2) * sgnK k = -1 := by
    unfold sgnK
    by_cases h : k % 4 < 2
    · rw [if_pos h, if_neg (by omega)]; norm_num
    · rw [if_neg h, if_pos (by omega)]; norm_num
  have hσ2 : sgnK k * sgnK k = 1 := by unfold sgnK; split_ifs <;> norm_num
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have key : muK L M k r * sgnK k + muK L M (k + 2) r * sgnK k =
      -(momK L M (k + 2) (r + 1) - momK L M k (r + 1)) / ((r : ℝ) + 1) := by
    unfold muK
    field_simp
    linear_combination (momK L M k (r + 1)) * hσ2 + (momK L M (k + 2) (r + 1)) * hσ
  rw [key, abs_div, abs_neg, abs_of_pos hr, div_le_iff₀ hr]
  have := moment_shift_le hε (centerK L M k) (2 * epsC L M) (by positivity) (r + 1)
    (by unfold centerK; nlinarith) (by unfold centerK; nlinarith)
  unfold momK profK
  rw [← centerK_add_two] at this
  push_cast at this ⊢
  linarith

/-- The total moment to be corrected in the `i`-th coordinate is `O(L ε)`. -/
lemma norm_sum_vK_muK_le (w : Fin L → Bool × Pt 2) (i : Fin 4) :
    ‖∑ k ∈ Finset.range (4 * L), vK w k i • muK L M k‖ ≤ 4 * L * epsC L M := by
  have hε := epsC_pos L M
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun r => ?_
  rw [Finset.sum_apply, sum_range_four_mul, Real.norm_eq_abs]
  calc |∑ l ∈ Finset.range L, ((vK w (4 * l) i • muK L M (4 * l)) r +
        (vK w (4 * l + 1) i • muK L M (4 * l + 1)) r + (vK w (4 * l + 2) i • muK L M (4 * l + 2)) r
        + (vK w (4 * l + 3) i • muK L M (4 * l + 3)) r)|
      ≤ ∑ l ∈ Finset.range L, 4 * epsC L M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        have hl' := Finset.mem_range.1 hl
        obtain ⟨h0, h1, h2, h3⟩ := vK_four w l hl'
        obtain ⟨s0, s1, s2, s3⟩ := sgnK_four l
        have e1 := abs_muK_add_le L M (4 * l) (by omega) r
        have e2 := abs_muK_add_le L M (4 * l + 1) (by omega) r
        rw [s0] at e1; rw [s1] at e2
        simp only [mul_one] at e1 e2
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h2, ← h0, h3, ← h1]
        have a0 := abs_vK_le w (4 * l) i
        have a1 := abs_vK_le w (4 * l + 1) i
        calc |vK w (4 * l) i * muK L M (4 * l) r + vK w (4 * l + 1) i * muK L M (4 * l + 1) r +
              vK w (4 * l) i * muK L M (4 * l + 2) r + vK w (4 * l + 1) i * muK L M (4 * l + 3) r|
            = |vK w (4 * l) i * (muK L M (4 * l) r + muK L M (4 * l + 2) r) +
                vK w (4 * l + 1) i * (muK L M (4 * l + 1) r + muK L M (4 * l + 1 + 2) r)| := by
              ring_nf
          _ ≤ |vK w (4 * l) i| * |muK L M (4 * l) r + muK L M (4 * l + 2) r| +
                |vK w (4 * l + 1) i| * |muK L M (4 * l + 1) r + muK L M (4 * l + 1 + 2) r| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ 1 * (2 * epsC L M) + 1 * (2 * epsC L M) := by gcongr
          _ = 4 * epsC L M := by ring
    _ = 4 * L * epsC L M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring


/-! ### Support, moments, smoothness and mixed bounds -/

lemma profK_eq_zero_of (k : ℕ) (hk : k < 4 * L) {s : ℝ} (hs : s ∉ Ioo (1 / 8 : ℝ) (1 / 4)) :
    profK L M k s = 0 := by
  refine profK_eq_zero L M k fun h => hs ⟨?_, ?_⟩
  · have hε := epsC_pos L M
    have : (0 : ℝ) ≤ epsC L M * k := by positivity
    linarith [h.1]
  · have hb := epsC_mul_le L M
    have hε := epsC_pos L M
    have hk' : (k : ℝ) + 1 ≤ 4 * L := by exact_mod_cast hk
    nlinarith [h.2]

lemma winA_ge (i : Fin 4) : 1 / 2 ≤ winA i := by
  unfold winA; have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _; linarith

lemma winA_le (i : Fin 4) : winA i + 1 / 10 ≤ 9 / 10 := by
  unfold winA
  have : ((i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  linarith

lemma corrH_eq_zero_of (i : Fin 4) (m : Fin (M - 1) → ℝ) {s : ℝ}
    (hs : s ∉ Ioo (1 / 2 : ℝ) (9 / 10)) : corrH M i m s = 0 :=
  corrH_eq_zero M i m fun h => hs ⟨by linarith [h.1, winA_ge i], by linarith [h.2, winA_le i]⟩

lemma gK_eq_zero (k : ℕ) (hk : k < 4 * L) (i : Fin 4) {s : ℝ} (hs : s ∉ Ioo (1 / 8 : ℝ) (9 / 10)) :
    gK L M k i s = 0 := by
  unfold gK
  rw [profK_eq_zero_of L M k hk fun h => hs ⟨h.1, by linarith [h.2]⟩,
    corrH_eq_zero_of M i _ fun h => hs ⟨by linarith [h.1], h.2⟩]
  simp

lemma coefC_eq_zero (w : Fin L → Bool × Pt 2) {s : ℝ} (hs : s ∉ Ioo (1 / 8 : ℝ) (9 / 10)) :
    coefC L M w s = 0 := by
  unfold coefC
  refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun i _ => ?_
  rw [gK_eq_zero L M k (Finset.mem_range.1 hk) i hs]; simp

lemma integral_pow_gK (k : ℕ) (i : Fin 4) (r : ℕ) (hr : r < M) :
    ∫ s, s ^ r * gK L M k i s = if r = 0 then sgnK k else 0 := by
  have hε := epsC_pos L M
  unfold gK
  simp_rw [mul_add]
  rw [integral_add (by simpa [profK, mul_left_comm] using
      (integrable_bumpAt_mul hε (centerK L M k) (F := fun s => s ^ r)
        (by fun_prop)).const_mul (sgnK k))
    (integrable_corrH_mul M i _ (by fun_prop))]
  have h1 : ∫ s, s ^ r * (sgnK k * profK L M k s) = sgnK k * momK L M k r := by
    unfold momK; rw [← integral_const_mul]; congr 1; funext s; ring
  rw [h1]
  rcases r with _ | r
  · simp only [pow_zero, one_mul, if_true]
    rw [integral_corrH]
    unfold momK; simp only [pow_zero, one_mul]; rw [integral_profK]; ring
  · rw [moment_corrH M i _ r hr, if_neg (Nat.succ_ne_zero r)]
    unfold muK
    have : ((r : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma integrable_pow_smul_gK (w : Fin L → Bool × Pt 2) (k : ℕ) (i : Fin 4) (r : ℕ) :
    Integrable fun s => (s ^ r * (vK w k i * gK L M k i s)) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
  have hε := epsC_pos L M
  refine Integrable.smul_const ?_ _
  have : (fun s => s ^ r * (vK w k i * gK L M k i s)) = fun s =>
      (vK w k i * sgnK k) * (s ^ r * profK L M k s) + vK w k i * (s ^ r * corrH M i (muK L M k) s) := by
    funext s; unfold gK; ring
  rw [this]
  exact (((integrable_bumpAt_mul hε _ (by fun_prop)).const_mul _)).add
    ((integrable_corrH_mul M i _ (by fun_prop)).const_mul _)

/-- The controls have vanishing time moments of orders `0, …, M-1`. -/
theorem coefC_moments (w : Fin L → Bool × Pt 2) (r : ℕ) (hr : r < M) :
    ∫ s in (0 : ℝ)..1, s ^ r • coefC L M w s = 0 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  swap
  · intro s hs
    by_contra h
    refine hs ?_
    simp only
    rw [coefC_eq_zero L M w fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩, smul_zero]
  have hfun : (fun s => s ^ r • coefC L M w s) = fun s => ∑ k ∈ Finset.range (4 * L), ∑ i,
      (s ^ r * (vK w k i * gK L M k i s)) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    funext s; unfold coefC; simp only [Finset.smul_sum, smul_smul]
  rw [hfun, integral_finset_sum _ fun k _ =>
    integrable_finset_sum _ fun i _ => integrable_pow_smul_gK L M w k i r]
  simp_rw [integral_finset_sum _ fun i _ => integrable_pow_smul_gK L M w _ i r]
  simp_rw [integral_smul_const]
  have hint : ∀ k i, ∫ s, s ^ r * (vK w k i * gK L M k i s) =
      vK w k i * (if r = 0 then sgnK k else 0) := fun k i => by
    rw [← integral_pow_gK L M k i r hr, ← integral_const_mul]; congr 1; funext s; ring
  simp_rw [hint]
  split_ifs with h0
  · have := sum_sgnK_vK w
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [← Finset.univ_sum_single (vK w k)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> ring
  · simp

lemma contDiff_vK_param (ιs : Fin L → Bool) (k : ℕ) (i : Fin 4) :
    ContDiff ℝ ∞ fun z : Fin L → Pt 2 => vK (fun j => (ιs j, z j)) k i := by
  unfold vK
  split_ifs with h h2
  · exact (contDiff_apply ℝ ℝ i).comp ((contDiff_vecH _).comp (contDiff_apply ℝ (Pt 2) _))
  · exact (contDiff_apply ℝ ℝ i).comp ((contDiff_vecV _).comp (contDiff_apply ℝ (Pt 2) _))
  · exact contDiff_const

theorem coefC_smooth (ιs : Fin L → Bool) :
    ContDiff ℝ ∞ (fun p : (Fin L → Pt 2) × ℝ => coefC L M (fun i => (ιs i, p.1 i)) p.2) := by
  unfold coefC
  refine ContDiff.sum fun k _ => ContDiff.sum fun i _ => ?_
  exact (((contDiff_vK_param L ιs k i).comp contDiff_fst).mul
    ((contDiff_gK L M k i).comp contDiff_snd)).smul contDiff_const

lemma hasCompactSupport_gK (k : ℕ) (hk : k < 4 * L) (i : Fin 4) : HasCompactSupport (gK L M k i) :=
  HasCompactSupport.intro (isCompact_Icc (a := (1 / 8 : ℝ)) (b := 9 / 10)) fun _ hs =>
    gK_eq_zero L M k hk i fun h => hs (Ioo_subset_Icc_self h)

lemma exists_bound_iteratedDeriv_gK (k : ℕ) (hk : k < 4 * L) (i : Fin 4) (r : ℕ) :
    ∃ C, ∀ s, ‖iteratedDeriv r (gK L M k i) s‖ ≤ C := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    ((contDiff_gK L M k i).continuous_iteratedFDeriv (m := r) (by exact_mod_cast le_top))
    ((hasCompactSupport_gK L M k hk i).iteratedFDeriv r)
  exact ⟨C, fun s => by rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC s⟩

theorem coefC_mixed (r : ℕ) : ∃ C, ∀ w s, ‖iteratedDeriv r (coefC L M w) s‖ ≤ C := by
  choose B hB using fun (k : Fin (4 * L)) (i : Fin 4) =>
    exists_bound_iteratedDeriv_gK L M k k.2 i r
  refine ⟨∑ k : Fin (4 * L), ∑ i, |B k i|, fun w s => ?_⟩
  have hcd : ∀ k i, ContDiff ℝ ∞ fun s => (vK w k i * gK L M k i s) •
      (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := fun k i =>
    (contDiff_const.mul (contDiff_gK L M k i)).smul contDiff_const
  have heq : iteratedDeriv r (coefC L M w) s = ∑ k ∈ Finset.range (4 * L), ∑ i,
      (vK w k i * iteratedDeriv r (gK L M k i) s) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    have : coefC L M w = fun s => ∑ k ∈ Finset.range (4 * L), ∑ i,
        (vK w k i * gK L M k i s) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
      rfl
    rw [this, iteratedDeriv_fun_sum fun k _ => (ContDiff.sum fun i _ => hcd k i).contDiffAt.of_le
      (by exact_mod_cast le_top)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDeriv_fun_sum fun i _ => (hcd k i).contDiffAt.of_le (by exact_mod_cast le_top)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedDeriv_smul_const ((contDiff_const.mul (contDiff_gK L M k i)).contDiffAt.of_le
      (by exact_mod_cast le_top)), iteratedDeriv_const_mul _ ((contDiff_gK L M k i).contDiffAt.of_le
      (by exact_mod_cast le_top))]
  rw [heq, Finset.sum_range (fun k => ∑ i, (vK w k i * iteratedDeriv r (gK L M k i) s) •
    (Pi.single i (1 : ℝ) : Fin 4 → ℝ))]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => ?_))
  rw [norm_smul, norm_mul]
  have h1 : ‖(Pi.single i (1 : ℝ) : Fin 4 → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  have h2 : ‖vK w k i‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact abs_vK_le w k i
  calc ‖vK w k i‖ * ‖iteratedDeriv r (gK L M k i) s‖ * ‖(Pi.single i (1 : ℝ) : Fin 4 → ℝ)‖
      ≤ 1 * |B k i| * 1 := by
        gcongr
        exact (hB k i s).trans (le_abs_self _)
    _ = |B k i| := by ring


/-! ### Spatial bounds -/

/-- The total correction in the `i`-th coordinate. -/
def corrTot (w : Fin L → Bool × Pt 2) (i : Fin 4) : Fin (M - 1) → ℝ :=
  ∑ k ∈ Finset.range (4 * L), vK w k i • muK L M k

lemma coefC_eq_split (w : Fin L → Bool × Pt 2) (s : ℝ) :
    coefC L M w s = ∑ k ∈ Finset.range (4 * L), (sgnK k * profK L M k s) • vK w k +
      ∑ i, corrH M i (corrTot L M w i) s • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
  funext j
  simp only [coefC, corrTot, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [corrH_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold gK; ring

lemma integral_abs_corrTot_le (w : Fin L → Bool × Pt 2) (i : Fin 4) :
    ∫ s, |corrH M i (corrTot L M w i) s| ≤ 1 / 16 := by
  refine (integral_abs_corrH_le M i _).trans ?_
  calc corrConst M i * ‖corrTot L M w i‖ ≤ |corrConst M i| * (4 * L * epsC L M) :=
        mul_le_mul (le_abs_self _) (norm_sum_vK_muK_le L M w i) (norm_nonneg _) (abs_nonneg _)
    _ ≤ 1 / 16 := corrConst_mul_le L M i

/-- The pointwise size of the controls. -/
def sizeC (w : Fin L → Bool × Pt 2) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (4 * L), profK L M k s + ∑ i, |corrH M i (corrTot L M w i) s|

lemma norm_coefC_le (w : Fin L → Bool × Pt 2) (s : ℝ) : ‖coefC L M w s‖ ≤ sizeC L M w s := by
  rw [coefC_eq_split]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_sgnK, one_mul,
      abs_of_nonneg (profK_nonneg L M k s)]
    exact mul_le_of_le_one_right (profK_nonneg L M k s) (norm_vK_le w k)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [h]

lemma integrable_sizeC (w : Fin L → Bool × Pt 2) : Integrable (sizeC L M w) := by
  have hε := epsC_pos L M
  refine (integrable_finset_sum _ fun k _ => ?_).add (integrable_finset_sum _ fun i _ => ?_)
  · simpa [profK] using integrable_bumpAt_mul hε (centerK L M k) (F := fun _ => 1) continuous_const
  · simpa using (integrable_corrH_mul M i (corrTot L M w i) (F := fun _ => 1) continuous_const).abs

lemma integral_sizeC_le (w : Fin L → Bool × Pt 2) : ∫ s, sizeC L M w s ≤ 4 * L + 4 := by
  have hε := epsC_pos L M
  unfold sizeC
  rw [integral_add (integrable_finset_sum _ fun k _ => by
      simpa [profK] using integrable_bumpAt_mul hε (centerK L M k) (F := fun _ => 1)
        continuous_const)
    (integrable_finset_sum _ fun i _ => by
      simpa using (integrable_corrH_mul M i (corrTot L M w i) (F := fun _ => 1)
        continuous_const).abs),
    integral_finset_sum _ fun k _ => by
      simpa [profK] using integrable_bumpAt_mul hε (centerK L M k) (F := fun _ => 1)
        continuous_const,
    integral_finset_sum _ fun i _ => by
      simpa using (integrable_corrH_mul M i (corrTot L M w i) (F := fun _ => 1)
        continuous_const).abs]
  simp_rw [integral_profK]
  have h2 : ∑ i : Fin 4, ∫ s, |corrH M i (corrTot L M w i) s| ≤ ∑ _i : Fin 4, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ => (integral_abs_corrTot_le L M w i).trans (by norm_num)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_fin] at h2 ⊢
  push_cast at h2 ⊢
  linarith

/-- A spatial norm controlled linearly by the coefficients integrates to `O(L)`. -/
lemma lintegral_coefC_le (w : Fin L → Bool × Pt 2) (F : (Fin 4 → ℝ) → ℝ≥0∞) {A : ℝ}
    (hA : 0 ≤ A) (hF : ∀ v, F v ≤ ENNReal.ofReal (A * ‖v‖)) :
    ∫⁻ s in Icc 0 1, F (coefC L M w s) ≤ ENNReal.ofReal (A * (4 * L + 4)) := by
  have hnn : ∀ s, 0 ≤ sizeC L M w s := fun s => (norm_nonneg _).trans (norm_coefC_le L M w s)
  calc ∫⁻ s in Icc 0 1, F (coefC L M w s)
      ≤ ∫⁻ s in Icc 0 1, ENNReal.ofReal (A * sizeC L M w s) := by
        refine lintegral_mono fun s => (hF _).trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_left (norm_coefC_le L M w s) hA
    _ ≤ ∫⁻ s, ENNReal.ofReal (A * sizeC L M w s) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ s, A * sizeC L M w s) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrable_sizeC L M w).const_mul A)
          (Eventually.of_forall fun s => mul_nonneg hA (hnn s))).symm
    _ ≤ ENNReal.ofReal (A * (4 * L + 4)) := by
        rw [integral_const_mul]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (integral_sizeC_le L M w) hA)

/-- The spatial bounds `S a`, independent of the number of vanishing moments. -/
def boundS (L : ℕ) (a : ℕ) : ℝ := (4 * L + 4) * (aConst a + 2 * aConst 1)

lemma boundS_nonneg (a : ℕ) : 0 ≤ boundS L a := by
  unfold boundS
  have := aConst_nonneg a; have := aConst_nonneg 1
  positivity

theorem coefC_bound (a : ℕ) (w : Fin L → Bool × Pt 2) :
    ∫⁻ s in Icc 0 1, cNormE a (eField (coefC L M w s)) ≤ ENNReal.ofReal (boundS L a) := by
  refine (lintegral_coefC_le L M w (fun v => cNormE a (eField v)) (aConst_nonneg a)
    fun v => ?_).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · show cNormE a (eField v) ≤ _
    rw [cNormE_eField]; exact iSup_le fun x => cSum_le a v x
  · unfold boundS
    have := aConst_nonneg 1
    have hL : (0 : ℝ) ≤ 4 * L + 4 := by positivity
    nlinarith

theorem coefC_bound_grad (w : Fin L → Bool × Pt 2) :
    ∫⁻ s in Icc 0 1, ⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (eField (coefC L M w s)) x))
      ≤ ENNReal.ofReal (boundS L 1) := by
  refine (lintegral_coefC_le L M w
    (fun v => ⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (eField v) x))) (A := 2 * aConst 1)
    (by have := aConst_nonneg 1; positivity) fun v => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · refine iSup_le fun x => ?_
    rw [fderiv_eField]
    exact gSum_le v x
  · unfold boundS
    have := aConst_nonneg 1
    have hL : (0 : ℝ) ≤ 4 * L + 4 := by positivity
    nlinarith

end AnomDiss
