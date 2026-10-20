module

public import RequestProject.DampedResponse

/-!
# Lemma 2.13: existence of the controls

The block map is a composition of `4L` elementary shears `p ↦ p ± Y(p)` with `Y ∈ 𝓔` a shear
field.  Concatenating the corresponding autonomous controls `c_k(s) Y_k` on consecutive short
time intervals realizes the block map; four further controls `φ_i'(s) eᵢ` with `∫ φ_i' = 0`
(which do not change the terminal map) cancel the time moments of orders `1, …, M-1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-! ### Sequential concatenation of shear controls -/

/-- `X` is a shear field: moving along `X` does not change `X`, so that the flow of `X` is
`p ↦ p + t X(p)`. -/
def IsShearField (X : Pt 2 → Pt 2) : Prop := ∀ (t : ℝ) p, X (p + t • X p) = X p

section seq

variable (c : ℕ → ℝ → ℝ) (X : ℕ → Pt 2 → Pt 2) (α : ℕ → ℝ)

/-- The accumulated control time `∫_{α_k}^s c_k`. -/
def cumC (k : ℕ) (s : ℝ) : ℝ := ∫ r in α k..s, c k r

/-- The flow of the concatenated controls `∑_{k < K} c_k(s) X_k`. -/
def seqFlow : ℕ → ℝ → Pt 2 → Pt 2
  | 0, _, x => x
  | k + 1, s, x => seqFlow k s x + cumC c α k s • X k (seqFlow k s x)

/-- The concatenated control field. -/
def seqField (K : ℕ) (s : ℝ) (p : Pt 2) : Pt 2 := ∑ k ∈ Finset.range K, c k s • X k p

variable {c X α} {β : ℕ → ℝ}

lemma cumC_of_le (hsupp : ∀ k s, s ∉ Ioo (α k) (β k) → c k s = 0) {k : ℕ} {s : ℝ}
    (hs : s ≤ α k) : cumC c α k s = 0 := by
  unfold cumC
  rw [intervalIntegral.integral_symm, neg_eq_zero]
  refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun r hr => ?_)
  rw [uIoc_of_le hs] at hr
  exact hsupp k r fun h => by linarith [h.1, hr.2]

lemma cumC_of_ge (hsupp : ∀ k s, s ∉ Ioo (α k) (β k) → c k s = 0) (hc : ∀ k, Continuous (c k))
    {k : ℕ} {s : ℝ} (hs : β k ≤ s) :
    cumC c α k s = ∫ r in α k..β k, c k r := by
  unfold cumC
  rw [← intervalIntegral.integral_add_adjacent_intervals ((hc k).intervalIntegrable _ _)
    ((hc k).intervalIntegrable (β k) s)]
  have : ∫ r in β k..s, c k r = 0 := by
    refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hs] at hr
    exact hsupp k r fun h => by linarith [h.2, hr.1]
  rw [this, add_zero]

lemma hasDerivAt_cumC (hc : ∀ k, Continuous (c k)) (k : ℕ) (s : ℝ) :
    HasDerivAt (cumC c α k) (c k s) s :=
  intervalIntegral.integral_hasDerivAt_right ((hc k).intervalIntegrable _ _)
    ((hc k).stronglyMeasurableAtFilter _ _) (hc k).continuousAt

/-- The concatenated flow solves the flow equation of the concatenated field. -/
theorem seqFlow_hasDerivAt (hc : ∀ k, Continuous (c k))
    (hsupp : ∀ k s, s ∉ Ioo (α k) (β k) → c k s = 0)
    (hord : ∀ j k, j < k → β j ≤ α k)
    (hX : ∀ k, Differentiable ℝ (X k)) (hshear : ∀ k, IsShearField (X k)) :
    ∀ K s x, HasDerivAt (fun s => seqFlow c X α K s x) (seqField c X K s (seqFlow c X α K s x)) s := by
  intro K
  induction K with
  | zero => intro s x; simp [seqFlow, seqField, hasDerivAt_const]
  | succ K ih =>
    intro s x
    have hΦ := ih s x
    have hC := hasDerivAt_cumC (α := α) hc K s
    have hXK : HasDerivAt (fun s => X K (seqFlow c X α K s x))
        (fderiv ℝ (X K) (seqFlow c X α K s x) (seqField c X K s (seqFlow c X α K s x))) s :=
      (hX K _).hasFDerivAt.comp_hasDerivAt s hΦ
    have hD := hΦ.add (hC.smul hXK)
    simp only [seqFlow]
    refine hD.congr_deriv ?_
    rcases le_or_gt s (α K) with h | h
    · -- before the `K`-th control starts
      have h0 : cumC c α K s = 0 := cumC_of_le hsupp h
      have h1 : c K s = 0 := hsupp K s fun hm => by linarith [hm.1]
      simp [seqField, Finset.sum_range_succ, h0, h1]
    · -- after all the earlier controls have ended
      have hz : ∀ k ∈ Finset.range K, c k s = 0 := fun k hk =>
        hsupp k s fun hm => by
          have := hord k K (Finset.mem_range.1 hk); linarith [hm.2]
      have hsum : ∀ p, ∑ k ∈ Finset.range K, c k s • X k p = 0 := fun p =>
        Finset.sum_eq_zero fun k hk => by rw [hz k hk, zero_smul]
      have hF : seqField c X K s (seqFlow c X α K s x) = 0 := hsum _
      rw [hF]
      simp only [seqField, Finset.sum_range_succ, hsum, map_zero, smul_zero, zero_add]
      rw [hshear K]

/-- Before the first control, the concatenated flow is the identity. -/
lemma seqFlow_of_le (hsupp : ∀ k s, s ∉ Ioo (α k) (β k) → c k s = 0)
    (hα : ∀ k, α 0 ≤ α k) {s : ℝ} (hs : s ≤ α 0) : ∀ K x, seqFlow c X α K s x = x := by
  intro K
  induction K with
  | zero => intro x; rfl
  | succ K ih =>
    intro x
    simp only [seqFlow, ih, cumC_of_le hsupp (hs.trans (hα K)), zero_smul, add_zero]

end seq

/-! ### The elementary shears -/

/-- Coefficients of the translated, possibly rotated, horizontal shear field. -/
noncomputable def vecH (ι : Bool) (z : Pt 2) : Fin 4 → ℝ :=
  if ι then ![0, 0, -((2 * π)⁻¹ * Real.cos (2 * π * z 0)), (2 * π)⁻¹ * Real.sin (2 * π * z 0)]
  else ![(2 * π)⁻¹ * Real.cos (2 * π * z 1), -((2 * π)⁻¹ * Real.sin (2 * π * z 1)), 0, 0]

/-- Coefficients of the translated, possibly rotated, vertical shear field. -/
noncomputable def vecV (ι : Bool) (z : Pt 2) : Fin 4 → ℝ :=
  if ι then ![-((2 * π)⁻¹ * Real.cos (2 * π * z 1)), (2 * π)⁻¹ * Real.sin (2 * π * z 1), 0, 0]
  else ![0, 0, (2 * π)⁻¹ * Real.cos (2 * π * z 0), -((2 * π)⁻¹ * Real.sin (2 * π * z 0))]

lemma sin_two_pi_sub (a b : ℝ) : Real.sin (2 * π * (a - b)) =
    Real.sin (2 * π * a) * Real.cos (2 * π * b) - Real.cos (2 * π * a) * Real.sin (2 * π * b) := by
  rw [mul_sub, Real.sin_sub]

lemma eField_apply (c : Fin 4 → ℝ) (x : Pt 2) :
    eField c x = ![c 0 * Real.sin (2 * π * x 1) + c 1 * Real.cos (2 * π * x 1),
      c 2 * Real.sin (2 * π * x 0) + c 3 * Real.cos (2 * π * x 0)] := by
  funext k; fin_cases k <;> simp [eField, eBasis, Fin.sum_univ_four]

lemma step_H (ι : Bool) (z x : Pt 2) : z + conjJ ι shearH (x - z) = x + eField (vecH ι z) x := by
  rw [eField_apply]
  cases ι <;> refine vec2_ext ?_ ?_ <;>
    simp [conjJ, shearH, rotJ, rotJinv, vecH, sin_two_pi_sub] <;> ring

lemma step_Hinv (ι : Bool) (z x : Pt 2) : z + conjJ ι shearHinv (x - z) = x - eField (vecH ι z) x := by
  rw [eField_apply]
  cases ι <;> refine vec2_ext ?_ ?_ <;>
    simp [conjJ, shearHinv, rotJ, rotJinv, vecH, sin_two_pi_sub] <;> ring

lemma step_V (ι : Bool) (z x : Pt 2) : z + conjJ ι shearV (x - z) = x + eField (vecV ι z) x := by
  rw [eField_apply]
  cases ι <;> refine vec2_ext ?_ ?_ <;>
    simp [conjJ, shearV, rotJ, rotJinv, vecV, sin_two_pi_sub] <;> ring

lemma step_Vinv (ι : Bool) (z x : Pt 2) : z + conjJ ι shearVinv (x - z) = x - eField (vecV ι z) x := by
  rw [eField_apply]
  cases ι <;> refine vec2_ext ?_ ?_ <;>
    simp [conjJ, shearVinv, rotJ, rotJinv, vecV, sin_two_pi_sub] <;> ring

lemma conj_comp (ι : Bool) (z : Pt 2) (A B : Pt 2 → Pt 2) (x : Pt 2) :
    z + conjJ ι (A ∘ B) (x - z) = z + conjJ ι A ((z + conjJ ι B (x - z)) - z) := by
  cases ι <;> simp [conjJ, rotJinv_rotJ]

lemma mapG_eq_steps (ι : Bool) (z x : Pt 2) :
    mapG ι z x =
      (fun y => y - eField (vecV ι z) y) ((fun y => y - eField (vecH ι z) y)
        ((fun y => y + eField (vecV ι z) y) (x + eField (vecH ι z) x))) := by
  simp only [mapG, mapF]
  rw [conj_comp, conj_comp, conj_comp, step_H, step_V, step_Hinv, step_Vinv]

lemma isShearField_x (c : Fin 4 → ℝ) (h2 : c 2 = 0) (h3 : c 3 = 0) : IsShearField (eField c) := by
  intro t p
  have e : ∀ q : Pt 2, eField c q = ![c 0 * Real.sin (2 * π * q 1) + c 1 * Real.cos (2 * π * q 1), 0] := by
    intro q; rw [eField_apply, h2, h3]; simp
  rw [e, e]
  simp

lemma isShearField_y (c : Fin 4 → ℝ) (h0 : c 0 = 0) (h1 : c 1 = 0) : IsShearField (eField c) := by
  intro t p
  have e : ∀ q : Pt 2, eField c q = ![0, c 2 * Real.sin (2 * π * q 0) + c 3 * Real.cos (2 * π * q 0)] := by
    intro q; rw [eField_apply, h0, h1]; simp
  rw [e, e]
  simp

lemma isShearField_vecH (ι : Bool) (z : Pt 2) : IsShearField (eField (vecH ι z)) := by
  cases ι
  · exact isShearField_x _ (by simp [vecH]) (by simp [vecH])
  · exact isShearField_y _ (by simp [vecH]) (by simp [vecH])

lemma isShearField_vecV (ι : Bool) (z : Pt 2) : IsShearField (eField (vecV ι z)) := by
  cases ι
  · exact isShearField_y _ (by simp [vecV]) (by simp [vecV])
  · exact isShearField_x _ (by simp [vecV]) (by simp [vecV])

lemma isShearField_eBasis (i : Fin 4) : IsShearField (eBasis i) := by
  rw [eBasis_eq_eField]
  fin_cases i
  · exact isShearField_x _ (by simp) (by simp)
  · exact isShearField_x _ (by simp) (by simp)
  · exact isShearField_y _ (by simp) (by simp)
  · exact isShearField_y _ (by simp) (by simp)

end AnomDiss
