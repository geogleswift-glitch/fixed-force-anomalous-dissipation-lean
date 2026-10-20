module

public import RequestProject.FlowC2

/-!
# `C¹` stability of flows under perturbation of the field

If two fields `V`, `W` satisfy the standing hypotheses and are uniformly `δ₀`-close with
derivatives `δ₁`-close, then their flow maps over a time `T` are `C¹`-close, with an error
`O(δ₀ + δ₁)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {V W : ℝ → E → E} {M K : ℝ≥0} {K2 K3 : ℝ} {t₀ t₁ : ℝ}

/-- `C⁰` stability of flows. -/
theorem norm_gflow_sub_gflow_le (hV : GoodField V M K) (hW : GoodField W M K) {δ₀ : ℝ}
    (hδ : ∀ s y, ‖V s y - W s y‖ ≤ δ₀) (h01 : t₀ ≤ t₁) (x : E) :
    ‖gflow V t₀ t₁ x - gflow W t₀ t₁ x‖ ≤ δ₀ * (t₁ - t₀) * Real.exp (K * (t₁ - t₀)) := by
  have hδ0 : 0 ≤ δ₀ := (norm_nonneg _).trans (hδ 0 x)
  have key := norm_le_of_hasDerivAt_le (f := fun s => gflow V t₀ s x - gflow W t₀ s x)
    (f' := fun s => V s (gflow V t₀ s x) - W s (gflow W t₀ s x)) (a := t₀) (b := t₁) (K := K)
    (ε := δ₀) (δ := 0) h01 K.2 hδ0
    (fun s _ => (hV.hasDerivAt_gflow t₀ s x).sub (hW.hasDerivAt_gflow t₀ s x))
    (fun s _ => by
      have e : V s (gflow V t₀ s x) - W s (gflow W t₀ s x) =
          (V s (gflow V t₀ s x) - V s (gflow W t₀ s x)) +
            (V s (gflow W t₀ s x) - W s (gflow W t₀ s x)) := by abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hδ _ _))
      have := (hV.lip s).dist_le_mul (gflow V t₀ s x) (gflow W t₀ s x)
      rwa [dist_eq_norm, dist_eq_norm] at this)
    (by simp [hV.gflow_self, hW.gflow_self])
  simpa [mul_comm, mul_assoc, mul_left_comm] using key

/-- `C¹` stability of flows (forward times). -/
theorem norm_fderiv_gflow_sub_le_fwd (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hW : GoodField W M K) (hW2 : C2Field W K2 K3) {δ₀ δ₁ : ℝ}
    (hδ0 : ∀ s y, ‖V s y - W s y‖ ≤ δ₀)
    (hδ1 : ∀ s y, ‖fderiv ℝ (V s) y - fderiv ℝ (W s) y‖ ≤ δ₁) (h01 : t₀ ≤ t₁) (x : E) :
    ‖fderiv ℝ (gflow V t₀ t₁) x - fderiv ℝ (gflow W t₀ t₁) x‖ ≤
      ((K2 * (δ₀ * (t₁ - t₀) * Real.exp (K * (t₁ - t₀))) + δ₁) * Real.exp (K * (t₁ - t₀))) *
        (t₁ - t₀) * Real.exp (K * (t₁ - t₀)) := by
  have hδ0' : 0 ≤ δ₀ := (norm_nonneg _).trans (hδ0 0 x)
  have hδ1' : 0 ≤ δ₁ := (norm_nonneg _).trans (hδ1 0 x)
  have hK2 := hV2.K2_nonneg
  have hK := NNReal.coe_nonneg K
  obtain ⟨JV, hJV⟩ := exists_varSol hV hV2 h01 x
  obtain ⟨JW, hJW⟩ := exists_varSol hW hW2 h01 x
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  rw [(hJV.hasFDerivAt hV hV2 ht₁).fderiv, (hJW.hasFDerivAt hW hW2 ht₁).fderiv]
  set T := t₁ - t₀ with hT
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  set ε : ℝ := (K2 * (δ₀ * T * Real.exp (K * T)) + δ₁) * Real.exp (K * T) with hε
  have hε0 : 0 ≤ ε := by positivity
  have key := norm_le_of_hasDerivAt_le (f := fun s => JV s - JW s)
    (f' := fun s => (fderiv ℝ (V s) (gflow V t₀ s x)).comp (JV s) -
      (fderiv ℝ (W s) (gflow W t₀ s x)).comp (JW s)) (a := t₀) (b := t₁) (K := K)
    (ε := ε) (δ := 0) h01 hK hε0 (fun s hs => (hJV.2 s hs).sub (hJW.2 s hs)) (fun s hs => by
      set AV := fderiv ℝ (V s) (gflow V t₀ s x)
      set AV' := fderiv ℝ (V s) (gflow W t₀ s x)
      set AW := fderiv ℝ (W s) (gflow W t₀ s x)
      have e : AV.comp (JV s) - AW.comp (JW s) =
          AV.comp (JV s - JW s) + ((AV - AV').comp (JW s) + (AV' - AW).comp (JW s)) := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
          ContinuousLinearMap.sub_comp]; abel
      rw [e]
      have hAV : ‖AV‖ ≤ K := hV.norm_fderiv_le s _
      have hJWb : ‖JW s‖ ≤ Real.exp (K * T) :=
        (hJW.norm_le hW hs).trans (Real.exp_le_exp.2 (by nlinarith [hs.2]))
      have hX : ‖gflow V t₀ s x - gflow W t₀ s x‖ ≤ δ₀ * T * Real.exp (K * T) := by
        refine (norm_gflow_sub_gflow_le hV hW hδ0 hs.1 x).trans ?_
        have h1 : s - t₀ ≤ T := by rw [hT]; linarith [hs.2]
        have h2 : 0 ≤ s - t₀ := by linarith [hs.1]
        gcongr
      have h1 : ‖AV - AV'‖ ≤ K2 * (δ₀ * T * Real.exp (K * T)) := by
        refine (norm_sub_rev AV AV').le.trans ?_
        refine (hV2.lip1 s _ _).trans ?_
        rw [norm_sub_rev]; gcongr
      have h2 : ‖AV' - AW‖ ≤ δ₁ := hδ1 _ _
      have n1 := ContinuousLinearMap.opNorm_comp_le AV (JV s - JW s)
      have n2 := ContinuousLinearMap.opNorm_comp_le (AV - AV') (JW s)
      have n3 := ContinuousLinearMap.opNorm_comp_le (AV' - AW) (JW s)
      have p1 := norm_nonneg (JV s - JW s)
      have p2 := norm_nonneg (JW s)
      have p3 := norm_nonneg (AV - AV')
      have p4 := norm_nonneg (AV' - AW)
      calc _ ≤ ‖AV.comp (JV s - JW s)‖ + (‖(AV - AV').comp (JW s)‖ + ‖(AV' - AW).comp (JW s)‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ K * ‖JV s - JW s‖ + (K2 * (δ₀ * T * Real.exp (K * T)) * Real.exp (K * T) +
              δ₁ * Real.exp (K * T)) := by
            gcongr
            · exact n1.trans (mul_le_mul_of_nonneg_right hAV p1)
            · exact n2.trans (mul_le_mul h1 hJWb p2 (by positivity))
            · exact n3.trans (mul_le_mul h2 hJWb p2 hδ1')
        _ = K * ‖JV s - JW s‖ + ε := by rw [hε]; ring)
    (by simp [hJV.1, hJW.1])
  simpa using key

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma revField_sub_norm (c s : ℝ) (y : E) :
    ‖GoodField.revField V c s y - GoodField.revField W c s y‖ = ‖V (c - s) y - W (c - s) y‖ := by
  simp only [GoodField.revField]
  rw [← norm_neg]; congr 1; abel

/-- `C¹` stability of flows, in both time directions. -/
theorem norm_fderiv_gflow_sub_le (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hW : GoodField W M K) (hW2 : C2Field W K2 K3) {δ₀ δ₁ : ℝ}
    (hδ0 : ∀ s y, ‖V s y - W s y‖ ≤ δ₀)
    (hδ1 : ∀ s y, ‖fderiv ℝ (V s) y - fderiv ℝ (W s) y‖ ≤ δ₁) (t₀ t : ℝ) (x : E) :
    ‖fderiv ℝ (gflow V t₀ t) x - fderiv ℝ (gflow W t₀ t) x‖ ≤
      ((K2 * (δ₀ * |t - t₀| * Real.exp (K * |t - t₀|)) + δ₁) * Real.exp (K * |t - t₀|)) *
        |t - t₀| * Real.exp (K * |t - t₀|) := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact norm_fderiv_gflow_sub_le_fwd hV hV2 hW hW2 hδ0 hδ1 h x
  · have heV : gflow V t₀ t = gflow (GoodField.revField V (2 * t₀)) t₀ (2 * t₀ - t) :=
      funext fun x => hV.gflow_rev t₀ t x
    have heW : gflow W t₀ t = gflow (GoodField.revField W (2 * t₀)) t₀ (2 * t₀ - t) :=
      funext fun x => hW.gflow_rev t₀ t x
    have h' : t₀ ≤ 2 * t₀ - t := by linarith
    have ha : |t - t₀| = 2 * t₀ - t - t₀ := by
      rw [abs_of_nonpos (sub_nonpos.2 h)]; ring
    rw [heV, heW, ha]
    refine norm_fderiv_gflow_sub_le_fwd (hV.revField_good (2 * t₀)) (hV2.rev (2 * t₀))
      (hW.revField_good (2 * t₀)) (hW2.rev (2 * t₀)) (fun s y => ?_) (fun s y => ?_) h' x
    · rw [revField_sub_norm]; exact hδ0 _ _
    · rw [fderiv_revField, fderiv_revField]
      dsimp only
      rw [← norm_neg]
      refine le_of_eq_of_le ?_ (hδ1 (2 * t₀ - s) y)
      congr 1; abel

end AnomDiss
