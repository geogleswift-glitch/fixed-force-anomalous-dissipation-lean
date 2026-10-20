module

public import RequestProject.FlowDeriv

/-!
# `C²` regularity of flow maps

Assembly of the variational estimates: the flow maps of a `C2Field` are `C²`, with explicit
bounds on `DΦ - I` and `D²Φ` in terms of the elapsed time.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {V : ℝ → E → E} {M K : ℝ≥0} {K2 K3 : ℝ} {t₀ t₁ : ℝ}

/-- **`C²` regularity of flows (forward times).** -/
theorem gflow_C2_fwd (hV : GoodField V M K) (hV2 : C2Field V K2 K3) (h01 : t₀ ≤ t₁) :
    ContDiff ℝ 2 (gflow V t₀ t₁) ∧ ∀ x,
      ‖fderiv ℝ (gflow V t₀ t₁) x - ContinuousLinearMap.id ℝ E‖ ≤
        K * (t₁ - t₀) * Real.exp (K * (t₁ - t₀)) ∧
      ‖fderiv ℝ (fderiv ℝ (gflow V t₀ t₁)) x‖ ≤ K2 * (t₁ - t₀) * Real.exp (3 * K * (t₁ - t₀)) := by
  choose Jf hJf using fun x => exists_varSol hV hV2 h01 x
  choose Hf hHf using fun x => exists_varSol2 hV hV2 h01 (hJf x)
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  have hD : ∀ x, HasFDerivAt (gflow V t₀ t₁) (Jf x t₁) x := fun x =>
    (hJf x).hasFDerivAt hV hV2 ht₁
  have hD2 : ∀ x, HasFDerivAt (fun y => Jf y t₁) (Hf x t₁) x := fun x =>
    hasFDerivAt_of_sq_bound (C := (t₁ - t₀) * Real.exp (K * (t₁ - t₀)) *
      (K3 * Real.exp (K * (t₁ - t₀)) ^ 3 + 2 * K2 * (K2 * (t₁ - t₀) *
        Real.exp (3 * K * (t₁ - t₀))) * Real.exp (K * (t₁ - t₀)))) fun y =>
      ((hHf x).remainder hV hV2 (hJf x) (hJf y) ht₁).trans (le_of_eq (by ring))
  have hcont : Continuous fun x => Hf x t₁ := by
    refine (LipschitzWith.of_dist_le' (f := fun x => Hf x t₁) (K := (t₁ - t₀) * Real.exp (K * (t₁ - t₀)) *
      (3 * K2 * (K2 * (t₁ - t₀) * Real.exp (3 * K * (t₁ - t₀))) * Real.exp (K * (t₁ - t₀)) +
        K3 * Real.exp (K * (t₁ - t₀)) ^ 3)) fun x y => ?_).continuous
    refine (dist_eq_norm (E := E →L[ℝ] E →L[ℝ] E) (Hf x t₁) (Hf y t₁)).le.trans ?_
    rw [dist_eq_norm]
    exact ((hHf y).lipschitz hV hV2 (hJf y) (hJf x) (hHf x) ht₁).trans (le_of_eq (by ring))
  have h1 : ContDiff ℝ 1 fun x => Jf x t₁ := contDiff_one_iff_hasFDerivAt.2 ⟨_, hcont, hD2⟩
  have h2 : ContDiff ℝ ((1 : ℕ) + 1) (gflow V t₀ t₁) :=
    contDiff_succ_iff_hasFDerivAt.2 ⟨_, by simpa using h1, hD⟩
  have hf : fderiv ℝ (gflow V t₀ t₁) = fun x => Jf x t₁ := funext fun x => (hD x).fderiv
  refine ⟨by convert h2 using 1 <;> norm_num, fun x => ⟨?_, ?_⟩⟩
  · rw [hf]; exact (hJf x).norm_sub_id_le hV ht₁
  · rw [hf, (hD2 x).fderiv]; exact (hHf x).norm_le hV hV2 (hJf x) ht₁

omit [CompleteSpace E] in
lemma fderiv_revField (V : ℝ → E → E) (c t : ℝ) :
    fderiv ℝ (GoodField.revField V c t) = fun x => -fderiv ℝ (V (c - t)) x :=
  funext fun _ => fderiv_neg (f := V (c - t))

omit [CompleteSpace E] in
lemma fderiv_fderiv_revField (V : ℝ → E → E) (c t : ℝ) :
    fderiv ℝ (fderiv ℝ (GoodField.revField V c t)) = fun x => -fderiv ℝ (fderiv ℝ (V (c - t))) x := by
  rw [fderiv_revField]
  exact funext fun _ => fderiv_neg (f := fderiv ℝ (V (c - t)))

omit [CompleteSpace E] in
/-- Time reversal preserves the second-order regularity hypotheses. -/
lemma C2Field.rev (hV2 : C2Field V K2 K3) (c : ℝ) : C2Field (GoodField.revField V c) K2 K3 where
  diff t := (hV2.diff (c - t)).neg
  d2 t x := by
    rw [fderiv_fderiv_revField]
    exact (norm_neg (E := E →L[ℝ] E →L[ℝ] E) _).le.trans (hV2.d2 _ _)
  nonneg3 := hV2.nonneg3
  lip2 t a b := by
    rw [fderiv_fderiv_revField, ← neg_sub']
    exact (norm_neg (E := E →L[ℝ] E →L[ℝ] E) _).le.trans (hV2.lip2 (c - t) a b)
  c1 x := by
    simp only [fderiv_revField]
    exact ((hV2.c1 x).comp (continuous_const.sub continuous_id)).neg
  c2 x := by
    simp only [fderiv_fderiv_revField]
    exact ((hV2.c2 x).comp (continuous_const.sub continuous_id)).neg

/-- **`C²` regularity of flow maps**, for forward and backward times. -/
theorem gflow_C2 (hV : GoodField V M K) (hV2 : C2Field V K2 K3) (t₀ t : ℝ) :
    ContDiff ℝ 2 (gflow V t₀ t) ∧ ∀ x,
      ‖fderiv ℝ (gflow V t₀ t) x - ContinuousLinearMap.id ℝ E‖ ≤
        K * |t - t₀| * Real.exp (K * |t - t₀|) ∧
      ‖fderiv ℝ (fderiv ℝ (gflow V t₀ t)) x‖ ≤ K2 * |t - t₀| * Real.exp (3 * K * |t - t₀|) := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact gflow_C2_fwd hV hV2 h
  · have he : gflow V t₀ t = gflow (GoodField.revField V (2 * t₀)) t₀ (2 * t₀ - t) :=
      funext fun x => hV.gflow_rev t₀ t x
    have h' : t₀ ≤ 2 * t₀ - t := by linarith
    have key := gflow_C2_fwd (hV.revField_good (2 * t₀)) (hV2.rev (2 * t₀)) h'
    have ha : |t - t₀| = 2 * t₀ - t - t₀ := by
      rw [abs_of_nonpos (sub_nonpos.2 h)]; ring
    rw [he, ha]
    exact key

end AnomDiss
