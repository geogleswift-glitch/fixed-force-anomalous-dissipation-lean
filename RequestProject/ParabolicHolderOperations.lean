module

public import RequestProject.Residue

/-! # Elementary operations on the project's parabolic Hölder predicates -/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T β γ δ : ℝ}

theorem timeHolder_one_of_bdd_dt {u : ℝ → Pt d → E}
    (hd : ∀ x, ∀ t ∈ Icc (0 : ℝ) T,
      DifferentiableWithinAt ℝ (fun s => u s x) (Icc (0 : ℝ) T) t)
    (hb : BddOn T (dt T u)) : TimeHolder T 1 u := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, fun t ht s hs x => ?_⟩
  have he := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hd x r hr).hasDerivWithinAt)
    (fun r hr => hC r hr x) hs ht
  simpa only [Real.norm_eq_abs, Real.rpow_one] using he

/-- A uniform bound permits reducing a time exponent without a constant
depending on the length of the time interval. -/
theorem TimeHolder.lower_of_bdd {g : ℝ → Pt d → E}
    (h : TimeHolder T γ g) (hb : BddOn T g) (hδ : 0 ≤ δ) (hδγ : δ ≤ γ) :
    TimeHolder T δ g := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨B, hB⟩ := hb
  let K := max (max C 0) (2 * max B 0)
  have hK0 : 0 ≤ K := (le_max_right C 0).trans (le_max_left _ _)
  refine ⟨K, fun t ht s hs x => ?_⟩
  by_cases hr : |t - s| ≤ 1
  · calc
      ‖g t x - g s x‖ ≤ C * |t - s| ^ γ := hC t ht s hs x
      _ ≤ max C 0 * |t - s| ^ γ :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ K * |t - s| ^ δ := mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hr hδ hδγ)
        (Real.rpow_nonneg (abs_nonneg _) _) hK0
  · have hr1 : 1 ≤ |t - s| := (lt_of_not_ge hr).le
    have hp : 1 ≤ |t - s| ^ δ := Real.one_le_rpow hr1 hδ
    calc
      ‖g t x - g s x‖ ≤ ‖g t x‖ + ‖g s x‖ := norm_sub_le _ _
      _ ≤ 2 * max B 0 := by linarith [hB t ht x, hB s hs x, le_max_left B 0]
      _ ≤ K := le_max_right _ _
      _ ≤ K * |t - s| ^ δ := le_mul_of_one_le_right hK0 hp

theorem parHolder_of_spatial_time {g : ℝ → Pt d → E}
    (hspace : ∃ C, ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      ‖g t x - g t y‖ ≤ C * ‖x - y‖ ^ β)
    (htime : TimeHolder T (β / 2) g) : ParHolder T β g := by
  obtain ⟨A, hA⟩ := hspace
  obtain ⟨B, hB⟩ := htime
  let C := max (max A B) 0
  have hAC : A ≤ C := (le_max_left A B).trans (le_max_left _ _)
  have hBC : B ≤ C := (le_max_right A B).trans (le_max_left _ _)
  refine ⟨C, fun t ht s hs x y => ?_⟩
  calc
    ‖g t x - g s y‖ ≤ ‖g t x - g t y‖ + ‖g t y - g s y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ A * ‖x - y‖ ^ β + B * |t - s| ^ (β / 2) :=
      add_le_add (hA t ht x y) (hB t ht s hs y)
    _ ≤ C * ‖x - y‖ ^ β + C * |t - s| ^ (β / 2) := add_le_add
      (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg (norm_nonneg _) _))
      (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg (abs_nonneg _) _))
    _ = _ := by ring

theorem TimeHolder.sub {f g : ℝ → Pt d → E}
    (hf : TimeHolder T γ f) (hg : TimeHolder T γ g) :
    TimeHolder T γ (fun t x => f t x - g t x) := by
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    sub_eq_add_neg] using hf.add (hg.clm (-ContinuousLinearMap.id ℝ E))

theorem ParHolder.sub {f g : ℝ → Pt d → E}
    (hf : ParHolder T β f) (hg : ParHolder T β g) :
    ParHolder T β (fun t x => f t x - g t x) := by
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    sub_eq_add_neg] using hf.add (hg.clm (-ContinuousLinearMap.id ℝ E))

theorem TimeHolder.mul {K : Type*} [NormedField K] [NormedSpace ℝ K]
    {f g : ℝ → Pt d → K}
    (hf : TimeHolder T γ f) (hg : TimeHolder T γ g)
    (hfb : BddOn T f) (hgb : BddOn T g) :
    TimeHolder T γ (fun t x => f t x * g t x) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨F, hF⟩ := hfb
  obtain ⟨G, hG⟩ := hgb
  refine ⟨max F 0 * max B 0 + max A 0 * max G 0, fun t ht s hs x => ?_⟩
  have hp : 0 ≤ |t - s| ^ γ := Real.rpow_nonneg (abs_nonneg _) _
  have hAe := (hA t ht s hs x).trans (mul_le_mul_of_nonneg_right (le_max_left A 0) hp)
  have hBe := (hB t ht s hs x).trans (mul_le_mul_of_nonneg_right (le_max_left B 0) hp)
  have hFe := (hF t ht x).trans (le_max_left F 0)
  have hGe := (hG s hs x).trans (le_max_left G 0)
  calc
    ‖f t x * g t x - f s x * g s x‖ =
        ‖f t x * (g t x - g s x) + (f t x - f s x) * g s x‖ := by congr 1; ring
    _ ≤ ‖f t x‖ * ‖g t x - g s x‖ + ‖f t x - f s x‖ * ‖g s x‖ := by
      simpa only [norm_mul] using norm_add_le
        (f t x * (g t x - g s x)) ((f t x - f s x) * g s x)
    _ ≤ max F 0 * (max B 0 * |t - s| ^ γ) +
        (max A 0 * |t - s| ^ γ) * max G 0 := add_le_add
      (mul_le_mul hFe hBe (norm_nonneg _) (le_max_right F 0))
      (mul_le_mul hAe hGe (norm_nonneg _) (mul_nonneg (le_max_right A 0) hp))
    _ = _ := by ring

theorem ParHolder.mul {K : Type*} [NormedField K] [NormedSpace ℝ K]
    {f g : ℝ → Pt d → K}
    (hf : ParHolder T β f) (hg : ParHolder T β g)
    (hfb : BddOn T f) (hgb : BddOn T g) :
    ParHolder T β (fun t x => f t x * g t x) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  obtain ⟨F, hF⟩ := hfb
  obtain ⟨G, hG⟩ := hgb
  refine ⟨max F 0 * max B 0 + max A 0 * max G 0, fun t ht s hs x y => ?_⟩
  have hp : 0 ≤ ‖x - y‖ ^ β + |t - s| ^ (β / 2) := add_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hAe := (hA t ht s hs x y).trans
    (mul_le_mul_of_nonneg_right (le_max_left A 0) hp)
  have hBe := (hB t ht s hs x y).trans
    (mul_le_mul_of_nonneg_right (le_max_left B 0) hp)
  have hFe := (hF t ht x).trans (le_max_left F 0)
  have hGe := (hG s hs y).trans (le_max_left G 0)
  calc
    ‖f t x * g t x - f s y * g s y‖ =
        ‖f t x * (g t x - g s y) + (f t x - f s y) * g s y‖ := by congr 1; ring
    _ ≤ ‖f t x‖ * ‖g t x - g s y‖ + ‖f t x - f s y‖ * ‖g s y‖ := by
      simpa only [norm_mul] using norm_add_le
        (f t x * (g t x - g s y)) ((f t x - f s y) * g s y)
    _ ≤ max F 0 * (max B 0 * (‖x - y‖ ^ β + |t - s| ^ (β / 2))) +
        (max A 0 * (‖x - y‖ ^ β + |t - s| ^ (β / 2))) * max G 0 := add_le_add
      (mul_le_mul hFe hBe (norm_nonneg _) (le_max_right F 0))
      (mul_le_mul hAe hGe (norm_nonneg _) (mul_nonneg (le_max_right A 0) hp))
    _ = _ := by ring

end AnomDiss
