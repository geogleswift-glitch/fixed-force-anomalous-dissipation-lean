module

public import RequestProject.FlowBasic

/-!
# Analytic tools for differentiating flows

A Grönwall estimate in closed form, a radial truncation, global existence for linear ODEs on a
compact time interval, a first-order Taylor estimate, and a criterion for Fréchet
differentiability from a quadratic remainder bound.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real Asymptotics
open scoped NNReal

noncomputable section

namespace AnomDiss

/-- Grönwall's inequality in closed form. -/
lemma gronwallBound_le {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with h | h
  · subst h; simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 h.ne']
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have := Real.add_one_le_exp (-(K * x))
      have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (K * x)]
    calc δ * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1)
        ≤ δ * Real.exp (K * x) + ε / K * (K * x * Real.exp (K * x)) := by gcongr
      _ = (δ + ε * x) * Real.exp (K * x) := by field_simp

/-- Grönwall's inequality for a function with an affine bound on its right derivative. -/
lemma norm_le_of_deriv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b K ε δ : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hd : ∀ s ∈ Icc a b, HasDerivWithinAt f (f' s) (Icc a b) s)
    (hb : ∀ s ∈ Icc a b, ‖f' s‖ ≤ K * ‖f s‖ + ε) (h0 : ‖f a‖ ≤ δ) :
    ‖f b‖ ≤ (δ + ε * (b - a)) * Real.exp (K * (b - a)) := by
  have hc : ContinuousOn f (Icc a b) := fun s hs => (hd s hs).continuousWithinAt
  have hd' : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s := fun s hs => by
    have := hd s (Ico_subset_Icc_self hs)
    refine (this.mono_of_mem_nhdsWithin ?_)
    exact Icc_mem_nhdsGE_of_mem ⟨hs.1, hs.2⟩
  have := norm_le_gronwallBound_of_norm_deriv_right_le hc hd' h0
    (fun s hs => hb s (Ico_subset_Icc_self hs)) b ⟨hab, le_rfl⟩
  exact this.trans (gronwallBound_le hK hε)

/-- A version with `HasDerivAt` on the interval. -/
lemma norm_le_of_hasDerivAt_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b K ε δ : ℝ} (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hd : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Icc a b, ‖f' s‖ ≤ K * ‖f s‖ + ε) (h0 : ‖f a‖ ≤ δ) :
    ‖f b‖ ≤ (δ + ε * (b - a)) * Real.exp (K * (b - a)) :=
  norm_le_of_deriv_le hab hK hε (fun s hs => (hd s hs).hasDerivWithinAt) hb h0

/-! ### Radial truncation -/

/-- The radial retraction onto the closed ball of radius `R`. -/
def rtrunc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) (y : F) : F :=
  min 1 (R / ‖y‖) • y

section Trunc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma rtrunc_of_le {R : ℝ} {y : F} (h : ‖y‖ ≤ R) : rtrunc R y = y := by
  unfold rtrunc
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
  · rw [norm_eq_zero.1 h0.symm]; simp
  · rw [min_eq_left ((one_le_div h0).2 h), one_smul]

lemma norm_rtrunc_eq {R : ℝ} (hR : 0 ≤ R) (y : F) : ‖rtrunc R y‖ = min ‖y‖ R := by
  unfold rtrunc
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
  · rw [norm_eq_zero.1 h0.symm]; simp [hR]
  · have hm : 0 ≤ min 1 (R / ‖y‖) := le_min zero_le_one (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm]
    rcases le_total ‖y‖ R with h | h
    · rw [min_eq_left ((one_le_div h0).2 h), min_eq_left h, one_mul]
    · rw [min_eq_right ((div_le_one h0).2 h), min_eq_right h, div_mul_cancel₀ _ h0.ne']

lemma norm_rtrunc_le {R : ℝ} (hR : 0 ≤ R) (y : F) : ‖rtrunc R y‖ ≤ ‖y‖ := by
  rw [norm_rtrunc_eq hR]; exact min_le_left _ _

lemma norm_rtrunc_le' {R : ℝ} (hR : 0 ≤ R) (y : F) : ‖rtrunc R y‖ ≤ R := by
  rw [norm_rtrunc_eq hR]; exact min_le_right _ _

lemma rtrunc_lip_aux {R : ℝ} (hR : 0 ≤ R) {x y : F} (hxy : ‖y‖ ≤ ‖x‖) :
    ‖rtrunc R x - rtrunc R y‖ ≤ 2 * ‖x - y‖ := by
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
  · have hy : y = 0 := norm_eq_zero.1 h0.symm
    subst hy
    have : rtrunc R (0 : F) = 0 := by simp [rtrunc]
    rw [this, sub_zero, sub_zero]
    linarith [norm_rtrunc_le hR x, norm_nonneg x]
  have h1 : 0 < ‖x‖ := h0.trans_le hxy
  set sx := min 1 (R / ‖x‖)
  set sy := min 1 (R / ‖y‖)
  have hsx0 : 0 ≤ sx := le_min zero_le_one (by positivity)
  have hsx1 : sx ≤ 1 := min_le_left _ _
  have hsy0 : 0 ≤ sy := le_min zero_le_one (by positivity)
  have hmono : sx * ‖x‖ = min ‖x‖ R := by
    have := norm_rtrunc_eq hR x
    unfold rtrunc at this
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsx0] at this
  have hmono' : sy * ‖y‖ = min ‖y‖ R := by
    have := norm_rtrunc_eq hR y
    unfold rtrunc at this
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsy0] at this
  have hsxy : sx ≤ sy := min_le_min le_rfl (div_le_div_of_nonneg_left hR h0 hxy)
  have he : rtrunc R x - rtrunc R y = sx • (x - y) - (sy - sx) • y := by
    simp only [rtrunc, sx, sy, smul_sub, sub_smul]; abel
  rw [he]
  have hxy' : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
  have hmin : min ‖y‖ R ≤ min ‖x‖ R := min_le_min hxy le_rfl
  calc ‖sx • (x - y) - (sy - sx) • y‖ ≤ ‖sx • (x - y)‖ + ‖(sy - sx) • y‖ := norm_sub_le _ _
    _ = sx * ‖x - y‖ + (sy - sx) * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsx0,
          abs_of_nonneg (by linarith)]
    _ ≤ 2 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]

lemma rtrunc_lip {R : ℝ} (hR : 0 ≤ R) : LipschitzWith 2 (rtrunc (F := F) R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact_mod_cast rtrunc_lip_aux hR h
  · rw [norm_sub_rev, norm_sub_rev x]; exact_mod_cast rtrunc_lip_aux hR h

end Trunc

/-! ### Linear ODEs -/

/-- Existence for ODEs `y' = W(t, y)` on a compact forward time interval, where `W(t, ·)` is
`K`-Lipschitz with at most affine growth (e.g. linear ODEs with bounded coefficients). -/
theorem exists_affODE_on {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {W : ℝ → F → F} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) {K G : ℝ} (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hW : ∀ y, ContinuousOn (fun t => W t y) (Icc t₀ t₁))
    (hlip : ∀ t ∈ Icc t₀ t₁, ∀ y z, ‖W t y - W t z‖ ≤ K * ‖y - z‖)
    (hb : ∀ t ∈ Icc t₀ t₁, ∀ y, ‖W t y‖ ≤ K * ‖y‖ + G) (y₀ : F) :
    ∃ y : ℝ → F, y t₀ = y₀ ∧ ∀ t ∈ Icc t₀ t₁, HasDerivAt y (W t (y t)) t := by
  set c : ℝ → ℝ := fun s => max t₀ (min s t₁) with hc
  have hcc : Continuous c := by fun_prop
  have hcm : ∀ s, c s ∈ Icc t₀ t₁ := fun s => ⟨le_max_left _ _, max_le h01 (min_le_right _ _)⟩
  have hcid : ∀ s ∈ Icc t₀ t₁, c s = s := fun s hs => by
    simp only [hc]; rw [min_eq_left hs.2, max_eq_right hs.1]
  set R : ℝ := (‖y₀‖ + G * (t₁ - t₀)) * Real.exp (K * (t₁ - t₀)) with hR
  have hR0 : 0 ≤ R := by have := sub_nonneg.2 h01; positivity
  set W' : ℝ → F → F := fun t y => W (c t) (rtrunc R y) with hW'def
  have hW' : GoodField W' ⟨K * R + G, by positivity⟩ ⟨K * 2, by positivity⟩ := by
    refine ⟨fun y => ?_, fun t y => ?_, fun t => ?_⟩
    · exact (hW (rtrunc R y)).comp_continuous hcc hcm
    · change ‖W (c t) (rtrunc R y)‖ ≤ K * R + G
      refine (hb _ (hcm t) _).trans ?_
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_rtrunc_le' hR0 y) hK) le_rfl
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm]
      change ‖W (c t) (rtrunc R x) - W (c t) (rtrunc R y)‖ ≤ (K * 2) * ‖x - y‖
      refine (hlip _ (hcm t) _ _).trans ?_
      have := (rtrunc_lip (F := F) hR0).dist_le_mul x y
      rw [dist_eq_norm, dist_eq_norm] at this
      have h2 : ‖rtrunc R x - rtrunc R y‖ ≤ 2 * ‖x - y‖ := by exact_mod_cast this
      calc
        K * ‖rtrunc R x - rtrunc R y‖ ≤ K * (2 * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left h2 hK
        _ = (K * 2) * ‖x - y‖ := (mul_assoc _ _ _).symm
  refine ⟨fun t => gflow W' t₀ t y₀, hW'.gflow_self t₀ y₀, fun t ht => ?_⟩
  have hbd : ‖gflow W' t₀ t y₀‖ ≤ R := by
    have key := norm_le_of_hasDerivAt_le (f := fun s => gflow W' t₀ s y₀)
      (f' := fun s => W' s (gflow W' t₀ s y₀)) (K := K) (ε := G) (δ := ‖y₀‖) ht.1 hK hG
      (fun s _ => hW'.hasDerivAt_gflow t₀ s y₀) (fun s _ => by
        simp only [hW'def]
        refine (hb _ (hcm s) _).trans ?_
        gcongr
        exact norm_rtrunc_le hR0 _) (by simp only [hW'.gflow_self]; exact le_rfl)
    refine key.trans ?_
    rw [hR]
    have h1 : t - t₀ ≤ t₁ - t₀ := by linarith [ht.2]
    have h2 : 0 ≤ t - t₀ := by linarith [ht.1]
    have h3 : ‖y₀‖ + G * (t - t₀) ≤ ‖y₀‖ + G * (t₁ - t₀) := by gcongr
    have h4 : Real.exp (K * (t - t₀)) ≤ Real.exp (K * (t₁ - t₀)) := by gcongr
    exact mul_le_mul h3 h4 (Real.exp_pos _).le (by have := sub_nonneg.2 h01; positivity)
  have := hW'.hasDerivAt_gflow t₀ t y₀
  have e : W' t (gflow W' t₀ t y₀) = W t (gflow W' t₀ t y₀) := by
    show W (c t) (rtrunc R _) = _
    rw [rtrunc_of_le hbd, hcid t ht]
  rw [e] at this
  exact this

/-! ### Taylor estimates and differentiability -/

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- First-order Taylor estimate from a Lipschitz derivative. -/
lemma norm_taylor1_le {f : E → F} {L : ℝ} (hL0 : 0 ≤ L) (hf : Differentiable ℝ f)
    (hL : ∀ a b, ‖fderiv ℝ f b - fderiv ℝ f a‖ ≤ L * ‖b - a‖) (a b : E) :
    ‖f b - f a - fderiv ℝ f a (b - a)‖ ≤ L * ‖b - a‖ ^ 2 := by
  set g : E → F := fun z => f z - fderiv ℝ f a z with hg
  have hgd : ∀ z, HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f a) z := fun z =>
    (hf z).hasFDerivAt.sub (fderiv ℝ f a).hasFDerivAt
  have key := (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le (f := g)
    (C := L * ‖b - a‖) (fun z _ => (hgd z).differentiableAt) (fun z hz => by
      rw [(hgd z).fderiv]
      refine (hL a z).trans ?_
      have hd := dist_add_dist_of_mem_segment hz
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hd
      have : ‖z - a‖ ≤ ‖b - a‖ := by
        rw [norm_sub_rev z a, norm_sub_rev b a]; linarith [norm_nonneg (z - b)]
      exact mul_le_mul_of_nonneg_left this hL0)
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  have he : g b - g a = f b - f a - fderiv ℝ f a (b - a) := by
    simp only [hg, map_sub]; abel
  rw [← he]
  calc ‖g b - g a‖ ≤ L * ‖b - a‖ * ‖b - a‖ := key
    _ = L * ‖b - a‖ ^ 2 := by ring

/-- A Lipschitz bound from a bound on the derivative. -/
lemma norm_sub_le_of_fderiv_le {f : E → F} {C : ℝ} (hf : Differentiable ℝ f)
    (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (a b : E) : ‖f b - f a‖ ≤ C * ‖b - a‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z) (fun z _ => hC z)
    (mem_univ _) (mem_univ _)

/-- Fréchet differentiability from a quadratic remainder bound. -/
lemma hasFDerivAt_of_sq_bound {f : E → F} {f' : E →L[ℝ] F} {x : E} {C : ℝ}
    (h : ∀ y, ‖f y - f x - f' (y - x)‖ ≤ C * ‖y - x‖ ^ 2) : HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 : (fun h => f (x + h) - f x - f' h) =O[𝓝 0] (fun h : E => ‖h‖ ^ 2) :=
    IsBigO.of_bound C (Eventually.of_forall fun v => by
      have := h (x + v)
      simp only [add_sub_cancel_left] at this
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact this)
  exact h1.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

end Taylor

/-- Joint continuity from continuity in time and a uniform Lipschitz bound in space. -/
lemma continuous_comp_of_lip {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {D : ℝ → E → F} (hc : ∀ x, Continuous fun t => D t x) {L : ℝ≥0}
    (hl : ∀ t, LipschitzWith L (D t)) {φ : ℝ → E} (hφ : Continuous φ) :
    Continuous fun t => D t (φ t) := by
  have : Continuous fun p : ℝ × E => D p.1 p.2 :=
    continuous_prod_of_continuous_lipschitzWith' _ L (fun t => hl t) hc
  exact this.comp (continuous_id.prodMk hφ)

end AnomDiss
