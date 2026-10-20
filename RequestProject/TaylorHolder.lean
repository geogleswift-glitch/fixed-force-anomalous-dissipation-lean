module

public import RequestProject.Basic

/-!
# Second-order Taylor expansion with Hölder remainder

For a `C²` function `f` on `ℝ²` whose second partial derivatives are `β`-Hölder with constant
`H`, the second-order Taylor remainder at `z` in direction `δ` is at most `4 H ‖δ‖^{2+β}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_apply_eq_sum_pd {f : Pt 2 → E} (x δ : Pt 2) :
    fderiv ℝ f x δ = ∑ j, δ j • pd j f x := by
  have hδ : δ = ∑ j, δ j • (Pi.single j 1 : Pt 2) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hδ]
  simp only [map_sum, map_smul, pd]

lemma differentiable_pd_of_C2 {f : Pt 2 → E} (hf : ContDiff ℝ 2 f) (j : Fin 2) :
    Differentiable ℝ (pd j f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ f) := h1.differentiable (by norm_num)
  intro x
  exact (h2 x).clm_apply (differentiableAt_const _)

lemma hasDerivAt_dirLine {f : Pt 2 → E} (hf : Differentiable ℝ f) (z δ : Pt 2) (u : ℝ) :
    HasDerivAt (fun u : ℝ => f (z + u • δ)) (∑ j, δ j • pd j f (z + u • δ)) u := by
  have hl : HasDerivAt (fun u : ℝ => z + u • δ) δ u := by
    simpa using ((hasDerivAt_id u).smul_const δ).const_add z
  have := (hf (z + u • δ)).hasFDerivAt.comp_hasDerivAt u hl
  rw [fderiv_apply_eq_sum_pd] at this
  exact this

lemma norm_coord_le (δ : Pt 2) (i : Fin 2) : ‖δ i‖ ≤ ‖δ‖ := norm_le_pi_norm δ i

/-- Second-order Taylor formula with Hölder remainder. -/
theorem taylor2_holder {f : Pt 2 → E} (hf : ContDiff ℝ 2 f) {H β : ℝ} (hβ : 0 ≤ β)
    (hH : ∀ i j x y, ‖pd i (pd j f) x - pd i (pd j f) y‖ ≤ H * ‖x - y‖ ^ β) (z δ : Pt 2) :
    ‖f (z + δ) - f z - ∑ j, δ j • pd j f z - (1 / 2 : ℝ) • ∑ j, ∑ i, (δ j * δ i) • pd i (pd j f) z‖
      ≤ 4 * H * ‖δ‖ ^ (2 + β) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  set g1 : ℝ → E := fun u => ∑ j, δ j • pd j f (z + u • δ) with hg1
  set g2 : ℝ → E := fun u => ∑ j, ∑ i, (δ j * δ i) • pd i (pd j f) (z + u • δ) with hg2
  have d0 : ∀ u, HasDerivAt (fun u : ℝ => f (z + u • δ)) (g1 u) u := hasDerivAt_dirLine hf1 z δ
  have d1 : ∀ u, HasDerivAt g1 (g2 u) u := by
    intro u
    have : HasDerivAt g1 (∑ j, δ j • ∑ i, δ i • pd i (pd j f) (z + u • δ)) u :=
      HasDerivAt.fun_sum fun j _ => (hasDerivAt_dirLine (differentiable_pd_of_C2 hf j) z δ u).const_smul (δ j)
    convert this using 1
    simp only [hg2, Finset.smul_sum, smul_smul]
  have hH0 : 0 ≤ H := by
    have := hH 0 0 (Pi.single 0 1) 0
    have h1 : (0:ℝ) ≤ H * ‖(Pi.single 0 1 : Pt 2) - 0‖ ^ β := (norm_nonneg _).trans this
    have h2 : ‖(Pi.single 0 1 : Pt 2) - 0‖ = 1 := by rw [sub_zero, Pi.norm_single, norm_one]
    rw [h2, Real.one_rpow, mul_one] at h1; exact h1
  set B : ℝ := 4 * H * ‖δ‖ ^ (2 + β) with hB
  have hB0 : 0 ≤ B := by positivity
  -- bound on the second derivative difference
  have hg2b : ∀ u ∈ Icc (0:ℝ) 1, ‖g2 u - g2 0‖ ≤ B := by
    intro u hu
    have e : g2 u - g2 0 = ∑ j, ∑ i, (δ j * δ i) •
        (pd i (pd j f) (z + u • δ) - pd i (pd j f) z) := by
      simp only [hg2, zero_smul, add_zero, ← Finset.sum_sub_distrib, smul_sub]
    rw [e]
    have hterm : ∀ i j, ‖(δ j * δ i) • (pd i (pd j f) (z + u • δ) - pd i (pd j f) z)‖ ≤
        H * ‖δ‖ ^ (2 + β) := by
      intro i j
      rw [norm_smul]
      have h1 := hH i j (z + u • δ) z
      have h2 : ‖z + u • δ - z‖ ≤ ‖δ‖ := by
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hu.2
      have h3 : ‖δ j * δ i‖ ≤ ‖δ‖ ^ 2 := by
        rw [norm_mul, sq]
        exact mul_le_mul (norm_coord_le δ j) (norm_coord_le δ i) (norm_nonneg _) (norm_nonneg _)
      calc ‖δ j * δ i‖ * ‖pd i (pd j f) (z + u • δ) - pd i (pd j f) z‖
          ≤ ‖δ‖ ^ 2 * (H * ‖δ‖ ^ β) := by
            refine mul_le_mul h3 (h1.trans ?_) (norm_nonneg _) (by positivity)
            gcongr
        _ = H * ‖δ‖ ^ (2 + β) := by
            rw [Real.rpow_add' (norm_nonneg _) (by positivity)]
            norm_cast; ring
    calc ‖∑ j, ∑ i, (δ j * δ i) • (pd i (pd j f) (z + u • δ) - pd i (pd j f) z)‖
        ≤ ∑ j : Fin 2, ∑ i : Fin 2, H * ‖δ‖ ^ (2 + β) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i j))
      _ = B := by simp [hB]; ring
  -- first integration
  set p1 : ℝ → E := fun u => g1 u - g1 0 - u • g2 0 with hp1
  have dp1 : ∀ u, HasDerivAt p1 (g2 u - g2 0) u := by
    intro u
    have := ((d1 u).sub_const (g1 0)).fun_sub ((hasDerivAt_id u).smul_const (g2 0))
    simpa only [hp1, Pi.sub_apply, id_eq, one_smul] using this
  have hp1b : ∀ u ∈ Icc (0:ℝ) 1, ‖p1 u‖ ≤ B := by
    intro u hu
    have key := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (dp1 s).hasDerivWithinAt) hg2b ⟨le_rfl, zero_le_one⟩ hu
    have hp10 : p1 0 = 0 := by simp [hp1]
    rw [hp10, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hu.1] at key
    exact key.trans (mul_le_of_le_one_right hB0 hu.2)
  -- second integration
  set p0 : ℝ → E := fun u => f (z + u • δ) - f z - u • g1 0 - (u ^ 2 / 2) • g2 0 with hp0
  have dp0 : ∀ u, HasDerivAt p0 (p1 u) u := by
    intro u
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
      simpa using ((hasDerivAt_pow 2 u).div_const 2)
    have := (((d0 u).sub_const (f z)).fun_sub ((hasDerivAt_id u).smul_const (g1 0))).fun_sub
      (h2.smul_const (g2 0))
    simpa only [hp0, hp1, Pi.sub_apply, id_eq, one_smul] using this
  have key := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (dp0 s).hasDerivWithinAt) hp1b ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hp00 : p0 0 = 0 := by simp [hp0]
  rw [hp00, sub_zero, sub_zero, norm_one, mul_one] at key
  have e : p0 1 = f (z + δ) - f z - ∑ j, δ j • pd j f z -
      (1 / 2 : ℝ) • ∑ j, ∑ i, (δ j * δ i) • pd i (pd j f) z := by
    simp only [hp0, hg1, hg2, one_smul, zero_smul, add_zero, one_pow]
  rw [← e]; exact key

end AnomDiss
