module

public import RequestProject.SplitRep

/-!
# Ingredients for the negative moment bound of the split maps

An elementary one-sided Lipschitz estimate for `t ↦ t^{-σ}`, the comparison of `|Aᵀe|` for two
Jacobians, the inverse terminal flow map of `b_ω` (built from the block maps), and the negative
moment bound for it inherited from Lemma 2.7.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal Matrix

noncomputable section

namespace AnomDiss

instance isFiniteMeasure_restrict_cell : IsFiniteMeasure (volume.restrict (cell 2)) := by
  rw [isFiniteMeasure_restrict]; simp [cell, Real.volume_Icc_pi]


/-- One-sided Lipschitz bound for `t ↦ t^{-σ}` away from zero: if `a ≥ c > 0` and `b ≥ 0` then
`a^{-σ} ≤ b^{-σ} + (σ+1)c^{-σ-1}|a-b|` (with the convention `0^{-σ} = 0`). -/
lemma rpow_neg_le_add {a b c σ : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) (hσ : 0 < σ) :
    a ^ (-σ) ≤ b ^ (-σ) + (σ + 1) * c ^ (-σ - 1) * |a - b| := by
  have ha0 : 0 < a := hc.trans_le ha
  have hcp : 0 < c ^ (-σ - 1) := Real.rpow_pos_of_pos hc _
  have hL0 : 0 ≤ (σ + 1) * c ^ (-σ - 1) := by positivity
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    rw [Real.zero_rpow (by linarith : -σ ≠ 0), zero_add, sub_zero, abs_of_pos ha0]
    have h1 : a ^ (-σ) ≤ c ^ (-σ) := Real.rpow_le_rpow_of_nonpos hc ha (by linarith)
    have h2 : c ^ (-σ) = c ^ (-σ - 1) * c := by
      rw [← Real.rpow_add_one hc.ne']; ring_nf
    have h3 : c ^ (-σ - 1) * c ≤ c ^ (-σ - 1) * a := mul_le_mul_of_nonneg_left ha hcp.le
    have h4 : 0 ≤ σ * c ^ (-σ - 1) * a := by positivity
    nlinarith
  rcases le_or_gt a b with hab | hab
  · have hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt (fun x : ℝ => x ^ (-σ))
        (-σ * x ^ (-σ - 1)) (Icc a b) x := fun x hx =>
      (Real.hasDerivAt_rpow_const (Or.inl (ha0.trans_le hx.1).ne')).hasDerivWithinAt
    have hbound : ∀ x ∈ Icc a b, ‖-σ * x ^ (-σ - 1)‖ ≤ σ * c ^ (-σ - 1) := by
      intro x hx
      have hx0 : 0 < x := ha0.trans_le hx.1
      rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hσ,
        abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hc (ha.trans hx.1) (by linarith)) hσ.le
    have key := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
    have h3 := (abs_le.1 key).1
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at h3
    rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
    nlinarith
  · have := Real.rpow_le_rpow_of_nonpos hbpos hab.le (by linarith : -σ ≤ 0)
    linarith [mul_nonneg hL0 (abs_nonneg (a - b))]

lemma abs_jac_entry_sub_le (Φ Ψ : Pt 2 → Pt 2) (y : Pt 2) (i j : Fin 2) :
    |(jac Φ y - jac Ψ y) i j| ≤ ‖fderiv ℝ Φ y - fderiv ℝ Ψ y‖ := by
  simp only [Matrix.sub_apply, jac, Matrix.of_apply]
  have h1 : ‖(Pi.single j (1:ℝ) : Pt 2)‖ ≤ 1 := by
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun k => ?_
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  calc |fderiv ℝ Φ y (Pi.single j 1) i - fderiv ℝ Ψ y (Pi.single j 1) i|
      = ‖(fderiv ℝ Φ y - fderiv ℝ Ψ y) (Pi.single j 1) i‖ := by
        simp [Real.norm_eq_abs]
    _ ≤ ‖(fderiv ℝ Φ y - fderiv ℝ Ψ y) (Pi.single j 1)‖ := norm_le_pi_norm _ i
    _ ≤ ‖fderiv ℝ Φ y - fderiv ℝ Ψ y‖ * ‖(Pi.single j (1:ℝ) : Pt 2)‖ :=
        (fderiv ℝ Φ y - fderiv ℝ Ψ y).le_opNorm _
    _ ≤ ‖fderiv ℝ Φ y - fderiv ℝ Ψ y‖ := mul_le_of_le_one_right (norm_nonneg _) h1

/-- `|DΦ(y)ᵀe|` and `|DΨ(y)ᵀe|` differ by at most `2‖DΦ(y) - DΨ(y)‖` for a unit vector `e`. -/
lemma abs_euclNorm_jac_sub_le (Φ Ψ : Pt 2 → Pt 2) (y e : Pt 2) (he : euclNorm e = 1) :
    |euclNorm ((jac Φ y)ᵀ *ᵥ e) - euclNorm ((jac Ψ y)ᵀ *ᵥ e)| ≤
      2 * ‖fderiv ℝ Φ y - fderiv ℝ Ψ y‖ := by
  set M := jac Φ y - jac Ψ y with hMdef
  have hM := abs_jac_entry_sub_le Φ Ψ y
  have hM' : ∀ i j, |(-M) i j| ≤ ‖fderiv ℝ Φ y - fderiv ℝ Ψ y‖ := fun i j => by
    rw [Matrix.neg_apply, abs_neg]; exact hM i j
  have e1 : (jac Φ y)ᵀ *ᵥ e = (jac Ψ y)ᵀ *ᵥ e + Mᵀ *ᵥ e := by
    rw [hMdef, Matrix.transpose_sub, Matrix.sub_mulVec]; abel
  have e2 : (jac Ψ y)ᵀ *ᵥ e = (jac Φ y)ᵀ *ᵥ e + (-M)ᵀ *ᵥ e := by
    rw [hMdef, Matrix.transpose_neg, Matrix.transpose_sub, Matrix.neg_mulVec, Matrix.sub_mulVec]
    abel
  have b1 := euclNorm_transpose_mulVec_le M _ hM e
  have b2 := euclNorm_transpose_mulVec_le (-M) _ hM' e
  rw [he] at b1 b2
  rw [abs_le]; constructor
  · have := euclNorm_add_le ((jac Φ y)ᵀ *ᵥ e) ((-M)ᵀ *ᵥ e); rw [← e2] at this; linarith
  · have := euclNorm_add_le ((jac Ψ y)ᵀ *ᵥ e) (Mᵀ *ᵥ e); rw [← e1] at this; linarith

lemma contDiff_foldl_mapG (l : List (Bool × Pt 2)) :
    ContDiff ℝ ∞ (fun x => l.foldl (fun y p => mapG p.1 p.2 y) x) := by
  induction l with
  | nil =>
    simpa only [List.foldl_nil] using
      (contDiff_fun_id : ContDiff ℝ ∞ (fun x : Pt 2 => x))
  | cons a l ih =>
    simpa only [List.foldl_cons, Function.comp_def] using
      (ih.comp (contDiff_mapG a.1 a.2))

lemma contDiff_blockMap {L : ℕ} (w : Fin L → Bool × Pt 2) : ContDiff ℝ ∞ (blockMap w) :=
  contDiff_foldl_mapG _

/-- The inverse terminal flow map `Ψ₀` of `b_ω`: the inverse block map conjugated by the global
translation. -/
def termInv {L : ℕ} (w : BlockParam L) (y : Pt 2) : Pt 2 := blockMapInv w.1 (y - w.2) + w.2

lemma contDiff_termInv {L : ℕ} (w : BlockParam L) : ContDiff ℝ ∞ (termInv w) :=
  ((contDiff_blockMapInv w.1).comp (contDiff_id.sub contDiff_const)).add contDiff_const

lemma fderiv_termInv {L : ℕ} (w : BlockParam L) (y : Pt 2) :
    fderiv ℝ (termInv w) y = fderiv ℝ (blockMapInv w.1) (y - w.2) := by
  have h := ((contDiff_blockMapInv w.1).differentiable (by simp) (y - w.2)).hasFDerivAt
  have h2 := (h.comp y ((hasFDerivAt_id y).sub_const w.2)).add_const w.2
  rw [show termInv w = fun y => (blockMapInv w.1 ∘ fun y => id y - w.2) y + w.2 from rfl,
    h2.fderiv]
  simp

lemma jac_termInv {L : ℕ} (w : BlockParam L) (y : Pt 2) :
    jac (termInv w) y = jac (blockMapInv w.1) (y - w.2) := by
  unfold jac; rw [fderiv_termInv]

variable {L M : ℕ} {S : ℕ → ℝ}

/-- `Ψ₀` is the inverse terminal flow map of `b_ω`. -/
theorem termInv_isInverseFlowMap (cf : ControlFamily L M S) (w : BlockParam L) :
    IsInverseFlowMap (bField cf w) 0 1 (termInv w) := by
  obtain ⟨Φ, ⟨hΦ0, hΦd⟩, hΦ1⟩ := cf.terminal w.1
  obtain ⟨hl, hr⟩ := blockMap_inverse w.1
  refine ⟨fun s x => Φ s (x - w.2) + w.2, fun x => by simp [hΦ0], fun s x => ?_, fun x => ?_⟩
  · have := (hΦd s (x - w.2)).add_const w.2
    simpa [bField] using this
  · simp only [termInv, hΦ1, add_sub_cancel_right]
    exact ⟨by rw [hl]; abel, by rw [hr]; abel⟩

/-- A uniform lower bound for `|D𝓕⁻¹(x)ᵀe|`, from the derivative bound of the block maps. -/
lemma blockMapInv_lower (L : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ (w1 : Fin L → Bool × Pt 2) (x e : Pt 2),
    euclNorm e = 1 → c ≤ euclNorm ((jac (blockMapInv w1) x)ᵀ *ᵥ e) := by
  obtain ⟨C, hC⟩ := blockMap_deriv_bounds L 1 le_rfl
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => (true, 0)) 0).1
  refine ⟨1 / (2 * (C + 1)), by positivity, fun w1 x e he => ?_⟩
  have h := jac_transpose_lower (blockMapInv w1) (blockMap w1)
    ((contDiff_blockMapInv w1).differentiable (by simp))
    ((contDiff_blockMap w1).differentiable (by simp)) (blockMap_inverse w1).2 (C + 1)
    (fun y => by rw [← norm_iteratedFDeriv_one]; linarith [(hC w1 y).1]) x e he
  rw [div_le_iff₀ (by positivity)]; linarith

lemma continuous_euclNorm_jac_blockMapInv (L : ℕ) (e : Pt 2) :
    Continuous fun p : (Fin L → Bool × Pt 2) × Pt 2 =>
      euclNorm ((jac (blockMapInv p.1) p.2)ᵀ *ᵥ e) := by
  have hc := continuous_jac_blockMapInv L
  have hij : ∀ i j, Continuous fun p : (Fin L → Bool × Pt 2) × Pt 2 =>
      jac (blockMapInv p.1) p.2 i j := fun i j => hc.matrix_elem i j
  unfold euclNorm
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
  fun_prop

/-- The negative moment bound for the inverse terminal flow map, averaged over the cell. -/
theorem termInv_neg_moment (q σ : ℝ) (hσ : 0 < σ) (L : ℕ) (h : NegMomentBound q σ L)
    (e : Pt 2) (he : euclNorm e = 1) :
    ∫⁻ w, (∫⁻ y in cell 2, ENNReal.ofReal (euclNorm ((jac (termInv w) y)ᵀ *ᵥ e) ^ (-σ)))
      ∂(blockMeasure L) ≤ ENNReal.ofReal (1 / (128 * q ^ σ)) := by
  obtain ⟨c, hc0, hc⟩ := blockMapInv_lower L
  set g : (Fin L → Bool × Pt 2) × Pt 2 → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (euclNorm ((jac (blockMapInv p.1) p.2)ᵀ *ᵥ e) ^ (-σ)) with hg
  have hcont := continuous_euclNorm_jac_blockMapInv L e
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (hcont.measurable.pow_const _)
  simp_rw [jac_termInv]
  change ∫⁻ w, (∫⁻ y in cell 2, g (w.1, y - w.2)) ∂(blockMeasure L) ≤ _
  set B := ENNReal.ofReal (1 / (128 * q ^ σ))
  have hpt : ∀ x, ∫⁻ w1, g (w1, x) ∂(Measure.pi fun _ : Fin L => stepMeasure) ≤ B := by
    intro x
    have hmx : Measurable fun w1 : Fin L → Bool × Pt 2 =>
        euclNorm ((jac (blockMapInv w1) x)ᵀ *ᵥ e) ^ (-σ) :=
      (hcont.comp (Continuous.prodMk_left x)).measurable.pow_const _
    have hint : Integrable (fun w1 => euclNorm ((jac (blockMapInv w1) x)ᵀ *ᵥ e) ^ (-σ))
        (Measure.pi fun _ : Fin L => stepMeasure) := by
      refine Integrable.of_bound hmx.aestronglyMeasurable (c ^ (-σ))
        (Eventually.of_forall fun w1 => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (euclNorm_nonneg _) _)]
      exact Real.rpow_le_rpow_of_nonpos hc0 (hc w1 x e he) (by linarith)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => Real.rpow_nonneg (euclNorm_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal ((block_map_negative q σ L h).2.1 x e he)
  have hG : Measurable fun p : BlockParam L × Pt 2 => g (p.1.1, p.2 - p.1.2) :=
    hgm.comp (by fun_prop)
  have hvol : volume (cell 2) = 1 := volume_cell_two
  unfold blockMeasure
  rw [lintegral_prod _ (hG.lintegral_prod_right' (ν := volume.restrict (cell 2))).aemeasurable]
  rw [lintegral_lintegral_swap (hG.lintegral_prod_right' (ν := volume.restrict (cell 2))).aemeasurable]
  calc ∫⁻ z, (∫⁻ w1, (∫⁻ y in cell 2, g (w1, y - z)) ∂(Measure.pi fun _ : Fin L => stepMeasure))
        ∂uniformTorus
      ≤ ∫⁻ z, B ∂uniformTorus := by
        refine lintegral_mono fun z => ?_
        have hz : Measurable fun p : (Fin L → Bool × Pt 2) × Pt 2 => g (p.1, p.2 - z) :=
          hgm.comp (by fun_prop)
        rw [lintegral_lintegral_swap hz.aemeasurable]
        calc ∫⁻ y in cell 2, ∫⁻ w1, g (w1, y - z) ∂(Measure.pi fun _ : Fin L => stepMeasure)
            ≤ ∫⁻ y in cell 2, B := lintegral_mono fun y => hpt (y - z)
          _ = B := by simp [hvol]
    _ = B := by simp [uniformTorus, hvol]

end AnomDiss
