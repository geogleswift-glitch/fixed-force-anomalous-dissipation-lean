module

public import RequestProject.H2Dens

/-!
# The heat operator does not increase the `H²` norm

For `C²` quasi-periodic `f`, `h2Dens (H_v f) ≤ H_v (h2Dens f)` pointwise (Jensen), hence
`∫_{𝕋²} h2Dens (H_v f) ≤ ∫_{𝕋²} h2Dens f`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {ξ : Pt 2}

instance (v : ℝ≥0) : IsProbabilityMeasure (gauss2 v) := by
  unfold gauss2; infer_instance

/-- Jensen's inequality `‖𝔼 u‖² ≤ 𝔼 ‖u‖²` for bounded continuous `u`. -/
lemma norm_integral_sq_le {P : Measure (Pt 2)} [IsProbabilityMeasure P] {u : Pt 2 → ℂ}
    (hu : Continuous u) {C : ℝ} (hC : ∀ y, ‖u y‖ ≤ C) :
    ‖∫ ζ, u ζ ∂P‖ ^ 2 ≤ ∫ ζ, ‖u ζ‖ ^ 2 ∂P := by
  have hm : MemLp (fun ζ => ‖u ζ‖) 2 P :=
    MemLp.of_bound hu.norm.aestronglyMeasurable C (Eventually.of_forall fun y => by
      rw [norm_norm]; exact hC y)
  have h1 := variance_nonneg (fun ζ => ‖u ζ‖) P
  rw [variance_eq_sub hm] at h1
  simp only [Pi.pow_apply] at h1
  have h2 := norm_integral_le_integral_norm (μ := P) u
  have h3 : 0 ≤ ‖∫ ζ, u ζ ∂P‖ := norm_nonneg _
  nlinarith

lemma sq_norm_heatOp_le {u : Pt 2 → ℂ} (hu : Continuous u) {C : ℝ} (hC : ∀ y, ‖u y‖ ≤ C)
    (v : ℝ≥0) (x : Pt 2) : ‖heatOp v u x‖ ^ 2 ≤ ∫ ζ, ‖u (x + ζ)‖ ^ 2 ∂(gauss2 v) :=
  norm_integral_sq_le (hu.comp (continuous_const.add continuous_id)) (fun _ => hC _)

lemma integrable_sq_norm_translate {u : Pt 2 → ℂ} (hu : Continuous u) {C : ℝ}
    (hC : ∀ y, ‖u y‖ ≤ C) (v : ℝ≥0) (x : Pt 2) :
    Integrable (fun ζ => ‖u (x + ζ)‖ ^ 2) (gauss2 v) :=
  Integrable.of_bound ((hu.comp (continuous_const.add continuous_id)).norm.pow 2).aestronglyMeasurable
    (C ^ 2) (Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2)

theorem h2Dens_heatOp_le {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f) (v : ℝ≥0)
    (x : Pt 2) : h2Dens (heatOp v f) x ≤ ∫ ζ, h2Dens f (x + ζ) ∂(gauss2 v) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  obtain ⟨C0, hC0⟩ := hqp.bdd hf.continuous
  have hc1 : ∀ i, Continuous (pd i f) := fun i => continuous_pd_of_C1 _ h1 i
  have hc2 : ∀ i j, Continuous (pd i (pd j f)) := fun i j =>
    continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf j) i
  have hb1 : ∀ i, ∃ C, ∀ y, ‖pd i f y‖ ≤ C := fun i => (hqp.pd hd i).bdd (hc1 i)
  have hb2 : ∀ i j, ∃ C, ∀ y, ‖pd i (pd j f) y‖ ≤ C := fun i j =>
    (isQP_pd2 hqp hf i j).bdd (hc2 i j)
  choose C1 hC1 using hb1
  choose C2 hC2 using hb2
  have I0 := integrable_sq_norm_translate hf.continuous hC0 v x
  have I1 := fun i => integrable_sq_norm_translate (hc1 i) (hC1 i) v x
  have I2 := fun i j => integrable_sq_norm_translate (hc2 i j) (hC2 i j) v x
  have e : (fun ζ => h2Dens f (x + ζ)) = fun ζ => ‖f (x + ζ)‖ ^ 2 +
      ∑ i, ‖pd i f (x + ζ)‖ ^ 2 + ∑ i, ∑ j, ‖pd i (pd j f) (x + ζ)‖ ^ 2 := rfl
  have J1 : Integrable (fun ζ => ∑ i, ‖pd i f (x + ζ)‖ ^ 2) (gauss2 v) :=
    integrable_finset_sum _ fun i _ => I1 i
  have J2 : Integrable (fun ζ => ∑ i, ∑ j, ‖pd i (pd j f) (x + ζ)‖ ^ 2) (gauss2 v) :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => I2 i j
  have J01 : Integrable (fun ζ => ‖f (x + ζ)‖ ^ 2 + ∑ i, ‖pd i f (x + ζ)‖ ^ 2) (gauss2 v) :=
    I0.add J1
  rw [e, integral_add J01 J2, integral_add I0 J1, integral_finset_sum _ fun i _ => I1 i,
    integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => I2 i j]
  simp_rw [integral_finset_sum _ fun j _ => I2 _ j]
  unfold h2Dens
  gcongr with i _ i _ j _
  · exact sq_norm_heatOp_le hf.continuous hC0 v x
  · rw [pd_heatOp_C1 hqp h1]
    exact sq_norm_heatOp_le (hc1 i) (hC1 i) v x
  · rw [pd2_heatOp hqp hf]
    exact sq_norm_heatOp_le (hc2 i j) (hC2 i j) v x

theorem integral_h2Dens_heatOp_le {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hf : ContDiff ℝ 2 f)
    (v : ℝ≥0) : ∫ x in cell 2, h2Dens (heatOp v f) x ≤ ∫ x in cell 2, h2Dens f x := by
  have hHq := heatOp_isQP hqp v
  have hHc := contDiff_heatOp hqp hf v
  calc ∫ x in cell 2, h2Dens (heatOp v f) x
      ≤ ∫ x in cell 2, ∫ ζ, (1 : ℝ) * h2Dens f (x + ζ) ∂(gauss2 v) := by
        refine setIntegral_mono (integrableOn_cell_of_continuous (continuous_h2Dens hHc)) ?_
          fun x => by simpa using h2Dens_heatOp_le hqp hf v x
        obtain ⟨C, hC⟩ := bdd_h2Dens hqp hf
        refine integrableOn_cell_of_continuous ?_
        simp only [one_mul]
        exact continuous_gavg (continuous_h2Dens hf) (fun y => by
          rw [Real.norm_of_nonneg (h2Dens_nonneg _ _)]; exact hC y) v
    _ = (∫ ζ, (1 : ℝ) ∂(gauss2 v)) * ∫ x in cell 2, h2Dens f x :=
        integral_cell_integral_translate (integrable_const _) (continuous_h2Dens hf)
          (periodic_h2Dens hqp hf)
    _ = ∫ x in cell 2, h2Dens f x := by simp

end AnomDiss
