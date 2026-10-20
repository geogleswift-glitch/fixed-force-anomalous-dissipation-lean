module

public import RequestProject.ScalarHeatSmoothing
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The actual Gaussian heat semigroup

Independent Gaussian increments add their variances. This is proved for the
two-dimensional product laws themselves and then applied to Bochner integrals.
The semigroup identity holds for continuous bounded inputs, including the
continuous periodic inputs used by the scalar mild construction.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem gauss2_add_map (v w : ℝ≥0) :
    ((gauss2 v).prod (gauss2 w)).map (fun p : Pt 2 × Pt 2 => p.1 + p.2) =
      gauss2 (v + w) := by
  have hp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 2)
    (fun _ => gaussianReal 0 v) (fun _ => gaussianReal 0 w)
  change ((Measure.pi fun _ : Fin 2 => gaussianReal 0 v).prod
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 w)).map _ = _
  rw [← hp.map_eq, Measure.map_map (by fun_prop) hp.measurable]
  change (Measure.pi fun _ : Fin 2 => (gaussianReal 0 v).prod (gaussianReal 0 w)).map
    (fun p i => (p i).1 + (p i).2) = _
  rw [Measure.pi_map_pi (fun _ => (by fun_prop :
    AEMeasurable (fun p : ℝ × ℝ => p.1 + p.2)
      ((gaussianReal 0 v).prod (gaussianReal 0 w))))]
  unfold gauss2
  congr 1
  funext i
  change (gaussianReal 0 v) ∗ (gaussianReal 0 w) = _
  rw [gaussianReal_conv_gaussianReal, zero_add]

/-- The genuine heat averages compose by adding Gaussian variances. -/
theorem heatOp_semigroup {f : Pt 2 → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (v w : ℝ≥0) (x : Pt 2) :
    heatOp (v + w) f x = heatOp v (heatOp w f) x := by
  have hi : Integrable (fun p : Pt 2 × Pt 2 => f (x + (p.1 + p.2)))
      ((gauss2 v).prod (gauss2 w)) :=
    Integrable.of_bound (hf.comp (continuous_const.add
      (continuous_fst.add continuous_snd))).aestronglyMeasurable C
      (Eventually.of_forall fun p => hC _)
  unfold heatOp
  rw [← gauss2_add_map v w]
  rw [integral_map (f := fun ζ : Pt 2 => f (x + ζ)) (by fun_prop)
    (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable]
  rw [integral_prod _ hi]
  congr 1
  funext ζ
  congr 1
  funext η
  rw [add_assoc]

theorem heatOp_semigroup_periodic {f : Pt 2 → ℂ} (hf : Continuous f)
    (hp : IsPeriodic f) (v w : ℝ≥0) (x : Pt 2) :
    heatOp (v + w) f x = heatOp v (heatOp w f) x := by
  obtain ⟨C, hC⟩ := (isQP_zero_iff.2 hp).bdd hf
  exact heatOp_semigroup hf hC v w x

end AnomDiss
