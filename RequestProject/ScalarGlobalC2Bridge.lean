module

public import RequestProject.HeatDuhamelFluxC2
public import RequestProject.ScalarGlobalMild

/-! A bundled spatial `C²` bridge for a scalar fixed point.

The hypotheses are exactly the source assumptions needed by
`contDiff_two_duhamelComponent_of_flux_derivative_holder`; this theorem is
useful independently of the external scalar existence interface.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

theorem scalar_mild_fixedPoint_contDiff_two_of_flux_derivative_holder
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hβ : 0 < β)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u)
    (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ)) (hfper : IsPeriodic f)
    (hflux : ∀ i : Fin 2,
      let G := extendSlabScalar hT (b i * u)
      Continuous (Function.uncurry (fun s x => pd i (G s) x)) ∧
      (∀ s, ContDiff ℝ 1 (G s)) ∧
      (∀ s, IsPeriodic (G s)) ∧
      (∃ C, ∀ s x, ‖pd i (G s) x‖ ≤ C) ∧
      (∃ H, 0 ≤ H ∧ ∀ s x y,
        ‖pd i (G s) x - pd i (G s) y‖ ≤ H * ‖x - y‖ ^ β)) :
    ∀ t : Icc (0 : ℝ) T, ContDiff ℝ 2 (fun x => u (t, x)) := by
  intro t
  have hD : ∀ i : Fin 2,
      ContDiff ℝ 2 (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) := by
    intro i
    obtain ⟨hF, hFs, hp, ⟨C, hC⟩, ⟨H, hH, hholder⟩⟩ := hflux i
    exact contDiff_two_duhamelComponent_of_flux_derivative_holder hν i hF hFs hp hC hH
      hβ (hholder) t.property.1
  have hheat : ContDiff ℝ 2
      (heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f) := by
    rcases eq_or_lt_of_le t.property.1 with ht | ht
    · have he : heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f = f := by
        rw [← ht]
        simp only [mul_zero, Real.toNNReal_zero]
        funext x
        exact heatOp_zero f.continuous x
      rw [he]
      exact hfc
    · have hv : 0 < (Real.toNNReal (2 * ν * (t : ℝ)) : ℝ) := by
        rw [Real.coe_toNNReal _ (by positivity)]
        positivity
      exact contDiff_two_heatOp_continuous_periodic f.continuous hfper hv
  have he : (fun x => u (t, x)) = fun x =>
      heatOp (Real.toNNReal (2 * ν * (t : ℝ))) f x -
        ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hT (b i * u)) i t x := by
    funext x
    have hh := congrArg (fun w : SlabScalar T => w (t, x)) hu
    simpa [scalarMildMap] using hh.symm
  rw [he]
  exact hheat.sub (ContDiff.sum fun i _ => hD i)

end AnomDiss
