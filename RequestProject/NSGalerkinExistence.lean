module

public import RequestProject.NSFiniteGalerkinODE
public import RequestProject.NSGalerkinCurve

/-!
# Existence of finite Galerkin solutions with uniform spatial estimates

The solution is obtained from the actual globally dissipative finite ODE.
The estimates use the original force and remain independent of the dimension
of the subspace. Passing to a limit and establishing classical regularity are
subsequent steps, not assumptions or conclusions of this module.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss.FiniteSolenoidalSpace

variable (G : FiniteSolenoidalSpace)

set_option maxHeartbeats 800000

/-- Every Laplacian-invariant finite solenoidal space has an actual Galerkin
solution with energy, enstrophy and integrated second-derivative bounds. -/
theorem exists_ns_galerkin_bounds {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hlap : ∀ v : G.State, lap (G.eval v) ∈ G.space)
    (f : ℝ → C(Pt 2, Pt 2))
    (hf : ContinuousOn (fun q : ℝ × Pt 2 => f q.1 q.2) (Icc 0 T ×ˢ univ))
    (v₀ : G.State) :
    ∃ u : ℝ → G.State, u 0 = v₀ ∧
      (∀ t ∈ Icc 0 T, HasDerivAt u (G.nsField ν (u t) + G.projection (f t)) t) ∧
      (∀ t ∈ Icc 0 T, ∀ w : G.State,
        cellVectorPair (G.eval w) (G.eval (G.nsField ν (u t) + G.projection (f t))) +
            cellVectorPair (G.eval w) (conv (G.eval (u t)) (G.eval (u t))) =
          ν * cellVectorPair (G.eval w) (lap (G.eval (u t))) +
            cellVectorPair (G.eval w) (f t)) ∧
      (∀ t ∈ Icc 0 T, l2sqV (G.eval (u t)) ≤
        (l2sqV (G.eval v₀) + ∫ s in (0 : ℝ)..T, l2sqV (f s)) * exp T) ∧
      (∀ t ∈ Icc 0 T,
        (∫ x in cell 2, gradSqV (G.eval (u t)) x) +
            ν * (∫ s in (0 : ℝ)..t, l2sqV (lap (G.eval (u s)))) ≤
          (∫ x in cell 2, gradSqV (G.eval v₀) x) +
            (1 / ν) * (∫ s in (0 : ℝ)..t, l2sqV (f s))) ∧
      (∀ t ∈ Icc 0 T,
        (∫ x in cell 2, gradSqV (G.eval (u t)) x) ≤
          (∫ x in cell 2, gradSqV (G.eval v₀) x) +
            (1 / ν) * (∫ s in (0 : ℝ)..T, l2sqV (f s))) ∧
      ν * (∫ s in (0 : ℝ)..T, l2sqV (lap (G.eval (u s)))) ≤
        (∫ x in cell 2, gradSqV (G.eval v₀) x) +
          (1 / ν) * (∫ s in (0 : ℝ)..T, l2sqV (f s)) := by
  obtain ⟨u, hu0, hud, hweak⟩ := G.exists_ns_galerkin_state hν.le hT f hf v₀
  let u' : ℝ → G.State := fun t => G.nsField ν (u t) + G.projection (f t)
  have hu : ContinuousOn u (Icc 0 T) := fun t ht =>
    (hud t ht).continuousAt.continuousWithinAt
  have hu' : ContinuousOn u' (Icc 0 T) :=
    (((G.contDiff_nsField ν).continuous.comp_continuousOn hu).add
      (G.continuousOn_projected_force f hT hf))
  have htests := fun t (ht : t ∈ Ioo 0 T) =>
    G.curve_tests ν (u t) (u' t) (f t) hlap (hweak t (Ioo_subset_Icc_self ht))
  have henergy := G.curve_energy_bound hT hν u u' (fun t x => f t x)
    hu hu' hf (fun t ht => hud t (Ioo_subset_Icc_self ht)) (fun t ht => (htests t ht).1)
  have henstrophy := G.curve_enstrophy_bound hT hν u u' (fun t x => f t x)
    hu hu' hf (fun t ht => hud t (Ioo_subset_Icc_self ht)) (fun t ht => (htests t ht).2)
  simp only [hu0, sub_zero] at henergy henstrophy
  exact ⟨u, hu0, hud, hweak, henergy, henstrophy.1, henstrophy.2.1, henstrophy.2.2⟩

end AnomDiss.FiniteSolenoidalSpace
