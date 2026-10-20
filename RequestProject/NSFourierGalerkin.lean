module

public import RequestProject.FourierGalerkinSpace
public import RequestProject.NSFiniteGalerkinODE

/-!
# Global solutions of the actual Fourier Galerkin systems

The concrete finite Fourier spaces are equipped with the genuine `L²`
structure and the projected Navier--Stokes vector field. Each finite system
has a global solution on every prescribed finite time interval. No classical
Navier--Stokes or scalar existence statement occurs as a hypothesis.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- The actual Fourier field range as a finite solenoidal Hilbert model. -/
def fourierGalerkinModel (S : Finset (Fin 2 → ℤ)) : FiniteSolenoidalSpace where
  space := solenoidalFourierSpace S
  finiteDimensional := inferInstance
  regular := fun _ hv => contDiff_of_mem_solenoidalFourierSpace S hv
  periodic := fun _ hv => isPeriodic_of_mem_solenoidalFourierSpace S hv
  solenoidal := fun _ hv x => divergence_of_mem_solenoidalFourierSpace S hv x

@[simp] theorem fourierGalerkinModel_space (S : Finset (Fin 2 → ℤ)) :
    (fourierGalerkinModel S).space = solenoidalFourierSpace S := rfl

/-- The constructed trajectories are actual smooth periodic vector fields
and satisfy the true Fourier Galerkin weak equation at every time. -/
theorem exists_fourier_galerkin_curve (S : Finset (Fin 2 → ℤ)) {ν T : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T) (v₀ : Pt 2 → Pt 2)
    (hv₀ : v₀ ∈ solenoidalFourierSpace S) (f : ℝ → C(Pt 2, Pt 2))
    (hf : ContinuousOn (fun q : ℝ × Pt 2 => f q.1 q.2) (Icc 0 T ×ˢ univ)) :
    ∃ v V' : ℝ → Pt 2 → Pt 2,
      v 0 = v₀ ∧
      (∀ t, v t ∈ solenoidalFourierSpace S) ∧
      (∀ t, V' t ∈ solenoidalFourierSpace S) ∧
      (∀ t, ContDiff ℝ ∞ (v t) ∧ IsPeriodic (v t) ∧ ∀ x, divergence (v t) x = 0) ∧
      (∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun s => v s x) (V' t x) t) ∧
      ∀ t ∈ Icc 0 T, ∀ w ∈ solenoidalFourierSpace S,
        (∫ x in cell 2, dot (w x) (V' t x)) +
            (∫ x in cell 2, dot (w x) (conv (v t) (v t) x)) =
          ν * (∫ x in cell 2, dot (w x) (lap (v t) x)) +
            (∫ x in cell 2, dot (w x) (f t x)) := by
  let G := fourierGalerkinModel S
  let z₀ : G.State := ⟨v₀, hv₀⟩
  obtain ⟨u, hu0, hud, hweak⟩ := G.exists_ns_galerkin_state hν hT f hf z₀
  let z' : ℝ → G.State := fun t => G.nsField ν (u t) + G.projection (f t)
  refine ⟨fun t => G.eval (u t), fun t => G.eval (z' t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change G.eval (u 0) = v₀
    rw [hu0]
    rfl
  · intro t
    exact (u t).2
  · intro t
    exact (z' t).2
  · intro t
    exact ⟨G.eval_contDiff (u t), G.eval_periodic (u t), G.eval_solenoidal (u t)⟩
  · intro t ht x
    exact G.hasDerivAt_eval (hud t ht) x
  · intro t ht w hw
    exact hweak t ht (show G.State from ⟨w, hw⟩)

end AnomDiss
