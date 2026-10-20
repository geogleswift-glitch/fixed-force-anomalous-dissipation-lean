module

public import RequestProject.FourierCoefficientCompactnessBridge
public import RequestProject.NSPhaseGalerkinCompactness

/-!
# Strong spatial L² compactness of the actual Galerkin sequence

The same coefficient subsequence obtained by countable Arzelà--Ascoli is
uniformly `L²` Cauchy on the original unit time interval. This is a statement
about genuine spatial fields, using their proved gradient-controlled tails.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- One actual increasing Galerkin subsequence has both uniform coefficient
convergence and uniform-in-time Cauchyness in the true spatial `L²` norm. -/
theorem exists_phaseGalerkin_uniform_l2_cauchy_subsequence
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) :
    ∃ a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀ k i ε, 0 < ε → ∀ᶠ n in atTop, ∀ (t : ℝ) (ht : t ∈ Icc 0 1),
        ‖vectorFourierCoeff (phaseGalerkinVelocity ν hν phase (φ n) t) k i -
          a (k, i) ⟨t, ht⟩‖ < ε) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ m, N ≤ m → ∀ t ∈ Icc 0 1,
        l2sqV (phaseGalerkinVelocity ν hν phase (φ n) t -
          phaseGalerkinVelocity ν hν phase (φ m) t) < ε := by
  obtain ⟨a, φ, hφ, hconv⟩ := exists_phaseGalerkin_uniform_coefficient_subsequence ν hν phase
  refine ⟨a, φ, hφ, hconv, ?_⟩
  apply uniform_l2_cauchy_of_fourier_tails_and_coefficients
    (fun n => phaseGalerkinVelocity ν hν phase (φ n))
    (fun n t => (phaseGalerkinVelocity_contDiff ν hν phase (φ n) t).continuous)
    ?_ (fun k i t => a (k, i) t) ?_
  · intro ε hε
    obtain ⟨K, hK⟩ := phaseGalerkinVelocity_uniform_fourier_tail ν hν phase hε
    exact ⟨fourierFrequencyBox (K + 1), fun n t ht => hK (φ n) t ht⟩
  · intro k i ε hε
    filter_upwards [hconv k i ε hε] with n hn
    intro t
    exact hn t.1 t.2

end AnomDiss
