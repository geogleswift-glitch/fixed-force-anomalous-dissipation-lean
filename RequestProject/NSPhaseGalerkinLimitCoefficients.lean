module

public import RequestProject.NSPhaseGalerkinCompactness
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Mathematical invariants of the actual Galerkin coefficient limit

The limit retains zero initial data, the true Fourier divergence relation and
the reality symmetry. Its squared `L²` and `H¹` Fourier energies are summable
and satisfy the same uniform bounds as the actual finite-dimensional solutions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction ComplexConjugate

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

/-- Real-valued fields have the genuine complex Fourier reality symmetry. -/
theorem vectorFourierCoeff_conj_symmetry (v : Pt 2 → Pt 2) (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff v (-k) i = conj (vectorFourierCoeff v k i) := by
  simp only [vectorFourierCoeff_apply, fc, intVec_neg, neg_neg]
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  dsimp only
  rw [expChar_neg_eq_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]

variable {ν : ℝ} {hν : 0 < ν} {phase : Phase}
  {a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ)} {φ : ℕ → ℕ}

/-- Sup-topology convergence of the coefficient curves implies convergence
of their actual Fourier values at every time in the original interval. -/
theorem phaseGalerkin_limit_coefficient_pointwise
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    Tendsto (fun n => vectorFourierCoeff (phaseGalerkinVelocity ν hν phase (φ n) t.1) k i)
      atTop (𝓝 (a (k, i) t)) := by
  simpa only [Function.comp_def, phaseGalerkinCoefficientCurve_apply] using
    ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto (a (k, i))).comp
      (hlim (k, i))

/-- The extracted coefficient limit has the original zero initial value. -/
theorem phaseGalerkin_limit_coefficient_initial
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (k : Fin 2 → ℤ) (i : Fin 2) :
    a (k, i) ⟨0, by norm_num⟩ = 0 := by
  have h := phaseGalerkin_limit_coefficient_pointwise hlim ⟨0, by norm_num⟩ k i
  simp only [phaseGalerkinVelocity_initial, vectorFourierCoeff_apply, fc,
    Pi.zero_apply, Complex.ofReal_zero, zero_mul, integral_zero] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Fourier incompressibility is preserved by the actual coefficient limit. -/
theorem phaseGalerkin_limit_coefficient_solenoidal
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) (k : Fin 2 → ℤ) :
    ∑ i : Fin 2, (k i : ℂ) * a (k, i) t = 0 := by
  have h := tendsto_finset_sum (Finset.univ : Finset (Fin 2)) (fun i _ =>
    (phaseGalerkin_limit_coefficient_pointwise hlim t k i).const_mul (k i : ℂ))
  have heq : (fun n => ∑ i : Fin 2, (k i : ℂ) *
      vectorFourierCoeff (phaseGalerkinVelocity ν hν phase (φ n) t.1) k i) =
      fun _ : ℕ => (0 : ℂ) := by
    funext n
    exact vectorFourierCoeff_solenoidal (phaseGalerkinVelocity ν hν phase (φ n) t.1)
      ((phaseGalerkinVelocity_contDiff ν hν phase (φ n) t.1).of_le (natCast_le_infty 1))
      (phaseGalerkinVelocity_periodic ν hν phase (φ n) t.1)
      (phaseGalerkinVelocity_solenoidal ν hν phase (φ n) t.1) k
  rw [heq] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The same subsequence preserves the reality symmetry at all frequencies. -/
theorem phaseGalerkin_limit_coefficient_reality
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    a (-k, i) t = conj (a (k, i) t) := by
  have hk := phaseGalerkin_limit_coefficient_pointwise hlim t k i
  have hm := phaseGalerkin_limit_coefficient_pointwise hlim t (-k) i
  have hc : Tendsto
      (fun n => conj (vectorFourierCoeff (phaseGalerkinVelocity ν hν phase (φ n) t.1) k i))
      atTop (𝓝 (conj (a (k, i) t))) :=
    ((by fun_prop : Continuous (fun z : ℂ => conj z)).tendsto _).comp hk
  simp only [← vectorFourierCoeff_conj_symmetry] at hc
  exact tendsto_nhds_unique hm hc

/-- The limit's actual scalar Fourier energy at a fixed frequency. -/
def phaseLimitCoefficientEnergy (a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ))
    (t : GalerkinTime) (k : Fin 2 → ℤ) : ℝ := ∑ i, ‖a (k, i) t‖ ^ 2

theorem phaseLimitCoefficientEnergy_nonneg
    (a : GalerkinCoefficientIndex → (GalerkinTime →ᵇ ℂ)) (t : GalerkinTime) (k : Fin 2 → ℤ) :
    0 ≤ phaseLimitCoefficientEnergy a t k := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Finite Fourier blocks of the limit retain the uniform actual kinetic
energy bound. -/
theorem phaseGalerkin_limit_finite_energy
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) (S : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ S, phaseLimitCoefficientEnergy a t k ≤ phaseGalerkinEnergyBound phase := by
  have h := tendsto_finset_sum S (fun k _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin 2)) (fun i _ =>
      (phaseGalerkin_limit_coefficient_pointwise hlim t k i).norm.pow 2))
  apply le_of_tendsto h
  apply Eventually.of_forall
  intro n
  let v := phaseGalerkinVelocity ν hν phase (φ n) t.1
  have hs := parseval_vector_cell v
    (phaseGalerkinVelocity_contDiff ν hν phase (φ n) t.1).continuous
    (phaseGalerkinVelocity_periodic ν hν phase (φ n) t.1)
  have hb := hs.summable.sum_le_tsum S (fun k _ => vectorFourierEnergy_nonneg v k)
  simp only [vectorFourierEnergy] at hb
  rw [hs.tsum_eq] at hb
  exact hb.trans (phaseGalerkinVelocity_energy_bound ν hν phase (φ n) t.2)

/-- The coefficient limit has a genuine summable `L²` Fourier energy. -/
theorem phaseGalerkin_limit_energy_summable
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) :
    Summable (phaseLimitCoefficientEnergy a t) :=
  summable_of_sum_le (fun k => phaseLimitCoefficientEnergy_nonneg a t k)
    (phaseGalerkin_limit_finite_energy hlim t)

/-- The whole summable kinetic Fourier energy satisfies the proven bound. -/
theorem phaseGalerkin_limit_energy_bound
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) :
    ∑' k, phaseLimitCoefficientEnergy a t k ≤ phaseGalerkinEnergyBound phase :=
  Real.tsum_le_of_sum_le (fun k => phaseLimitCoefficientEnergy_nonneg a t k)
    (phaseGalerkin_limit_finite_energy hlim t)

/-- Finite Fourier `H¹` energy bounds pass to the genuine coefficient limit. -/
theorem phaseGalerkin_limit_finite_gradient_energy
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) (S : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ S, fourierEigenvalue k * phaseLimitCoefficientEnergy a t k ≤
      phaseGalerkinGradientBound ν phase := by
  have h := tendsto_finset_sum S (fun k _ =>
    (tendsto_finset_sum (Finset.univ : Finset (Fin 2)) (fun i _ =>
      (phaseGalerkin_limit_coefficient_pointwise hlim t k i).norm.pow 2)).const_mul
        (fourierEigenvalue k))
  apply le_of_tendsto h
  apply Eventually.of_forall
  intro n
  let v := phaseGalerkinVelocity ν hν phase (φ n) t.1
  have hs := parseval_gradient_cell v
    ((phaseGalerkinVelocity_contDiff ν hν phase (φ n) t.1).of_le (natCast_le_infty 2))
    (phaseGalerkinVelocity_periodic ν hν phase (φ n) t.1)
  have hb := hs.summable.sum_le_tsum S (fun k _ => mul_nonneg
    (fourierEigenvalue_nonneg k) (vectorFourierEnergy_nonneg v k))
  rw [hs.tsum_eq] at hb
  exact hb.trans (phaseGalerkinVelocity_gradient_bound ν hν phase (φ n) t.2)

/-- The coefficient limit has genuinely summable squared-gradient Fourier
energy, inherited from the actual Galerkin enstrophy estimate. -/
theorem phaseGalerkin_limit_gradient_energy_summable
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) :
    Summable (fun k => fourierEigenvalue k * phaseLimitCoefficientEnergy a t k) :=
  summable_of_sum_le (fun k => mul_nonneg (fourierEigenvalue_nonneg k)
    (phaseLimitCoefficientEnergy_nonneg a t k))
      (phaseGalerkin_limit_finite_gradient_energy hlim t)

theorem phaseGalerkin_limit_gradient_energy_bound
    (hlim : ∀ m, Tendsto (fun n => phaseGalerkinCoefficientCurve ν hν phase (φ n) m)
      atTop (𝓝 (a m))) (t : GalerkinTime) :
    ∑' k, fourierEigenvalue k * phaseLimitCoefficientEnergy a t k ≤
      phaseGalerkinGradientBound ν phase :=
  Real.tsum_le_of_sum_le (fun k => mul_nonneg (fourierEigenvalue_nonneg k)
    (phaseLimitCoefficientEnergy_nonneg a t k))
      (phaseGalerkin_limit_finite_gradient_energy hlim t)

end AnomDiss
