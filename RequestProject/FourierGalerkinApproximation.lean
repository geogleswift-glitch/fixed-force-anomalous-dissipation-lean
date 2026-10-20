module

public import RequestProject.FourierGalerkinDensity

/-!
# Actual solenoidal Fourier approximation in the torus L² norm

Parseval supplies a vanishing spectral tail. Taking real parts cannot increase
the squared error, so the range spaces approximate every C¹ periodic
solenoidal field in its genuine torus norm.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

def realFourierTruncation (S : Finset (Fin 2 → ℤ)) (v : Pt 2 → Pt 2) : Pt 2 → Pt 2 :=
  fun x i => (∑ k ∈ S, fc (fun y => (v y i : ℂ)) k * expChar (intVec k) x).re

lemma continuous_realFourierTruncation (S : Finset (Fin 2 → ℤ)) (v : Pt 2 → Pt 2) :
    Continuous (realFourierTruncation S v) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_re.comp (continuous_finset_sum _ fun k _ =>
    continuous_const.mul (continuous_expChar _))

lemma l2sqV_eq_sum_component (v : Pt 2 → Pt 2) (hv : Continuous v) :
    l2sqV v = ∑ i, l2sq (fun x => v x i) := by
  unfold l2sqV l2sq
  exact integral_finset_sum _ fun i _ =>
    integrableOn_cell_of_continuous (((continuous_apply i).comp hv).pow 2)

theorem realFourierTruncation_l2_error (S : Finset (Fin 2 → ℤ))
    (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) :
    l2sqV (v - realFourierTruncation S v) ≤
      l2sqV v - ∑ k ∈ S, ∑ i, ‖vectorFourierCoeff v k i‖ ^ 2 := by
  have hc : ∀ i : Fin 2, Continuous (fun x => v x i) :=
    fun i => (continuous_apply i).comp hv
  have hC : ∀ i : Fin 2, Continuous (fun x => (v x i : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (hc i)
  have hS : ∀ i : Fin 2, Continuous (fun x =>
      ∑ k ∈ S, fc (fun y => (v y i : ℂ)) k * expChar (intVec k) x) := fun i =>
    continuous_finset_sum _ fun k _ => continuous_const.mul (continuous_expChar _)
  have hcomponent : ∀ i : Fin 2,
      l2sq (fun x => (v - realFourierTruncation S v) x i) ≤
        l2sq (fun x => v x i) - ∑ k ∈ S, ‖vectorFourierCoeff v k i‖ ^ 2 := by
    intro i
    have hreal : Continuous (fun x => (v - realFourierTruncation S v) x i) :=
      (continuous_apply i).comp (hv.sub (continuous_realFourierTruncation S v))
    calc
      l2sq (fun x => (v - realFourierTruncation S v) x i)
          ≤ ∫ x in cell 2,
            ‖(v x i : ℂ) - ∑ k ∈ S, fc (fun y => (v y i : ℂ)) k * expChar (intVec k) x‖ ^ 2 := by
        apply setIntegral_mono_on (integrableOn_cell_of_continuous (hreal.pow 2))
          (integrableOn_cell_of_continuous (((hC i).sub (hS i)).norm.pow 2)) measurableSet_Icc
        intro x hx
        have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
          (Complex.abs_re_le_norm ((v x i : ℂ) -
            ∑ k ∈ S, fc (fun y => (v y i : ℂ)) k * expChar (intVec k) x))
        simpa only [Pi.pow_apply, sq_abs, Complex.sub_re, Complex.ofReal_re,
          Pi.sub_apply, realFourierTruncation] using hsq
      _ = l2sq (fun x => v x i) - ∑ k ∈ S, ‖vectorFourierCoeff v k i‖ ^ 2 := by
        rw [bessel_truncation _ (hC i) (fun x n => by simp only [hp x n])]
        simp only [vectorFourierCoeff_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs, l2sq]
  rw [l2sqV_eq_sum_component (v - realFourierTruncation S v)
    (hv.sub (continuous_realFourierTruncation S v)),
    l2sqV_eq_sum_component v hv]
  calc
    (∑ i, l2sq (fun x => (v - realFourierTruncation S v) x i))
        ≤ ∑ i, (l2sq (fun x => v x i) - ∑ k ∈ S, ‖vectorFourierCoeff v k i‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hcomponent i
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_comm]

theorem solenoidalFourierPolynomial_eq_realTruncation (S : Finset (Fin 2 → ℤ))
    (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v) (hp : IsPeriodic v)
    (hdiv : ∀ x, divergence v x = 0) :
    solenoidalFourierPolynomial S (vectorFourierCoeff v) = realFourierTruncation S v := by
  funext x i
  simp only [solenoidalFourierPolynomial, fourierLeray_vectorFourierCoeff v hv hp hdiv,
    Finset.sum_apply, realFourierMode, vectorFourierCoeff_apply, realFourierTruncation]
  simpa only [Complex.coe_reAddGroupHom] using
    (map_sum Complex.reAddGroupHom
      (fun k => fc (fun y => (v y i : ℂ)) k * expChar (intVec k) x) S).symm

theorem parseval_vector_cell (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) :
    HasSum (fun k => ∑ i, ‖vectorFourierCoeff v k i‖ ^ 2) (l2sqV v) := by
  rw [l2sqV_eq_sum_component v hv]
  exact hasSum_sum fun i _ => parseval_cell _ ((continuous_apply i).comp hv)
    (fun x n => by simp only [hp x n])

/-- Every smooth periodic solenoidal velocity is approximated by elements of
the actual finite Galerkin state spaces, with arbitrarily small squared L² error. -/
theorem exists_solenoidalFourier_approximation (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset (Fin 2 → ℤ)) (w : Pt 2 → Pt 2),
      w ∈ solenoidalFourierSpace S ∧ l2sqV (v - w) < ε := by
  have hs := parseval_vector_cell v hv.continuous hp
  have hl : Tendsto (fun S : Finset (Fin 2 → ℤ) =>
      ∑ k ∈ S, ∑ i, ‖vectorFourierCoeff v k i‖ ^ 2) atTop (𝓝 (l2sqV v)) := hs
  have htail : Tendsto (fun S : Finset (Fin 2 → ℤ) =>
      l2sqV v - ∑ k ∈ S, ∑ i, ‖vectorFourierCoeff v k i‖ ^ 2) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : Finset (Fin 2 → ℤ) => l2sqV v) atTop (𝓝 (l2sqV v)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hl
  obtain ⟨S, hS⟩ := (htail.eventually (Iio_mem_nhds hε)).exists
  refine ⟨S, solenoidalFourierPolynomial S (vectorFourierCoeff v),
    fourierCoeff_polynomial_mem S v, ?_⟩
  rw [solenoidalFourierPolynomial_eq_realTruncation S v hv hp hdiv]
  exact (realFourierTruncation_l2_error S v hv.continuous hp).trans_lt hS

end AnomDiss
