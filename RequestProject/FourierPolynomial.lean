module

public import RequestProject.LerayFourier
public import RequestProject.HeatFourier

/-!
# Real solenoidal Fourier polynomials

This module constructs genuine smooth vector fields from finite coefficient
families.  The Leray multiplier makes every reconstructed field divergence
free.  The spatial differential identities will be used to define and test
finite Galerkin equations without assuming an exact Navier--Stokes solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- A real-valued vector Fourier mode. Taking real parts permits arbitrary
complex coefficients, without an additional reality assumption. -/
def realFourierMode (k : Fin 2 → ℤ) (a : FourierVelocity) (x : Pt 2) : Pt 2 :=
  fun i => (a i * expChar (intVec k) x).re

theorem contDiff_realFourierMode (k : Fin 2 → ℤ) (a : FourierVelocity) :
    ContDiff ℝ ∞ (realFourierMode k a) := by
  apply contDiff_pi.2
  intro i
  exact Complex.reCLM.contDiff.comp
    (contDiff_const.mul (contDiff_expChar (intVec k)))

theorem isPeriodic_realFourierMode (k : Fin 2 → ℤ) (a : FourierVelocity) :
    IsPeriodic (realFourierMode k a) := by
  intro x n
  funext i
  simp only [realFourierMode, isPeriodic_expChar k x n]

theorem pd_realFourierMode_component (k : Fin 2 → ℤ) (a : FourierVelocity)
    (j i : Fin 2) (x : Pt 2) :
    pd j (realFourierMode k a) x i =
      (a i * ((2 * π * Complex.I * (k j : ℂ)) * expChar (intVec k) x)).re := by
  rw [← pd_component _ x ((contDiff_realFourierMode k a).differentiable (by simp) x)]
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (a i))
  change pd j (fun y => L (expChar (intVec k) y)) x = _
  rw [pd_clm_fun L _ j ((contDiff_expChar _).differentiable (by simp))]
  dsimp only
  rw [pd_expChar]
  rfl

theorem divergence_realFourierMode (k : Fin 2 → ℤ) (a : FourierVelocity) (x : Pt 2) :
    divergence (realFourierMode k a) x =
      ((2 * π * Complex.I * expChar (intVec k) x) * fourierDivSymbol k a).re := by
  unfold divergence fourierDivSymbol
  simp only [pd_realFourierMode_component, Fin.sum_univ_two]
  rw [← Complex.add_re]
  congr 1
  ring

/-- The pressure-free coefficient projection reconstructs an actually
divergence-free spatial field, not merely a formally constrained coefficient. -/
theorem divergence_realFourierMode_leray (k : Fin 2 → ℤ) (a : FourierVelocity) (x : Pt 2) :
    divergence (realFourierMode k (fourierLeray k a)) x = 0 := by
  rw [divergence_realFourierMode, fourierLeray_div_free, mul_zero]
  rfl

/-- Reconstruction of a finite set of projected Fourier coefficients. -/
def solenoidalFourierPolynomial (S : Finset (Fin 2 → ℤ))
    (a : (Fin 2 → ℤ) → FourierVelocity) : Pt 2 → Pt 2 :=
  fun x => ∑ k ∈ S, realFourierMode k (fourierLeray k (a k)) x

theorem contDiff_solenoidalFourierPolynomial (S : Finset (Fin 2 → ℤ))
    (a : (Fin 2 → ℤ) → FourierVelocity) :
    ContDiff ℝ ∞ (solenoidalFourierPolynomial S a) := by
  exact ContDiff.sum fun k _ => contDiff_realFourierMode k _

theorem isPeriodic_solenoidalFourierPolynomial (S : Finset (Fin 2 → ℤ))
    (a : (Fin 2 → ℤ) → FourierVelocity) :
    IsPeriodic (solenoidalFourierPolynomial S a) := by
  intro x n
  apply Finset.sum_congr rfl
  intro k hk
  exact isPeriodic_realFourierMode k _ x n

lemma pd_finite_sum {ι : Type*} (S : Finset ι) (f : ι → Pt 2 → Pt 2)
    (hf : ∀ k ∈ S, Differentiable ℝ (f k)) (j : Fin 2) (x : Pt 2) :
    pd j (fun y => ∑ k ∈ S, f k y) x = ∑ k ∈ S, pd j (f k) x := by
  unfold pd
  rw [fderiv_fun_sum (fun k hk => hf k hk x)]
  simp

theorem divergence_solenoidalFourierPolynomial (S : Finset (Fin 2 → ℤ))
    (a : (Fin 2 → ℤ) → FourierVelocity) (x : Pt 2) :
    divergence (solenoidalFourierPolynomial S a) x = 0 := by
  unfold divergence solenoidalFourierPolynomial
  simp only [pd_finite_sum S (fun k => realFourierMode k (fourierLeray k (a k)))
    (fun k _ => (contDiff_realFourierMode k _).differentiable (by simp)),
    Finset.sum_apply]
  rw [Finset.sum_comm]
  have h : ∀ k ∈ S, ∑ i : Fin 2, pd i (realFourierMode k (fourierLeray k (a k))) x i = 0 := by
    intro k hk
    exact divergence_realFourierMode_leray k (a k) x
  exact Finset.sum_eq_zero h

end AnomDiss
