module

public import RequestProject.FourierDifferential

/-!
# Finite-dimensional spaces of actual solenoidal Fourier fields

The state space is the range of a real linear reconstruction map. Thus two
coefficient families representing the same spatial field are the same state;
no nondegeneracy assumption on a redundant coefficient table is needed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- Extend a finite coefficient table by zero. -/
def fourierCoefficientExtension (S : Finset (Fin 2 → ℤ))
    (a : (k : S) → FourierVelocity) (k : Fin 2 → ℤ) : FourierVelocity :=
  if hk : k ∈ S then a ⟨k, hk⟩ else 0

@[simp] lemma fourierCoefficientExtension_mem (S : Finset (Fin 2 → ℤ))
    (a : (k : S) → FourierVelocity) (k : Fin 2 → ℤ) (hk : k ∈ S) :
    fourierCoefficientExtension S a k = a ⟨k, hk⟩ := by
  simp [fourierCoefficientExtension, hk]

lemma fourierCoefficientExtension_add (S : Finset (Fin 2 → ℤ))
    (a b : (k : S) → FourierVelocity) :
    fourierCoefficientExtension S (a + b) =
      fourierCoefficientExtension S a + fourierCoefficientExtension S b := by
  funext k
  by_cases hk : k ∈ S <;> simp [fourierCoefficientExtension, hk]

lemma fourierCoefficientExtension_smul (S : Finset (Fin 2 → ℤ)) (c : ℝ)
    (a : (k : S) → FourierVelocity) :
    fourierCoefficientExtension S (c • a) = c • fourierCoefficientExtension S a := by
  funext k
  by_cases hk : k ∈ S <;> simp [fourierCoefficientExtension, hk]

/-- Real linear reconstruction into actual functions on the lifted torus. -/
def fourierReconstruction (S : Finset (Fin 2 → ℤ)) :
    ((k : S) → FourierVelocity) →ₗ[ℝ] (Pt 2 → Pt 2) where
  toFun a := solenoidalFourierPolynomial S (fourierCoefficientExtension S a)
  map_add' a b := by
    rw [fourierCoefficientExtension_add, solenoidalFourierPolynomial_add]
  map_smul' c a := by
    rw [fourierCoefficientExtension_smul, solenoidalFourierPolynomial_real_smul]
    rfl

@[simp] lemma fourierReconstruction_apply (S : Finset (Fin 2 → ℤ))
    (a : (k : S) → FourierVelocity) :
    fourierReconstruction S a = solenoidalFourierPolynomial S (fourierCoefficientExtension S a) :=
  rfl

/-- The finite Galerkin velocity space consists of spatial functions. -/
def solenoidalFourierSpace (S : Finset (Fin 2 → ℤ)) : Submodule ℝ (Pt 2 → Pt 2) :=
  (fourierReconstruction S).range

instance finiteDimensional_solenoidalFourierSpace (S : Finset (Fin 2 → ℤ)) :
    FiniteDimensional ℝ (solenoidalFourierSpace S) := by
  unfold solenoidalFourierSpace
  infer_instance

theorem contDiff_of_mem_solenoidalFourierSpace (S : Finset (Fin 2 → ℤ))
    {v : Pt 2 → Pt 2} (hv : v ∈ solenoidalFourierSpace S) : ContDiff ℝ ∞ v := by
  obtain ⟨a, rfl⟩ := hv
  exact contDiff_solenoidalFourierPolynomial S _

theorem isPeriodic_of_mem_solenoidalFourierSpace (S : Finset (Fin 2 → ℤ))
    {v : Pt 2 → Pt 2} (hv : v ∈ solenoidalFourierSpace S) : IsPeriodic v := by
  obtain ⟨a, rfl⟩ := hv
  exact isPeriodic_solenoidalFourierPolynomial S _

theorem divergence_of_mem_solenoidalFourierSpace (S : Finset (Fin 2 → ℤ))
    {v : Pt 2 → Pt 2} (hv : v ∈ solenoidalFourierSpace S) (x : Pt 2) :
    divergence v x = 0 := by
  obtain ⟨a, rfl⟩ := hv
  exact divergence_solenoidalFourierPolynomial S _ x

/-- Differentiating twice multiplies each finite coefficient by its negative
Laplace eigenvalue and preserves the state space. -/
theorem lap_fourierReconstruction (S : Finset (Fin 2 → ℤ))
    (a : (k : S) → FourierVelocity) :
    lap (fourierReconstruction S a) =
      fourierReconstruction S (fun k => (-fourierEigenvalue k.1) • a k) := by
  rw [fourierReconstruction_apply, lap_solenoidalFourierPolynomial,
    fourierReconstruction_apply]
  funext x
  unfold solenoidalFourierPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  simp only [fourierCoefficientExtension_mem S _ k hk]

theorem lap_mem_solenoidalFourierSpace (S : Finset (Fin 2 → ℤ))
    {v : Pt 2 → Pt 2} (hv : v ∈ solenoidalFourierSpace S) :
    lap v ∈ solenoidalFourierSpace S := by
  obtain ⟨a, rfl⟩ := hv
  exact ⟨fun k => (-fourierEigenvalue k.1) • a k, (lap_fourierReconstruction S a).symm⟩

end AnomDiss
