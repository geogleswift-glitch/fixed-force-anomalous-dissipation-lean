module

public import RequestProject.NSGalerkinCalculus

/-!
# Energy tests of the finite-dimensional projected equation

The test equation below is the genuine weak form of the Galerkin ODE. Its
velocity and Laplacian test functions belong to the finite-dimensional space.
Periodic integration by parts and the two-dimensional nonlinear cancellation
then supply the identities used in `NSGalerkinApriori`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- The vector Laplacian energy pairing on the periodic cell. -/
theorem ns_velocity_laplacian_pairing (v : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v) :
    (∫ x in cell 2, dot (v x) (lap v x)) = -(∫ x in cell 2, gradSqV v x) := by
  have hk : ∀ k : Fin 2, ContDiff ℝ 2 (cmp v k) := contDiff_cmp hv
  have hkp : ∀ k : Fin 2, IsPeriodic (cmp v k) := fun k x n => by
    simp [cmp, hp x n]
  have heq : (fun x => dot (v x) (lap v x)) =
      fun x => ∑ k : Fin 2, cmp v k x * lap (cmp v k) x := by
    funext x
    simp only [dot, cmp, lap_component v hv]
  rw [heq, integral_finset_sum (f := fun k x => cmp v k x * lap (cmp v k) x) _
    (fun k _ => integrableOn_cell_of_continuous
      ((hk k).continuous.mul (continuous_lap_of_C2 _ (hk k))))]
  simp only [fun k => integral_mul_lap (cmp v k) (hk k) (hkp k)]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum
    (f := fun k x => gradSq (cmp v k) x) _ (fun k _ =>
      integrableOn_cell_of_continuous (continuous_finset_sum _ (fun j _ =>
        (continuous_pd_of_C1 _ ((hk k).of_le (by norm_num)) j).pow 2)))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  simp only [gradSq, gradSqV, pd_component v x (hv.differentiable (by norm_num) x)]
  exact Finset.sum_comm

/-- The velocity nonlinear term does no work in the kinetic-energy test. -/
theorem ns_velocity_convection_cancellation (v : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 1 v) (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) :
    (∫ x in cell 2, dot (v x) (conv v v x)) = 0 := by
  have hk : ∀ k : Fin 2, ContDiff ℝ 1 (cmp v k) := contDiff_cmp hv
  have hkp : ∀ k : Fin 2, IsPeriodic (cmp v k) := fun k x n => by
    simp [cmp, hp x n]
  have heq : (fun x => dot (v x) (conv v v x)) =
      fun x => ∑ k : Fin 2, cmp v k x * conv v (cmp v k) x := by
    funext x
    simp only [dot, cmp, conv_component v v (hv.differentiable one_ne_zero)]
  rw [heq, integral_finset_sum (f := fun k x => cmp v k x * conv v (cmp v k) x) _
    (fun k _ => integrableOn_cell_of_continuous
      ((hk k).continuous.mul (continuous_conv_of_C1 v hv.continuous _ (hk k))))]
  simp only [fun k => integral_mul_conv v hv hp hdiv (cmp v k) (hk k) (hkp k)]
  simp

/-- Testing the projected equation with `v` and `Δv` gives precisely the two
identities needed for the uniform Galerkin estimates. -/
theorem ns_galerkin_tests (S : Submodule ℝ (Pt 2 → Pt 2)) (ν : ℝ)
    (v V' g : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0)
    (hmem : v ∈ S) (hlapmem : lap v ∈ S)
    (hweak : ∀ w ∈ S,
      (∫ x in cell 2, dot (w x) (V' x)) + (∫ x in cell 2, dot (w x) (conv v v x)) =
        ν * (∫ x in cell 2, dot (w x) (lap v x)) + (∫ x in cell 2, dot (w x) (g x))) :
    ((∫ x in cell 2, dot (v x) (V' x)) + ν * (∫ x in cell 2, gradSqV v x) =
      (∫ x in cell 2, dot (v x) (g x))) ∧
    (-(∫ x in cell 2, dot (lap v x) (V' x)) + ν * l2sqV (lap v) =
      -(∫ x in cell 2, dot (lap v x) (g x))) := by
  constructor
  · have h := hweak v hmem
    rw [ns_velocity_convection_cancellation v (hv.of_le (by norm_num)) hp hdiv,
      ns_velocity_laplacian_pairing v hv hp] at h
    linarith
  · have h := hweak (lap v) hlapmem
    rw [ns_laplacian_convection_cancellation v hv hp hdiv] at h
    have heq : (∫ x in cell 2, dot (lap v x) (lap v x)) = l2sqV (lap v) := by
      unfold dot l2sqV
      congr 1
      funext x
      simp only [pow_two]
    rw [heq] at h
    linarith

end AnomDiss
