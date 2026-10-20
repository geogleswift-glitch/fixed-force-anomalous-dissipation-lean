module

public import RequestProject.TorusL2Fourier
public import RequestProject.NSFourierFlux

/-!
# The genuine retained-frequency Galerkin coefficient equation

Orthogonal spatial testing gives the actual Leray multiplier of the force
and nonlinear term. Periodic integration by parts gives the viscous symbol,
and the finite-state ODE therefore supplies the true complex Fourier ODE.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

theorem fourierGalerkin_projection_mode_pair (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (a : FourierVelocity) (f : C(Pt 2, Pt 2)) :
    cellVectorPair (realFourierMode k (fourierLeray k a))
        ((fourierGalerkinModel S).eval ((fourierGalerkinModel S).projection f)) =
      (inner ℂ a (fourierLeray k (vectorFourierCoeff f k))).re := by
  let G := fourierGalerkinModel S
  let z : G.State := fourierGalerkinModeTest S hk a
  change cellVectorPair (G.eval z) (G.eval (G.projection f)) = _
  rw [← G.inner_eq_cellPair, real_inner_comm (G.projection f) z,
    G.inner_projection_test, cellVectorPair_comm]
  change cellVectorPair (realFourierMode k (fourierLeray k a)) f = _
  rw [realFourierMode_cellPair k _ f f.continuous, fourierLeray_self_adjoint]

theorem fourierGalerkin_projection_coefficient (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (f : C(Pt 2, Pt 2)) :
    vectorFourierCoeff ((fourierGalerkinModel S).eval ((fourierGalerkinModel S).projection f)) k =
      fourierLeray k (vectorFourierCoeff f k) := by
  let G := fourierGalerkinModel S
  ext i
  apply Complex.ext
  · have h := fourierGalerkin_projection_mode_pair S hk (EuclideanSpace.single i (1 : ℂ)) f
    rw [projected_realFourierMode_reads_re k i (G.eval (G.projection f))
      ((G.eval_contDiff _).of_le (natCast_le_infty 1)) (G.eval_periodic _) (G.eval_solenoidal _),
      EuclideanSpace.inner_single_left] at h
    simpa only [map_one, one_mul] using h
  · have h := fourierGalerkin_projection_mode_pair S hk (EuclideanSpace.single i Complex.I) f
    rw [projected_realFourierMode_reads_im k i (G.eval (G.projection f))
      ((G.eval_contDiff _).of_le (natCast_le_infty 1)) (G.eval_periodic _) (G.eval_solenoidal _),
      EuclideanSpace.inner_single_left] at h
    simpa [Complex.mul_re] using h

theorem vectorFourierCoeff_lap (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v)
    (hp : IsPeriodic v) (k : Fin 2 → ℤ) :
    vectorFourierCoeff (lap v) k = (-fourierEigenvalue k) • vectorFourierCoeff v k := by
  ext i
  have hpd (j : Fin 2) :
      vectorFourierCoeff (pd j (pd j v)) k i =
        (2 * π * Complex.I * (k j : ℂ)) *
          ((2 * π * Complex.I * (k j : ℂ)) * vectorFourierCoeff v k i) := by
    rw [vectorFourierCoeff_pd (pd j v) (contDiff_pd_of_C2 v hv j) (isPeriodic_pd v hp j),
      vectorFourierCoeff_pd v (hv.of_le (by norm_num)) hp]
    rfl
  have heq : (fun x => (lap v x i : ℂ)) =
      fun x => ∑ j : Fin 2, ((pd j (pd j v) x i : ℝ) : ℂ) := by
    funext x
    simp only [lap, Finset.sum_apply, Complex.ofReal_sum]
  change fc (fun x => (lap v x i : ℂ)) k = _
  rw [heq]
  unfold fc
  simp only [Finset.sum_mul]
  rw [integral_finset_sum (μ := volume.restrict (cell 2))
    (f := fun j x => ((pd j (pd j v) x i : ℝ) : ℂ) * expChar (-intVec k) x)
    (Finset.univ : Finset (Fin 2)) (fun j _ =>
      ((Complex.continuous_ofReal.comp ((continuous_apply i).comp
        (continuous_pd_of_C1 _ (contDiff_pd_of_C2 v hv j) j))).mul
        (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc)]
  change (∑ j : Fin 2, vectorFourierCoeff (pd j (pd j v)) k i) = _
  simp only [hpd, Fin.sum_univ_two, PiLp.smul_apply, Complex.real_smul]
  unfold fourierEigenvalue euclNorm
  rw [sq_sqrt (by positivity)]
  simp only [intVec, Fin.sum_univ_two]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

def nonlinearFourierFluxVector (v : Pt 2 → Pt 2) (k : Fin 2 → ℤ) : FourierVelocity :=
  WithLp.toLp 2 (fun i => nonlinearFourierFlux v k i)

theorem fourierGalerkin_viscosity_coefficient (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (i : Fin 2) (v : (fourierGalerkinModel S).State) :
    (fourierGalerkinModel S).fourierCoeffCLM k i ((fourierGalerkinModel S).viscosity v) =
      ((-fourierEigenvalue k : ℝ) : ℂ) * vectorFourierCoeff ((fourierGalerkinModel S).eval v) k i := by
  let G := fourierGalerkinModel S
  rw [G.fourierCoeffCLM_apply]
  change vectorFourierCoeff (G.eval (G.projection (G.lapField v))) k i = _
  rw [fourierGalerkin_projection_coefficient S hk]
  change fourierLeray k (vectorFourierCoeff (lap (G.eval v)) k) i = _
  rw [vectorFourierCoeff_lap (G.eval v) ((G.eval_contDiff v).of_le (natCast_le_infty 2))
    (G.eval_periodic v), ContinuousLinearMap.map_smul_of_tower,
    fourierLeray_vectorFourierCoeff (G.eval v) ((G.eval_contDiff v).of_le (natCast_le_infty 1))
      (G.eval_periodic v) (G.eval_solenoidal v)]
  rfl

theorem fourierGalerkin_transport_coefficient (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (i : Fin 2) (v : (fourierGalerkinModel S).State) :
    (fourierGalerkinModel S).fourierCoeffCLM k i ((fourierGalerkinModel S).transport v v) =
      fourierLeray k (nonlinearFourierFluxVector ((fourierGalerkinModel S).eval v) k) i := by
  let G := fourierGalerkinModel S
  rw [G.fourierCoeffCLM_apply]
  change vectorFourierCoeff (G.eval (G.projection (G.convField v v))) k i = _
  rw [fourierGalerkin_projection_coefficient S hk]
  have heq : vectorFourierCoeff (conv (G.eval v) (G.eval v)) k =
      nonlinearFourierFluxVector (G.eval v) k := by
    ext j
    exact vectorFourierCoeff_conv_eq_flux (G.eval v)
      ((G.eval_contDiff v).of_le (natCast_le_infty 1)) (G.eval_periodic v) (G.eval_solenoidal v) k j
  change fourierLeray k (vectorFourierCoeff (conv (G.eval v) (G.eval v)) k) i = _
  rw [heq]

def galerkinFourierRHS (ν : ℝ) (v : Pt 2 → Pt 2) (f : Pt 2 → Pt 2)
    (k : Fin 2 → ℤ) (i : Fin 2) : ℂ :=
  ((-(ν * fourierEigenvalue k) : ℝ) : ℂ) * vectorFourierCoeff v k i -
    fourierLeray k (nonlinearFourierFluxVector v k) i + fourierLeray k (vectorFourierCoeff f k) i

theorem fourierGalerkin_rhs_coefficient (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (i : Fin 2) (ν : ℝ)
    (v : (fourierGalerkinModel S).State) (f : C(Pt 2, Pt 2)) :
    (fourierGalerkinModel S).fourierCoeffCLM k i
      ((fourierGalerkinModel S).nsField ν v + (fourierGalerkinModel S).projection f) =
      galerkinFourierRHS ν ((fourierGalerkinModel S).eval v) f k i := by
  let G := fourierGalerkinModel S
  simp only [FiniteSolenoidalSpace.nsField, map_add, map_sub, map_smul,
    fourierGalerkin_viscosity_coefficient S hk i v, fourierGalerkin_transport_coefficient S hk i v]
  rw [G.fourierCoeffCLM_apply, fourierGalerkin_projection_coefficient S hk]
  simp only [galerkinFourierRHS, Complex.real_smul]
  push_cast
  ring

/-- The actual finite-state evolution gives the retained complex Fourier ODE. -/
theorem hasDerivAt_fourierGalerkin_coefficient (S : Finset (Fin 2 → ℤ))
    {k : Fin 2 → ℤ} (hk : k ∈ S) (i : Fin 2) (ν : ℝ)
    (u : ℝ → (fourierGalerkinModel S).State) (f : ℝ → C(Pt 2, Pt 2)) {t : ℝ}
    (hu : HasDerivAt u ((fourierGalerkinModel S).nsField ν (u t) +
      (fourierGalerkinModel S).projection (f t)) t) :
    HasDerivAt (fun s => vectorFourierCoeff ((fourierGalerkinModel S).eval (u s)) k i)
      (galerkinFourierRHS ν ((fourierGalerkinModel S).eval (u t)) (f t) k i) t := by
  have h := (fourierGalerkinModel S).hasDerivAt_fourierCoeff k i hu
  rw [← (fourierGalerkinModel S).fourierCoeffCLM_apply,
    fourierGalerkin_rhs_coefficient S hk i ν (u t) (f t)] at h
  exact h

end AnomDiss
