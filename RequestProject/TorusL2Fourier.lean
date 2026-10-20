module

public import RequestProject.TorusVelocityL2
public import RequestProject.NSFourierModeTests

/-!
# Genuine Fourier coefficient functionals on the completed velocity space

Real cosine and sine tests define continuous real-linear complex coefficient
functionals on cell `L²`. On an actual continuous periodic field they equal
the manuscript's integral Fourier coefficients exactly.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

def l2FourierTestReal (k : Fin 2 → ℤ) (i : Fin 2) : TorusVelocityL2 :=
  periodicVelocityToL2 (realFourierMode k (EuclideanSpace.single i (1 : ℂ)))
    (contDiff_realFourierMode k _).continuous (isPeriodic_realFourierMode k _)

def l2FourierTestImag (k : Fin 2 → ℤ) (i : Fin 2) : TorusVelocityL2 :=
  periodicVelocityToL2 (realFourierMode k (EuclideanSpace.single i Complex.I))
    (contDiff_realFourierMode k _).continuous (isPeriodic_realFourierMode k _)

/-- The actual complex Fourier coefficient of a real `L²` velocity. -/
def l2FourierCoeff (k : Fin 2 → ℤ) (i : Fin 2) : TorusVelocityL2 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ (l2FourierTestReal k i)) +
    ((ContinuousLinearMap.mul ℝ ℂ Complex.I).comp Complex.ofRealCLM).comp
      (innerSL ℝ (l2FourierTestImag k i))

theorem l2FourierCoeff_periodicVelocityToL2 (k : Fin 2 → ℤ) (i : Fin 2)
    (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) :
    l2FourierCoeff k i (periodicVelocityToL2 v hv hp) = vectorFourierCoeff v k i := by
  have hR : cellVectorPair (realFourierMode k (EuclideanSpace.single i (1 : ℂ))) v =
      (vectorFourierCoeff v k i).re := by
    rw [realFourierMode_cellPair k _ v hv, EuclideanSpace.inner_single_left]
    simp
  have hI : cellVectorPair (realFourierMode k (EuclideanSpace.single i Complex.I)) v =
      (vectorFourierCoeff v k i).im := by
    rw [realFourierMode_cellPair k _ v hv, EuclideanSpace.inner_single_left]
    simp [Complex.mul_re]
  change (⟪l2FourierTestReal k i, periodicVelocityToL2 v hv hp⟫_ℝ : ℂ) +
    Complex.I * (⟪l2FourierTestImag k i, periodicVelocityToL2 v hv hp⟫_ℝ : ℂ) = _
  unfold l2FourierTestReal l2FourierTestImag
  rw [inner_periodicVelocityToL2, inner_periodicVelocityToL2, hR, hI]
  simpa only [mul_comm] using Complex.re_add_im (vectorFourierCoeff v k i)

namespace FiniteSolenoidalSpace

variable (G : FiniteSolenoidalSpace)

def fourierCoeffCLM (k : Fin 2 → ℤ) (i : Fin 2) : G.State →L[ℝ] ℂ :=
  (l2FourierCoeff k i).comp G.toL2Isometry.toContinuousLinearMap

theorem fourierCoeffCLM_apply (k : Fin 2 → ℤ) (i : Fin 2) (v : G.State) :
    G.fourierCoeffCLM k i v = vectorFourierCoeff (G.eval v) k i :=
  l2FourierCoeff_periodicVelocityToL2 k i (G.eval v)
    (G.eval_contDiff v).continuous (G.eval_periodic v)

theorem hasDerivAt_fourierCoeff (k : Fin 2 → ℤ) (i : Fin 2)
    {u : ℝ → G.State} {u' : G.State} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => vectorFourierCoeff (G.eval (u s)) k i)
      (vectorFourierCoeff (G.eval u') k i) t := by
  simpa only [Function.comp_def, G.fourierCoeffCLM_apply] using
    (G.fourierCoeffCLM k i).hasFDerivAt.comp_hasDerivAt t hu

end FiniteSolenoidalSpace

end AnomDiss
