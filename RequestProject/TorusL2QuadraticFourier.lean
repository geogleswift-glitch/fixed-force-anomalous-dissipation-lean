module

public import RequestProject.TorusVelocityL2
public import RequestProject.NSFourierFlux
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Genuine quadratic Fourier moments on the completed velocity L² space

The products are constructed by Hölder's continuous bilinear map from `L² × L²`
to `L¹`, then tested against the actual bounded Fourier character. Therefore
they are defined on Lebesgue equivalence classes and are continuous for strong
`L²` convergence. For smooth periodic fields they equal the original spatial
Fourier tensor moments exactly.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

abbrev TorusComplexL2 := Lp ℂ 2 (volume.restrict (cell 2))
abbrev TorusComplexL1 := Lp ℂ 1 (volume.restrict (cell 2))

/-- The actual real velocity coordinate, viewed in complex spatial `L²`. -/
def torusComplexComponent (i : Fin 2) : TorusVelocityL2 →L[ℝ] TorusComplexL2 :=
  (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i)).compLpL
    2 (volume.restrict (cell 2))

theorem torusComplexComponent_ae (i : Fin 2) (u : TorusVelocityL2) :
    torusComplexComponent i u =ᵐ[volume.restrict (cell 2)] fun x => (u x i : ℂ) :=
  (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i)).coeFn_compLpL u

def fourierCharacterBCF (k : Fin 2 → ℤ) : Pt 2 →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (expChar (-intVec k))
    (continuous_expChar _) 1 (fun _x => (norm_expChar _ _).le)

def fourierCharacterLInfinity (k : Fin 2 → ℤ) :
    Lp ℂ ⊤ (volume.restrict (cell 2)) :=
  BoundedContinuousFunction.toLp ⊤ (volume.restrict (cell 2)) ℝ (fourierCharacterBCF k)

theorem fourierCharacterLInfinity_ae (k : Fin 2 → ℤ) :
    fourierCharacterLInfinity k =ᵐ[volume.restrict (cell 2)] expChar (-intVec k) :=
  (fourierCharacterBCF k).coeFn_toLp ⊤ (volume.restrict (cell 2)) ℝ

/-- Testing an `L¹` complex function against the true Fourier character. -/
def torusFourierL1Functional (k : Fin 2 → ℤ) : TorusComplexL1 →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).lpPairing (volume.restrict (cell 2)) ⊤ 1
    (fourierCharacterLInfinity k)

/-- The genuine Hölder product from complex `L² × L²` into `L¹`. -/
def torusComplexProduct : TorusComplexL2 →L[ℝ] TorusComplexL2 →L[ℝ] TorusComplexL1 :=
  (ContinuousLinearMap.mul ℝ ℂ).holderL (volume.restrict (cell 2)) 2 2 1

/-- Quadratic Fourier tensor moment as an actual continuous bilinear map on
the completed real velocity Hilbert space. -/
def torusQuadraticFourierBilinear (k : Fin 2 → ℤ) (j i : Fin 2) :
    TorusVelocityL2 →L[ℝ] TorusVelocityL2 →L[ℝ] ℂ :=
  ((torusFourierL1Functional k).postcomp TorusVelocityL2).comp
    (((ContinuousLinearMap.precompR TorusVelocityL2 torusComplexProduct).flip
      (torusComplexComponent i)).comp
      (torusComplexComponent j))

theorem torusQuadraticFourierBilinear_integral (k : Fin 2 → ℤ) (j i : Fin 2)
    (u v : TorusVelocityL2) :
    torusQuadraticFourierBilinear k j i u v =
      ∫ x in cell 2, ((u x j * v x i : ℝ) : ℂ) * expChar (-intVec k) x := by
  change torusFourierL1Functional k
    (torusComplexProduct (torusComplexComponent j u) (torusComplexComponent i v)) = _
  unfold torusFourierL1Functional
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [fourierCharacterLInfinity_ae k,
    (ContinuousLinearMap.mul ℝ ℂ).coeFn_holder (r := (1 : ℝ≥0∞))
      (torusComplexComponent j u) (torusComplexComponent i v),
    torusComplexComponent_ae j u, torusComplexComponent_ae i v] with x hx hw hu hv
  change fourierCharacterLInfinity k x *
    torusComplexProduct (torusComplexComponent j u) (torusComplexComponent i v) x = _
  change torusComplexProduct (torusComplexComponent j u) (torusComplexComponent i v) x =
    torusComplexComponent j u x * torusComplexComponent i v x at hw
  rw [hx, hw, hu, hv]
  simp only [Complex.ofReal_mul]
  ring

/-- For actual periodic fields, the completed-space tensor moment is exactly
the original spatial quadratic Fourier coefficient. -/
theorem torusQuadraticFourierBilinear_of_field (k : Fin 2 → ℤ) (j i : Fin 2)
    (v w : Pt 2 → Pt 2) (hv : Continuous v) (hvp : IsPeriodic v)
    (hw : Continuous w) (hwp : IsPeriodic w) :
    torusQuadraticFourierBilinear k j i (periodicVelocityToL2 v hv hvp)
      (periodicVelocityToL2 w hw hwp) = quadraticFourierCoefficient v w k j i := by
  rw [torusQuadraticFourierBilinear_integral]
  apply integral_congr_ae
  filter_upwards [periodicVelocityToL2_ae v hv hvp, periodicVelocityToL2_ae w hw hwp] with x hx hy
  rw [hx, hy]
  rfl

/-- Diagonal quadratic tensor moment on the genuine completed velocity space. -/
def torusQuadraticFourierMoment (k : Fin 2 → ℤ) (j i : Fin 2) (u : TorusVelocityL2) : ℂ :=
  torusQuadraticFourierBilinear k j i u u

theorem continuous_torusQuadraticFourierMoment (k : Fin 2 → ℤ) (j i : Fin 2) :
    Continuous (torusQuadraticFourierMoment k j i) :=
  (torusQuadraticFourierBilinear k j i).continuous.clm_apply continuous_id

private theorem norm_bilinear_diagonal_difference_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℂ) (u v : E) :
    ‖B u u - B v v‖ ≤ ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have heq : B u u - B v v = B (u - v) u + B v (u - v) := by
    rw [map_sub, ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [heq]
  calc
    ‖B (u - v) u + B v (u - v)‖ ≤ ‖B (u - v) u‖ + ‖B v (u - v)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u - v‖ * ‖u‖ + ‖B‖ * ‖v‖ * ‖u - v‖ :=
      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ = ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-- The completed-space quadratic moment has the required strong `L²`
stability, with a finite fixed-frequency operator constant. -/
theorem torusQuadraticFourierMoment_difference_le (k : Fin 2 → ℤ) (j i : Fin 2)
    (u v : TorusVelocityL2) :
    ‖torusQuadraticFourierMoment k j i u - torusQuadraticFourierMoment k j i v‖ ≤
      ‖torusQuadraticFourierBilinear k j i‖ * (‖u‖ + ‖v‖) * ‖u - v‖ :=
  norm_bilinear_diagonal_difference_le _ u v

/-- The conservative Fourier nonlinear flux on the completed velocity space. -/
def torusNonlinearFourierFlux (k : Fin 2 → ℤ) (i : Fin 2) (u : TorusVelocityL2) : ℂ :=
  ∑ j : Fin 2, (2 * π * Complex.I * (k j : ℂ)) * torusQuadraticFourierMoment k j i u

theorem continuous_torusNonlinearFourierFlux (k : Fin 2 → ℤ) (i : Fin 2) :
    Continuous (torusNonlinearFourierFlux k i) :=
  continuous_finset_sum _ fun j _ => continuous_const.mul
    (continuous_torusQuadraticFourierMoment k j i)

theorem torusNonlinearFourierFlux_of_field (k : Fin 2 → ℤ) (i : Fin 2)
    (v : Pt 2 → Pt 2) (hv : Continuous v) (hvp : IsPeriodic v) :
    torusNonlinearFourierFlux k i (periodicVelocityToL2 v hv hvp) = nonlinearFourierFlux v k i := by
  unfold torusNonlinearFourierFlux nonlinearFourierFlux torusQuadraticFourierMoment
  simp only [torusQuadraticFourierBilinear_of_field]

end AnomDiss
