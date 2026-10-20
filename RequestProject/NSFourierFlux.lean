module

public import RequestProject.NSPhaseGalerkinLimitCoefficients

/-!
# The nonlinear Fourier flux and its actual spatial L² stability

For smooth solenoidal fields, the advective term is the divergence of the
quadratic velocity tensor. The resulting Fourier moments are stable under
strong spatial `L²` convergence, with constants depending only on velocity
energy and the fixed frequency.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

/-- The genuine quadratic Fourier tensor moment of two real velocity fields. -/
def quadraticFourierCoefficient (v w : Pt 2 → Pt 2) (k : Fin 2 → ℤ) (j i : Fin 2) : ℂ :=
  fc (fun x => ((v x j * w x i : ℝ) : ℂ)) k

/-- The Fourier coefficient of the distributional divergence of `v ⊗ v`. -/
def nonlinearFourierFlux (v : Pt 2 → Pt 2) (k : Fin 2 → ℤ) (i : Fin 2) : ℂ :=
  ∑ j : Fin 2, (2 * π * Complex.I * (k j : ℂ)) * quadraticFourierCoefficient v v k j i

/-- The advective term has the exact conservative tensor form whenever the
actual velocity is divergence free. -/
theorem conv_eq_quadratic_divergence (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, divergence v x = 0) (x : Pt 2) (i : Fin 2) :
    conv v v x i = ∑ j : Fin 2, pd j (fun y => v y j * v y i) x := by
  have hprod (j : Fin 2) : pd j (fun y => v y j * v y i) x =
      pd j v x j * v x i + v x j * pd j v x i := by
    rw [pd_mul' _ _ x ((contDiff_pi.1 hv j).differentiable one_ne_zero x)
      ((contDiff_pi.1 hv i).differentiable one_ne_zero x)]
    rw [pd_component v x (hv.differentiable one_ne_zero x),
      pd_component v x (hv.differentiable one_ne_zero x)]
  have hd : (∑ j : Fin 2, pd j v x j) = 0 := hdiv x
  simp only [hprod, Finset.sum_add_distrib, ← Finset.sum_mul, hd,
    zero_mul, zero_add, conv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The genuine advective Fourier coefficient equals the conservative
quadratic flux, proved by periodic integration by parts. -/
theorem vectorFourierCoeff_conv_eq_flux (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff (conv v v) k i = nonlinearFourierFlux v k i := by
  have hprod (j : Fin 2) : ContDiff ℝ 1 (fun y => v y j * v y i) :=
    (contDiff_pi.1 hv j).mul (contDiff_pi.1 hv i)
  have hcomplex (j : Fin 2) : ContDiff ℝ 1 (fun y => ((v y j * v y i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hprod j)
  have hpd (j : Fin 2) : pd j (fun y => ((v y j * v y i : ℝ) : ℂ)) =
      fun x => ((pd j (fun y => v y j * v y i) x : ℝ) : ℂ) := by
    exact pd_clm_fun Complex.ofRealCLM _ j ((hprod j).differentiable one_ne_zero)
  have heq : (fun x => (conv v v x i : ℂ)) =
      fun x => ∑ j : Fin 2, pd j (fun y => ((v y j * v y i : ℝ) : ℂ)) x := by
    funext x
    rw [conv_eq_quadratic_divergence v hv hdiv]
    simp only [hpd, Complex.ofReal_sum]
  change fc (fun x => (conv v v x i : ℂ)) k = _
  rw [heq]
  unfold fc
  simp only [Finset.sum_mul]
  rw [integral_finset_sum (μ := volume.restrict (cell 2))
    (f := fun j x => pd j (fun y => ((v y j * v y i : ℝ) : ℂ)) x * expChar (-intVec k) x)
    (Finset.univ : Finset (Fin 2))
    (fun j _ => ((continuous_pd_of_C1 _ (hcomplex j) j).mul
      (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc)]
  change (∑ j : Fin 2, fc (pd j (fun y => ((v y j * v y i : ℝ) : ℂ))) k) = _
  simp only [fun j => fc_pd _ (hcomplex j)
    (fun x n => by simp only [hp x n]) j k, nonlinearFourierFlux, quadraticFourierCoefficient]

private theorem scalar_abs_product_cauchy_schwarz (f g : Pt 2 → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x in cell 2, |f x * g x|) ≤ sqrt (l2sq f) * sqrt (l2sq g) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (cell 2))
    Real.HolderConjugate.two_two (f := fun x => |f x|) (g := fun x => |g x|)
    (Eventually.of_forall fun x => abs_nonneg _) (Eventually.of_forall fun x => abs_nonneg _)
    ?_ ?_
  · simp only [Real.rpow_two, sq_abs, ← abs_mul] at h
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact h
  · rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hf.abs.aestronglyMeasurable).2
      (integrableOn_cell_of_continuous (hf.abs.pow 2))
  · rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hg.abs.aestronglyMeasurable).2
      (integrableOn_cell_of_continuous (hg.abs.pow 2))

private theorem l2sq_component_le (v : Pt 2 → Pt 2) (hv : Continuous v) (i : Fin 2) :
    l2sq (fun x => v x i) ≤ l2sqV v := by
  apply setIntegral_mono_on
    (integrableOn_cell_of_continuous (((continuous_apply i).comp hv).pow 2))
    (integrableOn_cell_of_continuous (continuous_finset_sum _ fun j _ =>
      ((continuous_apply j).comp hv).pow 2)) measurableSet_Icc
  intro x _
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- Every actual quadratic Fourier moment is bounded by the spatial `L²`
norms of the two fields. -/
theorem norm_quadraticFourierCoefficient_le (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hw : Continuous w) (k : Fin 2 → ℤ) (j i : Fin 2) :
    ‖quadraticFourierCoefficient v w k j i‖ ≤ sqrt (l2sqV v) * sqrt (l2sqV w) := by
  have hj := (continuous_apply j).comp hv
  have hi := (continuous_apply i).comp hw
  calc
    ‖quadraticFourierCoefficient v w k j i‖ ≤
        ∫ x in cell 2, ‖((v x j * w x i : ℝ) : ℂ) * expChar (-intVec k) x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x in cell 2, |v x j * w x i| := by
      congr 1
      funext x
      rw [norm_mul, norm_expChar, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ sqrt (l2sq (fun x => v x j)) * sqrt (l2sq (fun x => w x i)) :=
      scalar_abs_product_cauchy_schwarz _ _ hj hi
    _ ≤ sqrt (l2sqV v) * sqrt (l2sqV w) :=
      mul_le_mul (sqrt_le_sqrt (l2sq_component_le v hv j))
        (sqrt_le_sqrt (l2sq_component_le w hw i)) (sqrt_nonneg _) (sqrt_nonneg _)

/-- The quadratic Fourier tensor is stable in the genuine spatial `L²`
distance. This estimate is independent of spatial derivative norms. -/
theorem quadraticFourierCoefficient_difference_le (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hw : Continuous w) (k : Fin 2 → ℤ) (j i : Fin 2) :
    ‖quadraticFourierCoefficient v v k j i - quadraticFourierCoefficient w w k j i‖ ≤
      (sqrt (l2sqV v) + sqrt (l2sqV w)) * sqrt (l2sqV (v - w)) := by
  have hc (a b : Pt 2 → Pt 2) (ha : Continuous a) (hb : Continuous b) :
      IntegrableOn (fun x => ((a x j * b x i : ℝ) : ℂ) * expChar (-intVec k) x) (cell 2) :=
    ((Complex.continuous_ofReal.comp (((continuous_apply j).comp ha).mul
      ((continuous_apply i).comp hb))).mul (continuous_expChar _)).continuousOn.integrableOn_compact
        isCompact_Icc
  have hid : quadraticFourierCoefficient v v k j i - quadraticFourierCoefficient w w k j i =
      quadraticFourierCoefficient (v - w) v k j i + quadraticFourierCoefficient w (v - w) k j i := by
    unfold quadraticFourierCoefficient fc
    rw [← integral_sub (hc v v hv hv) (hc w w hw hw),
      ← integral_add (hc (v - w) v (hv.sub hw) hv) (hc w (v - w) hw (hv.sub hw))]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    dsimp only
    simp only [Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [hid]
  calc
    ‖quadraticFourierCoefficient (v - w) v k j i + quadraticFourierCoefficient w (v - w) k j i‖ ≤
      ‖quadraticFourierCoefficient (v - w) v k j i‖ +
        ‖quadraticFourierCoefficient w (v - w) k j i‖ := norm_add_le _ _
    _ ≤ sqrt (l2sqV (v - w)) * sqrt (l2sqV v) + sqrt (l2sqV w) * sqrt (l2sqV (v - w)) :=
      add_le_add (norm_quadraticFourierCoefficient_le _ _ (hv.sub hw) hv k j i)
        (norm_quadraticFourierCoefficient_le _ _ hw (hv.sub hw) k j i)
    _ = (sqrt (l2sqV v) + sqrt (l2sqV w)) * sqrt (l2sqV (v - w)) := by ring

/-- The actual conservative nonlinear Fourier flux is continuous with
respect to strong spatial `L²` convergence at every fixed frequency. -/
theorem nonlinearFourierFlux_difference_le (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hw : Continuous w) (k : Fin 2 → ℤ) (i : Fin 2) :
    ‖nonlinearFourierFlux v k i - nonlinearFourierFlux w k i‖ ≤
      fourierTestDerivativeBound k *
        ((sqrt (l2sqV v) + sqrt (l2sqV w)) * sqrt (l2sqV (v - w))) := by
  let B := (sqrt (l2sqV v) + sqrt (l2sqV w)) * sqrt (l2sqV (v - w))
  have heq : nonlinearFourierFlux v k i - nonlinearFourierFlux w k i =
      ∑ j : Fin 2, (2 * π * Complex.I * (k j : ℂ)) *
        (quadraticFourierCoefficient v v k j i - quadraticFourierCoefficient w w k j i) := by
    simp only [nonlinearFourierFlux, ← Finset.sum_sub_distrib, mul_sub]
  rw [heq]
  calc
    ‖∑ j : Fin 2, (2 * π * Complex.I * (k j : ℂ)) *
        (quadraticFourierCoefficient v v k j i - quadraticFourierCoefficient w w k j i)‖ ≤
      ∑ j : Fin 2, ‖(2 * π * Complex.I * (k j : ℂ)) *
        (quadraticFourierCoefficient v v k j i - quadraticFourierCoefficient w w k j i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, ‖(2 * π * Complex.I * (k j : ℂ))‖ * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (quadraticFourierCoefficient_difference_le v w hv hw k j i)
        (norm_nonneg _)
    _ = fourierTestDerivativeBound k *
        ((sqrt (l2sqV v) + sqrt (l2sqV w)) * sqrt (l2sqV (v - w))) := by
      simp only [Fin.sum_univ_two, norm_mul, Complex.norm_I, Complex.norm_intCast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos, mul_one,
        fourierTestDerivativeBound]
      norm_num
      dsimp [B]
      ring

end AnomDiss
