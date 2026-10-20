module

public import RequestProject.FourierGalerkinSpace
public import RequestProject.NonStationary
public import RequestProject.PulseAverage

/-!
# Fourier coefficients and solenoidal approximation

The Fourier divergence condition is derived from the actual spatial
divergence equation by periodic integration by parts. Consequently the finite
Leray reconstruction of a smooth solenoidal field uses its genuine Fourier
coefficients unchanged.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- Fourier integration by parts for a continuously differentiable periodic
complex function on the actual unit cell. -/
theorem fc_pd (f : Pt 2 → ℂ) (hf : ContDiff ℝ 1 f) (hp : IsPeriodic f)
    (j : Fin 2) (k : Fin 2 → ℤ) :
    fc (pd j f) k = (2 * π * Complex.I * (k j : ℂ)) * fc f k := by
  have hchar : IsPeriodic (expChar (-intVec k)) := by
    simpa only [intVec_neg] using isPeriodic_expChar (-k)
  have hi := integral_mul_pd_complex f (expChar (-intVec k)) hf
    ((contDiff_expChar _).of_le (by norm_cast)) hp hchar j
  apply neg_injective
  unfold fc
  calc
    -(∫ x in cell 2, pd j f x * expChar (-intVec k) x)
        = ∫ x in cell 2, f x * pd j (expChar (-intVec k)) x := hi.symm
    _ = -((2 * π * Complex.I * (k j : ℂ)) *
        ∫ x in cell 2, f x * expChar (-intVec k) x) := by
      rw [← integral_const_mul, ← integral_neg]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only
      rw [pd_expChar]
      simp only [Pi.neg_apply, intVec, Complex.ofReal_neg, Complex.ofReal_intCast]
      ring

/-- Genuine vector Fourier coefficients, in the coefficient Hilbert space. -/
def vectorFourierCoeff (v : Pt 2 → Pt 2) (k : Fin 2 → ℤ) : FourierVelocity :=
  WithLp.toLp 2 (fun i => fc (fun x => (v x i : ℂ)) k)

@[simp] lemma vectorFourierCoeff_apply (v : Pt 2 → Pt 2)
    (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff v k i = fc (fun x => (v x i : ℂ)) k := rfl

theorem vectorFourierCoeff_solenoidal (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) (k : Fin 2 → ℤ) :
    fourierDivSymbol k (vectorFourierCoeff v k) = 0 := by
  have hf : ∀ i, ContDiff ℝ 1 (fun x => (v x i : ℂ)) := fun i =>
    Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 hv i)
  have hpd : ∀ j i, pd j (fun x => (v x i : ℂ)) =
      fun x => (pd j v x i : ℂ) := by
    intro j i
    change pd j (fun x => Complex.ofRealCLM (v x i)) = _
    rw [pd_clm_fun Complex.ofRealCLM _ j
      ((contDiff_pi.1 hv i).differentiable one_ne_zero)]
    funext x
    rw [pd_component v x (hv.differentiable one_ne_zero x)]
    rfl
  have hid : ∀ x,
      (∑ i : Fin 2, pd i (fun y => (v y i : ℂ)) x) = 0 := by
    intro x
    simp only [hpd, ← Complex.ofReal_sum]
    rw [show (∑ i, pd i v x i) = 0 from hdiv x, Complex.ofReal_zero]
  have hsum : (2 * π * Complex.I) * fourierDivSymbol k (vectorFourierCoeff v k) = 0 := by
    have hi : ∀ i, IntegrableOn
        (fun x => pd i (fun y => (v y i : ℂ)) x * expChar (-intVec k) x) (cell 2) := fun i =>
      ((continuous_pd_of_C1 _ (hf i) i).mul (continuous_expChar _)).continuousOn.integrableOn_compact
        isCompact_Icc
    have he : ∑ i : Fin 2, fc (pd i (fun x => (v x i : ℂ))) k = 0 := by
      unfold fc
      rw [← integral_finset_sum _ (fun i _ => hi i)]
      simp only [← Finset.sum_mul, hid, zero_mul, integral_zero]
    have hfc : ∀ i : Fin 2, fc (pd i (fun x => (v x i : ℂ))) k =
        (2 * π * Complex.I * (k i : ℂ)) * fc (fun x => (v x i : ℂ)) k := fun i =>
      fc_pd _ (hf i) (fun x n => by simp only [hp x n]) i k
    simp only [hfc] at he
    simpa only [fourierDivSymbol, vectorFourierCoeff_apply, Finset.mul_sum, mul_assoc] using he
  exact (mul_eq_zero.mp hsum).resolve_left (by
    have hp0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) hp0) Complex.I_ne_zero)

theorem fourierLeray_vectorFourierCoeff (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v)
    (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) (k : Fin 2 → ℤ) :
    fourierLeray k (vectorFourierCoeff v k) = vectorFourierCoeff v k :=
  fourierLeray_fixes_solenoidal k _ (vectorFourierCoeff_solenoidal v hv hp hdiv k)

/-- The actual finite approximation lies in the concrete Fourier state space. -/
theorem fourierCoeff_polynomial_mem (S : Finset (Fin 2 → ℤ)) (v : Pt 2 → Pt 2) :
    solenoidalFourierPolynomial S (vectorFourierCoeff v) ∈ solenoidalFourierSpace S := by
  refine ⟨fun k => vectorFourierCoeff v k.1, ?_⟩
  funext x
  unfold fourierReconstruction solenoidalFourierPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  simp only [fourierCoefficientExtension_mem S _ k hk]

end AnomDiss
