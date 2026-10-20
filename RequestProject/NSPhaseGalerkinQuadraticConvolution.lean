module

public import RequestProject.NSPhaseGalerkinSobolevProduct

/-!
# Actual quadratic Fourier moments and coefficient convolution

Parseval's inner-product identity first gives the exact product formula
for continuous periodic fields. Strong spatial L² convergence then passes
the same formula to the completed-space velocity limit.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction ComplexConjugate

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

section CellParseval

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The genuine complex cross-Parseval identity on the unit cell. -/
theorem hasSum_cell_fourier_product_conj (f g : Pt 2 → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfp : IsPeriodic f) (hgp : IsPeriodic g) :
    HasSum (fun l => conj (fc f l) * fc g l)
      (∫ x in cell 2, conj (f x) * g x) := by
  let F : UnitAddTorus (Fin 2) → ℂ := torusLift f
  let G : UnitAddTorus (Fin 2) → ℂ := torusLift g
  have hFm : Measurable F := measurable_torusLift_complex f hf
  have hGm : Measurable G := measurable_torusLift_complex g hg
  obtain ⟨Cf, hCf⟩ := torusLift_bdd_complex f hf
  obtain ⟨Cg, hCg⟩ := torusLift_bdd_complex g hg
  have hF : MemLp F 2 volume :=
    MemLp.of_bound hFm.aestronglyMeasurable Cf (Eventually.of_forall hCf)
  have hG : MemLp G 2 volume :=
    MemLp.of_bound hGm.aestronglyMeasurable Cg (Eventually.of_forall hCg)
  have hcoeff (q : Pt 2 → ℂ) (hq : Continuous q) (hqp : IsPeriodic q)
      (Q : UnitAddTorus (Fin 2) → ℂ) (hQ : Q = torusLift q)
      (hmem : MemLp Q 2 volume) (l : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff (hmem.toLp Q) l = fc q l := by
    have hQm : Measurable Q := hQ ▸ measurable_torusLift_complex q hq
    rw [show UnitAddTorus.mFourierCoeff (hmem.toLp Q) l =
        UnitAddTorus.mFourierCoeff Q l by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with x hx
      rw [hx]]
    rw [UnitAddTorus.mFourierCoeff, integral_torus_eq_cell _
      (((UnitAddTorus.mFourier (-l)).continuous.measurable).fun_smul hQm).aestronglyMeasurable, fc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    simp only [hQ, torusLift_proj q hqp, mFourier_torusProj, smul_eq_mul]
    have hl : intVec (-l) = -intVec l := by ext i; simp [intVec]
    rw [hl, mul_comm]
  have hpair : (∫ x, conj (hF.toLp F x) * hG.toLp G x) =
      ∫ x in cell 2, conj (f x) * g x := by
    rw [show (∫ x, conj (hF.toLp F x) * hG.toLp G x) =
        ∫ x, conj (F x) * G x by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
      rw [hx, hy]]
    have hmeas : AEStronglyMeasurable (fun x => conj (F x) * G x) volume := by
      simpa only [Function.comp_def] using
        ((((by fun_prop : Continuous fun z : ℂ => conj z).measurable.comp hFm).fun_mul
          hGm).aestronglyMeasurable)
    rw [integral_torus_eq_cell (fun x => conj (F x) * G x) hmeas]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    simp only [F, G, torusLift_proj f hfp, torusLift_proj g hgp]
  have hs := UnitAddTorus.hasSum_prod_mFourierCoeff (hF.toLp F) (hG.toLp G)
  simpa only [hcoeff f hf hfp F rfl hF, hcoeff g hg hgp G rfl hG, hpair] using hs

end CellParseval

/-- Modulating the conjugated second factor turns cross-Parseval into the
Fourier coefficient of an ordinary product. -/
theorem conj_fc_conj_mul_expChar (g : Pt 2 → ℂ) (k l : Fin 2 → ℤ) :
    conj (fc (fun x => conj (g x) * expChar (intVec k) x) l) = fc g (k - l) := by
  unfold fc
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [map_mul, Complex.conj_conj, ← expChar_neg_eq_conj, neg_neg]
    rw [mul_assoc, expChar_mul]
    congr 2
    ext i
    simp only [Pi.add_apply, Pi.neg_apply, intVec, Pi.sub_apply, Int.cast_sub]
    ring

/-- Exact Fourier convolution for continuous periodic scalar factors. -/
theorem hasSum_fc_product (f g : Pt 2 → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfp : IsPeriodic f) (hgp : IsPeriodic g)
    (k : Fin 2 → ℤ) :
    HasSum (fun l => fc f l * fc g (k - l)) (fc (fun x => f x * g x) k) := by
  let G : Pt 2 → ℂ := fun x => conj (g x) * expChar (intVec k) x
  have hG : Continuous G := hg.star.mul (continuous_expChar _)
  have hGp : IsPeriodic G := fun x n => by
    simp only [G, hgp x n, isPeriodic_expChar k x n]
  have hs := hasSum_cell_fourier_product_conj G f hG hf hGp hfp
  have heq : (∫ x in cell 2, conj (G x) * f x) = fc (fun x => f x * g x) k := by
    unfold fc
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [G, map_mul, Complex.conj_conj, ← expChar_neg_eq_conj]
      ring
  rw [heq] at hs
  change HasSum (fun l => conj (fc (fun x => conj (g x) * expChar (intVec k) x) l) *
    fc f l) _ at hs
  simp_rw [conj_fc_conj_mul_expChar] at hs
  simpa only [mul_comm] using hs

/-- For an actual continuous periodic real velocity the genuine quadratic
moment is exactly the convolution of its vector Fourier coefficients. -/
theorem quadraticFourierCoefficient_eq_tsum (v : Pt 2 → Pt 2)
    (hv : Continuous v) (hvp : IsPeriodic v) (k : Fin 2 → ℤ) (j i : Fin 2) :
    quadraticFourierCoefficient v v k j i =
      ∑' l, vectorFourierCoeff v l j * vectorFourierCoeff v (k - l) i := by
  have hj : Continuous (fun x => (v x j : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_apply j).comp hv)
  have hi : Continuous (fun x => (v x i : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_apply i).comp hv)
  have hs := hasSum_fc_product (fun x => (v x j : ℂ)) (fun x => (v x i : ℂ))
    hj hi (fun x n => by simp only [hvp x n]) (fun x n => by simp only [hvp x n]) k
  simpa only [quadraticFourierCoefficient, vectorFourierCoeff_apply, Complex.ofReal_mul] using
    hs.tsum_eq.symm

private theorem vectorFourierCoeff_sub_continuous (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hw : Continuous w) (k : Fin 2 → ℤ) (i : Fin 2) :
    vectorFourierCoeff (v - w) k i = vectorFourierCoeff v k i - vectorFourierCoeff w k i := by
  have hv' := Complex.continuous_ofReal.comp ((continuous_apply i).comp hv)
  have hw' := Complex.continuous_ofReal.comp ((continuous_apply i).comp hw)
  simpa only [vectorFourierCoeff_apply, Pi.sub_apply, Complex.ofReal_sub] using
    (fc_sub (fun x => (v x i : ℂ)) (fun x => (w x i : ℂ)) hv' hw' k).symm

/-- Bessel's inequality for differences of actual smooth-cell embeddings. -/
theorem finite_l2FourierCoeff_difference_le_norm_sq (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hw : Continuous w) (hvp : IsPeriodic v) (hwp : IsPeriodic w)
    (S : Finset (Fin 2 → ℤ)) (i : Fin 2) :
    (∑ k ∈ S, ‖l2FourierCoeff k i (periodicVelocityToL2 v hv hvp) -
      l2FourierCoeff k i (periodicVelocityToL2 w hw hwp)‖ ^ 2) ≤
        ‖periodicVelocityToL2 v hv hvp - periodicVelocityToL2 w hw hwp‖ ^ 2 := by
  simp_rw [l2FourierCoeff_periodicVelocityToL2,
    ← vectorFourierCoeff_sub_continuous v w hv hw]
  rw [norm_periodicVelocityToL2_sub_sq]
  have hp : IsPeriodic (v - w) := fun x n => by simp only [Pi.sub_apply, hvp x n, hwp x n]
  have hs := parseval_vector_cell (v - w) (hv.sub hw) hp
  calc
    _ ≤ ∑ k ∈ S, vectorFourierEnergy (v - w) k := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.single_le_sum (f := fun j => ‖vectorFourierCoeff (v - w) k j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑' k, vectorFourierEnergy (v - w) k :=
      hs.summable.sum_le_tsum S (fun k _ => vectorFourierEnergy_nonneg _ k)
    _ = _ := hs.tsum_eq

/-- Strong spatial L² convergence controls the whole finite coefficient
difference energy, with constant one. -/
theorem phaseGalerkin_l2_limit_finite_coefficient_difference_le
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (N : ℕ) (t : GalerkinTime) (S : Finset (Fin 2 → ℤ)) (i : Fin 2) :
    (∑ k ∈ S, ‖l2FourierCoeff k i (phaseGalerkinL2Curve ν hν phase N t) -
      l2FourierCoeff k i (U t)‖ ^ 2) ≤
        ‖phaseGalerkinL2Curve ν hν phase N t - U t‖ ^ 2 := by
  have hp := ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto U).comp hU
  have hL : Tendsto (fun n => ∑ k ∈ S,
      ‖l2FourierCoeff k i (phaseGalerkinL2Curve ν hν phase N t) -
        l2FourierCoeff k i (phaseGalerkinL2Curve ν hν phase (φ n) t)‖ ^ 2) atTop
      (𝓝 (∑ k ∈ S, ‖l2FourierCoeff k i (phaseGalerkinL2Curve ν hν phase N t) -
        l2FourierCoeff k i (U t)‖ ^ 2)) := by
    exact tendsto_finset_sum S (fun k _ =>
      ((tendsto_const_nhds.sub ((l2FourierCoeff k i).continuous.tendsto (U t) |>.comp hp)).norm).pow 2)
  have hR : Tendsto (fun n => ‖phaseGalerkinL2Curve ν hν phase N t -
      phaseGalerkinL2Curve ν hν phase (φ n) t‖ ^ 2) atTop
      (𝓝 (‖phaseGalerkinL2Curve ν hν phase N t - U t‖ ^ 2)) := by
    exact (tendsto_const_nhds.sub hp).norm.pow 2
  apply le_of_tendsto_of_tendsto' hL hR
  intro n
  exact finite_l2FourierCoeff_difference_le_norm_sq
    (phaseGalerkinVelocity ν hν phase N t.1) (phaseGalerkinVelocity ν hν phase (φ n) t.1)
    (phaseGalerkinVelocity_contDiff ν hν phase N t.1).continuous
    (phaseGalerkinVelocity_contDiff ν hν phase (φ n) t.1).continuous
    (phaseGalerkinVelocity_periodic ν hν phase N t.1)
    (phaseGalerkinVelocity_periodic ν hν phase (φ n) t.1) S i

private theorem sum_convolution_shift (S : Finset (Fin 2 → ℤ)) (k : Fin 2 → ℤ)
    (F : (Fin 2 → ℤ) → ℝ) :
    (∑ l ∈ S, F (k - l)) = ∑ l ∈ S.image (fun l => k - l), F l := by
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact sub_right_inj.mp hab

/-- Finite convolution is uniformly continuous for the genuine finite
ℓ² energy distance, with no pointwise spatial regularity assumption. -/
theorem finite_sum_convolution_difference_norm_le
    (A B : (Fin 2 → ℤ) → Fin 2 → ℂ) {E D : ℝ} (hD : 0 ≤ D)
    (hA : ∀ S : Finset (Fin 2 → ℤ), ∀ i, ∑ l ∈ S, ‖A l i‖ ^ 2 ≤ E)
    (hB : ∀ S : Finset (Fin 2 → ℤ), ∀ i, ∑ l ∈ S, ‖B l i‖ ^ 2 ≤ E)
    (hAB : ∀ S : Finset (Fin 2 → ℤ), ∀ i, ∑ l ∈ S, ‖A l i - B l i‖ ^ 2 ≤ D ^ 2)
    (S : Finset (Fin 2 → ℤ)) (k : Fin 2 → ℤ) (j i : Fin 2) :
    (∑ l ∈ S, ‖A l j * A (k - l) i - B l j * B (k - l) i‖) ≤
      2 * Real.sqrt E * D := by
  have hAsh : ∑ l ∈ S, ‖A (k - l) i‖ ^ 2 ≤ E := by
    rw [sum_convolution_shift S k (fun l => ‖A l i‖ ^ 2)]
    exact hA _ i
  have hDsh : ∑ l ∈ S, ‖A (k - l) i - B (k - l) i‖ ^ 2 ≤ D ^ 2 := by
    rw [sum_convolution_shift S k (fun l => ‖A l i - B l i‖ ^ 2)]
    exact hAB _ i
  have hsqrtD (R : Finset (Fin 2 → ℤ)) (q : Fin 2) :
      Real.sqrt (∑ l ∈ R, ‖A l q - B l q‖ ^ 2) ≤ D :=
    (Real.sqrt_le_sqrt (hAB R q)).trans_eq (Real.sqrt_sq hD)
  have hsqrtDsh : Real.sqrt (∑ l ∈ S, ‖A (k - l) i - B (k - l) i‖ ^ 2) ≤ D :=
    (Real.sqrt_le_sqrt hDsh).trans_eq (Real.sqrt_sq hD)
  calc
    _ ≤ ∑ l ∈ S, (‖A l j - B l j‖ * ‖A (k - l) i‖ +
        ‖B l j‖ * ‖A (k - l) i - B (k - l) i‖) := by
      apply Finset.sum_le_sum
      intro l _
      have he : A l j * A (k - l) i - B l j * B (k - l) i =
          (A l j - B l j) * A (k - l) i + B l j * (A (k - l) i - B (k - l) i) := by ring
      rw [he]
      simpa only [norm_mul] using norm_add_le
        ((A l j - B l j) * A (k - l) i) (B l j * (A (k - l) i - B (k - l) i))
    _ = (∑ l ∈ S, ‖A l j - B l j‖ * ‖A (k - l) i‖) +
        ∑ l ∈ S, ‖B l j‖ * ‖A (k - l) i - B (k - l) i‖ := Finset.sum_add_distrib
    _ ≤ Real.sqrt (∑ l ∈ S, ‖A l j - B l j‖ ^ 2) *
          Real.sqrt (∑ l ∈ S, ‖A (k - l) i‖ ^ 2) +
        Real.sqrt (∑ l ∈ S, ‖B l j‖ ^ 2) *
          Real.sqrt (∑ l ∈ S, ‖A (k - l) i - B (k - l) i‖ ^ 2) :=
      add_le_add
        (Real.sum_mul_le_sqrt_mul_sqrt S (fun l => ‖A l j - B l j‖) (fun l => ‖A (k - l) i‖))
        (Real.sum_mul_le_sqrt_mul_sqrt S (fun l => ‖B l j‖)
          (fun l => ‖A (k - l) i - B (k - l) i‖))
    _ ≤ D * Real.sqrt E + Real.sqrt E * D := add_le_add
      (mul_le_mul (hsqrtD S j) (Real.sqrt_le_sqrt hAsh) (Real.sqrt_nonneg _) hD)
      (mul_le_mul (Real.sqrt_le_sqrt (hB S j)) hsqrtDsh (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Quantitative strong L² stability of the actual infinite Fourier
convolution along the genuine Galerkin approximants. -/
theorem phaseGalerkin_l2_limit_convolution_difference_le
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (N : ℕ) (t : GalerkinTime) (k : Fin 2 → ℤ) (j i : Fin 2) :
    ‖(∑' l, l2FourierCoeff l j (phaseGalerkinL2Curve ν hν phase N t) *
        l2FourierCoeff (k - l) i (phaseGalerkinL2Curve ν hν phase N t)) -
      ∑' l, l2FourierCoeff l j (U t) * l2FourierCoeff (k - l) i (U t)‖ ≤
        2 * Real.sqrt (phaseGalerkinEnergyBound phase) *
          ‖phaseGalerkinL2Curve ν hν phase N t - U t‖ := by
  have hN : Tendsto (fun _ : ℕ => phaseGalerkinL2Curve ν hν phase N) atTop
      (𝓝 (phaseGalerkinL2Curve ν hν phase N)) := tendsto_const_nhds
  have hA (S : Finset (Fin 2 → ℤ)) (q : Fin 2) :
      ∑ l ∈ S, ‖l2FourierCoeff l q (phaseGalerkinL2Curve ν hν phase N t)‖ ^ 2 ≤
        phaseGalerkinEnergyBound phase :=
    (Finset.sum_le_sum fun l _ => l2FourierCoeff_sq_le_energy _ l q).trans
      (phaseGalerkin_l2_limit_fourier_finite_energy ν hν phase hN t S)
  have hB (S : Finset (Fin 2 → ℤ)) (q : Fin 2) :
      ∑ l ∈ S, ‖l2FourierCoeff l q (U t)‖ ^ 2 ≤ phaseGalerkinEnergyBound phase :=
    (Finset.sum_le_sum fun l _ => l2FourierCoeff_sq_le_energy _ l q).trans
      (phaseGalerkin_l2_limit_fourier_finite_energy ν hν phase hU t S)
  have hfinite (S : Finset (Fin 2 → ℤ)) :
      (∑ l ∈ S, ‖l2FourierCoeff l j (phaseGalerkinL2Curve ν hν phase N t) *
          l2FourierCoeff (k - l) i (phaseGalerkinL2Curve ν hν phase N t) -
        l2FourierCoeff l j (U t) * l2FourierCoeff (k - l) i (U t)‖) ≤
          2 * Real.sqrt (phaseGalerkinEnergyBound phase) *
            ‖phaseGalerkinL2Curve ν hν phase N t - U t‖ :=
    finite_sum_convolution_difference_norm_le
      (fun l q => l2FourierCoeff l q (phaseGalerkinL2Curve ν hν phase N t))
      (fun l q => l2FourierCoeff l q (U t)) (norm_nonneg _) hA hB
      (fun R q => phaseGalerkin_l2_limit_finite_coefficient_difference_le ν hν phase hU N t R q)
      S k j i
  have hsA := (summable_norm_iff).mp
    (phaseGalerkin_l2_limit_convolution_norm_summable ν hν phase hN t k j i)
  have hsB := (summable_norm_iff).mp
    (phaseGalerkin_l2_limit_convolution_norm_summable ν hν phase hU t k j i)
  rw [← hsA.tsum_sub hsB]
  exact (norm_tsum_le_tsum_norm (summable_of_sum_le (fun _ => norm_nonneg _) hfinite)).trans
    (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hfinite)

/-- The actual quadratic coefficient convolution converges with the
genuine strong L² Galerkin limit. -/
theorem phaseGalerkin_l2_limit_convolution_tendsto
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (j i : Fin 2) :
    Tendsto (fun n => ∑' l, l2FourierCoeff l j (phaseGalerkinL2Curve ν hν phase (φ n) t) *
      l2FourierCoeff (k - l) i (phaseGalerkinL2Curve ν hν phase (φ n) t)) atTop
        (𝓝 (∑' l, l2FourierCoeff l j (U t) * l2FourierCoeff (k - l) i (U t))) := by
  have hp := ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto U).comp hU
  have hzero : Tendsto (fun n => 2 * Real.sqrt (phaseGalerkinEnergyBound phase) *
      ‖phaseGalerkinL2Curve ν hν phase (φ n) t - U t‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, sub_self, norm_zero, mul_zero] using
      ((hp.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => U t) atTop (𝓝 (U t)))).norm).const_mul
        (2 * Real.sqrt (phaseGalerkinEnergyBound phase))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => phaseGalerkin_l2_limit_convolution_difference_le ν hν phase hU (φ n) t k j i) hzero

/-- The completed-space quadratic Fourier moment of the actual limit is
exactly the absolutely convergent convolution of its own true coefficients. -/
theorem phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (j i : Fin 2) :
    torusQuadraticFourierMoment k j i (U t) =
      ∑' l, l2FourierCoeff l j (U t) * l2FourierCoeff (k - l) i (U t) := by
  have hp := ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto U).comp hU
  have hactual := ((continuous_torusQuadraticFourierMoment k j i).tendsto (U t)).comp hp
  have hconvolution := phaseGalerkin_l2_limit_convolution_tendsto ν hν phase hU t k j i
  have heq (n : ℕ) : torusQuadraticFourierMoment k j i
      (phaseGalerkinL2Curve ν hν phase (φ n) t) =
      ∑' l, l2FourierCoeff l j (phaseGalerkinL2Curve ν hν phase (φ n) t) *
        l2FourierCoeff (k - l) i (phaseGalerkinL2Curve ν hν phase (φ n) t) := by
    rw [phaseGalerkinL2Curve_eq]
    change torusQuadraticFourierBilinear k j i _ _ = _
    rw [torusQuadraticFourierBilinear_of_field]
    simp_rw [l2FourierCoeff_periodicVelocityToL2]
    exact quadraticFourierCoefficient_eq_tsum _
      (phaseGalerkinVelocity_contDiff ν hν phase (φ n) t.1).continuous
      (phaseGalerkinVelocity_periodic ν hν phase (φ n) t.1) k j i
  have hs : (fun n => torusQuadraticFourierMoment k j i
      (phaseGalerkinL2Curve ν hν phase (φ n) t)) =
      (fun n => ∑' l, l2FourierCoeff l j (phaseGalerkinL2Curve ν hν phase (φ n) t) *
        l2FourierCoeff (k - l) i (phaseGalerkinL2Curve ν hν phase (φ n) t)) := funext heq
  simp only [Function.comp_def] at hactual
  rw [hs] at hactual
  exact tendsto_nhds_unique hactual hconvolution

/-- Consequently the genuine nonlinear flux is the standard Fourier
convolution formula, including the physical `2πi` derivative multiplier. -/
theorem phaseGalerkin_l2_limit_nonlinearFourierFlux_eq_tsum
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (k : Fin 2 → ℤ) (i : Fin 2) :
    torusNonlinearFourierFlux k i (U t) =
      ∑ j : Fin 2, (2 * π * Complex.I * (k j : ℂ)) *
        ∑' l, l2FourierCoeff l j (U t) * l2FourierCoeff (k - l) i (U t) := by
  unfold torusNonlinearFourierFlux
  simp_rw [phaseGalerkin_l2_limit_quadraticFourierMoment_eq_tsum ν hν phase hU t]

end AnomDiss
