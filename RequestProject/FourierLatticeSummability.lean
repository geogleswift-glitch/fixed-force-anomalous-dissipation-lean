module

public import RequestProject.NSPhaseGalerkinSobolevProduct
public import Mathlib.Analysis.PSeries

/-!
# Genuine two-dimensional Fourier lattice summability

One-dimensional integer p-series and a separated-coordinate majorant give
summability above the dimensional threshold for the inhomogeneous Laplace
weight. These are actual infinite-series results on the original frequency
lattice, without a lattice summability assumption.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

theorem summable_one_add_abs_int_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-s)) := by
  have hnat : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-s)) := by
    have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-s)) 1).mpr hp
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, Nat.abs_cast] using hnat
  · simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast] using hnat

lemma abs_intCast_le_sq (n : ℤ) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
  have hp : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Int.le_self_sq n
  have hn : -(n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h : ((-n : ℤ) : ℝ) ≤ ((-n : ℤ) : ℝ) ^ 2 := by
      exact_mod_cast Int.le_self_sq (-n)
    simpa only [Int.cast_neg, neg_sq] using h
  exact abs_le.mpr ⟨by linarith, hp⟩

/-- A separated positive weight is dominated by the true inhomogeneous
Laplace weight on the integer lattice. -/
theorem separated_int_weight_le_fourier_weight (k : Fin 2 → ℤ) :
    (1 + |(k 0 : ℝ)|) * (1 + |(k 1 : ℝ)|) ≤ 1 + fourierEigenvalue k := by
  have h0 := abs_intCast_le_sq (k 0)
  have h1 := abs_intCast_le_sq (k 1)
  have hab : |(k 0 : ℝ)| * |(k 1 : ℝ)| ≤ (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(k 0 : ℝ)| - |(k 1 : ℝ)|),
      sq_abs (k 0 : ℝ), sq_abs (k 1 : ℝ), sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
  have hπ : 2 ≤ 4 * π ^ 2 := by nlinarith [Real.pi_gt_three]
  have he : fourierEigenvalue k =
      4 * π ^ 2 * ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) := by
    unfold fourierEigenvalue euclNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [intVec, Fin.sum_univ_two]
  rw [he]
  nlinarith [mul_nonneg (sub_nonneg.2 hπ)
    (add_nonneg (sq_nonneg (k 0 : ℝ)) (sq_nonneg (k 1 : ℝ)))]

/-- The actual two-dimensional inhomogeneous Fourier weight is summable
at every exponent strictly larger than the dimensional threshold one. -/
theorem summable_fourier_weight_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable (fun k : Fin 2 → ℤ => (1 + fourierEigenvalue k) ^ (-s)) := by
  have h1 := summable_one_add_abs_int_rpow hs
  have hp : Summable (fun p : ℤ × ℤ =>
      (1 + |(p.1 : ℝ)|) ^ (-s) * (1 + |(p.2 : ℝ)|) ^ (-s)) :=
    h1.mul_of_nonneg h1 (fun _ => Real.rpow_nonneg (by positivity) _)
      (fun _ => Real.rpow_nonneg (by positivity) _)
  have hcomp : Summable ((fun p : ℤ × ℤ =>
      (1 + |(p.1 : ℝ)|) ^ (-s) * (1 + |(p.2 : ℝ)|) ^ (-s)) ∘ finTwoArrowEquiv ℤ) :=
    (finTwoArrowEquiv ℤ).summable_iff.mpr hp
  have hsep : Summable (fun k : Fin 2 → ℤ =>
      (1 + |(k 0 : ℝ)|) ^ (-s) * (1 + |(k 1 : ℝ)|) ^ (-s)) := by
    apply hcomp.congr
    intro k
    rfl
  apply hsep.of_nonneg_of_le
  · intro k
    exact Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  · intro k
    calc
      (1 + fourierEigenvalue k) ^ (-s) ≤
          ((1 + |(k 0 : ℝ)|) * (1 + |(k 1 : ℝ)|)) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (separated_int_weight_le_fourier_weight k) (by linarith)
      _ = _ := Real.mul_rpow (by positivity) (by positivity)

/-- The actual lattice kernel and Cauchy--Schwarz turn square-summable
inhomogeneous `H¹` coefficients into negatively weighted `ℓ¹` coefficients,
with every strictly positive loss and an explicit bound. -/
theorem fourier_weighted_l1_of_h1 {a : (Fin 2 → ℤ) → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (ha : Summable (fun k => (1 + fourierEigenvalue k) * ‖a k‖ ^ 2)) :
    Summable (fun k => ‖a k‖ * (1 + fourierEigenvalue k) ^ (-δ / 2)) ∧
      (∑' k, ‖a k‖ * (1 + fourierEigenvalue k) ^ (-δ / 2)) ≤
        Real.sqrt (∑' k, (1 + fourierEigenvalue k) * ‖a k‖ ^ 2) *
          Real.sqrt (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ))) := by
  let E : (Fin 2 → ℤ) → ℝ := fun k => (1 + fourierEigenvalue k) * ‖a k‖ ^ 2
  let W : (Fin 2 → ℤ) → ℝ := fun k => (1 + fourierEigenvalue k) ^ (-(1 + δ))
  have hE : ∀ k, 0 ≤ E k := fun k => mul_nonneg
    (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)
  have hW : ∀ k, 0 ≤ W k := fun k => Real.rpow_nonneg
    (by positivity [fourierEigenvalue_nonneg k]) _
  have hWs : Summable W := summable_fourier_weight_rpow_neg (by linarith : 1 < 1 + δ)
  have hproduct (k : Fin 2 → ℤ) :
      Real.sqrt (E k) * Real.sqrt (W k) = ‖a k‖ * (1 + fourierEigenvalue k) ^ (-δ / 2) := by
    let b := 1 + fourierEigenvalue k
    have hb : 0 < b := by dsimp [b]; positivity [fourierEigenvalue_nonneg k]
    have hpower : Real.sqrt b * Real.sqrt (b ^ (-(1 + δ))) = b ^ (-δ / 2) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hb.le,
        ← Real.rpow_add hb]
      congr 1
      ring
    change Real.sqrt (b * ‖a k‖ ^ 2) * Real.sqrt (b ^ (-(1 + δ))) = _
    rw [Real.sqrt_mul hb.le, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      Real.sqrt b * ‖a k‖ * Real.sqrt (b ^ (-(1 + δ))) =
          ‖a k‖ * (Real.sqrt b * Real.sqrt (b ^ (-(1 + δ)))) := by ring
      _ = _ := by rw [hpower]
  have hbound (S : Finset (Fin 2 → ℤ)) :
      ∑ k ∈ S, ‖a k‖ * (1 + fourierEigenvalue k) ^ (-δ / 2) ≤
        Real.sqrt (∑' k, E k) * Real.sqrt (∑' k, W k) := by
    calc
      _ = ∑ k ∈ S, Real.sqrt (E k) * Real.sqrt (W k) :=
        Finset.sum_congr rfl (fun k _ => (hproduct k).symm)
      _ ≤ Real.sqrt (∑ k ∈ S, E k) * Real.sqrt (∑ k ∈ S, W k) :=
        Real.sum_sqrt_mul_sqrt_le S hE hW
      _ ≤ _ := mul_le_mul
        (Real.sqrt_le_sqrt (ha.sum_le_tsum S (fun k _ => hE k)))
        (Real.sqrt_le_sqrt (hWs.sum_le_tsum S (fun k _ => hW k)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hn : ∀ k : Fin 2 → ℤ,
      0 ≤ ‖a k‖ * (1 + fourierEigenvalue k) ^ (-δ / 2) := fun k =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
      (by positivity [fourierEigenvalue_nonneg k]) _)
  exact ⟨summable_of_sum_le hn hbound, Real.tsum_le_of_sum_le hn hbound⟩

/-- The actual Galerkin velocity limit has uniform negatively weighted `ℓ¹`
Fourier coefficients for every positive loss, proved from its existing
kinetic and gradient energies. -/
theorem phaseGalerkin_l2_limit_weighted_l1
    (ν : ℝ) (hν : 0 < ν) (phase : Phase) {φ : ℕ → ℕ}
    {U : GalerkinTime →ᵇ TorusVelocityL2}
    (hU : Tendsto (fun n => phaseGalerkinL2Curve ν hν phase (φ n)) atTop (𝓝 U))
    (t : GalerkinTime) (i : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun k => ‖l2FourierCoeff k i (U t)‖ *
      (1 + fourierEigenvalue k) ^ (-δ / 2)) ∧
      (∑' k, ‖l2FourierCoeff k i (U t)‖ * (1 + fourierEigenvalue k) ^ (-δ / 2)) ≤
        Real.sqrt (phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase) *
          Real.sqrt (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(1 + δ))) := by
  obtain ⟨hE, hEb, hG, hGb⟩ :=
    phaseGalerkin_l2_limit_fourier_sobolev_energy ν hν phase hU t
  have hsum : Summable (fun k => (1 + fourierEigenvalue k) * l2VelocityFourierEnergy (U t) k) := by
    simpa only [add_mul, one_mul] using hE.add hG
  have hpoint : ∀ k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2 ≤
      (1 + fourierEigenvalue k) * l2VelocityFourierEnergy (U t) k := fun k =>
    mul_le_mul_of_nonneg_left (l2FourierCoeff_sq_le_energy (U t) k i)
      (by positivity [fourierEigenvalue_nonneg k])
  have hcomponent : Summable (fun k => (1 + fourierEigenvalue k) *
      ‖l2FourierCoeff k i (U t)‖ ^ 2) :=
    hsum.of_nonneg_of_le (fun k => mul_nonneg
      (by positivity [fourierEigenvalue_nonneg k]) (sq_nonneg _)) hpoint
  obtain ⟨hs, hb⟩ := fourier_weighted_l1_of_h1 hδ hcomponent
  have henergy : (∑' k, (1 + fourierEigenvalue k) * ‖l2FourierCoeff k i (U t)‖ ^ 2) ≤
      phaseGalerkinEnergyBound phase + phaseGalerkinGradientBound ν phase := by
    calc
      _ ≤ ∑' k, (1 + fourierEigenvalue k) * l2VelocityFourierEnergy (U t) k :=
        Summable.tsum_le_tsum hpoint hcomponent hsum
      _ = (∑' k, l2VelocityFourierEnergy (U t) k) +
          ∑' k, fourierEigenvalue k * l2VelocityFourierEnergy (U t) k := by
        simp only [add_mul, one_mul]
        exact hE.tsum_add hG
      _ ≤ _ := add_le_add hEb hGb
  exact ⟨hs, hb.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt henergy)
    (Real.sqrt_nonneg _))⟩

end AnomDiss
