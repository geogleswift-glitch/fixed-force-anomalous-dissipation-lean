module

public import RequestProject.FourierSobolevProduct

/-!
# The actual two-dimensional Sobolev convolution algebra

Above the dimensional threshold, genuine square-summable Fourier energy
gives absolute coefficient summability. The true infinite convolution
preserves the same energy exponent, with an explicit lattice constant.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 1200000

/-- The genuine lattice kernel gives a weighted absolute-summability
embedding whenever the Sobolev exponent exceeds the moment by more than one. -/
theorem fourier_weighted_l1_of_sobolev {a : (Fin 2 → ℤ) → ℂ} {r q : ℝ}
    (hgap : 1 < r - q)
    (ha : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2)) :
    Summable (fun k => fourierSobolevWeight k ^ q * ‖a k‖) ∧
      (∑' k, fourierSobolevWeight k ^ q * ‖a k‖) ≤
        Real.sqrt (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2) *
          Real.sqrt (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(r - q))) := by
  let E := fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2
  let K := fun k : Fin 2 → ℤ => (1 + fourierEigenvalue k) ^ (-(r - q))
  have hE : ∀ k, 0 ≤ E k := fun k => mul_nonneg
    (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hK : ∀ k, 0 ≤ K k := fun k =>
    Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  have hKs : Summable K := summable_fourier_weight_rpow_neg hgap
  have hproduct (k : Fin 2 → ℤ) :
      Real.sqrt (E k) * Real.sqrt (K k) = fourierSobolevWeight k ^ q * ‖a k‖ := by
    let b := 1 + fourierEigenvalue k
    have hb : 0 < b := by dsimp [b]; positivity [fourierEigenvalue_nonneg k]
    have hp : Real.sqrt (b ^ r) * Real.sqrt (b ^ (-(r-q))) = (Real.sqrt b) ^ q := by
      simp_rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hb.le]
      rw [← Real.rpow_add hb]
      congr 1
      ring
    change Real.sqrt (b ^ r * ‖a k‖ ^ 2) * Real.sqrt (b ^ (-(r-q))) = _
    rw [Real.sqrt_mul (Real.rpow_nonneg hb.le _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    calc
      _ = (Real.sqrt (b ^ r) * Real.sqrt (b ^ (-(r-q)))) * ‖a k‖ := by ring
      _ = _ := by rw [hp]; rfl
  have hbound (S : Finset (Fin 2 → ℤ)) :
      ∑ k ∈ S, fourierSobolevWeight k ^ q * ‖a k‖ ≤
        Real.sqrt (∑' k, E k) * Real.sqrt (∑' k, K k) := by
    calc
      _ = ∑ k ∈ S, Real.sqrt (E k) * Real.sqrt (K k) :=
        Finset.sum_congr rfl (fun k _ => (hproduct k).symm)
      _ ≤ Real.sqrt (∑ k ∈ S, E k) * Real.sqrt (∑ k ∈ S, K k) :=
        Real.sum_sqrt_mul_sqrt_le S hE hK
      _ ≤ _ := mul_le_mul
        (Real.sqrt_le_sqrt (ha.sum_le_tsum S (fun k _ => hE k)))
        (Real.sqrt_le_sqrt (hKs.sum_le_tsum S (fun k _ => hK k)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hn : ∀ k, 0 ≤ fourierSobolevWeight k ^ q * ‖a k‖ := fun k =>
    mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _)
  exact ⟨summable_of_sum_le hn hbound, Real.tsum_le_of_sum_le hn hbound⟩

/-- The covering-space frequency moment used by actual Fourier series
reconstruction is controlled by the true unit-torus Laplace weight. -/
theorem one_add_norm_intVec_le_fourier_weight (k : Fin 2 → ℤ) :
    1 + ‖intVec k‖ ≤ 2 * fourierSobolevWeight k := by
  have hcoef : 1 ≤ 4 * π ^ 2 := by nlinarith [Real.pi_gt_three]
  have he := fourierSobolevWeight_sq k
  unfold fourierEigenvalue at he
  have hmul : 0 ≤ (4 * π ^ 2 - 1) * euclNorm (intVec k) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hcoef) (sq_nonneg _)
  have heu : euclNorm (intVec k) ≤ fourierSobolevWeight k := by
    nlinarith [euclNorm_nonneg (intVec k), fourierSobolevWeight_nonneg k]
  have hn := (norm_le_euclNorm (intVec k)).trans heu
  linarith [one_le_fourierSobolevWeight k]

/-- Direct absolute moments for the actual covering-space character
series, including the constant in the reconstruction weight. -/
theorem fourier_covering_weighted_l1_of_sobolev
    {a : (Fin 2 → ℤ) → ℂ} {r q : ℝ} (hq : 0 ≤ q) (hgap : 1 < r-q)
    (ha : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2)) :
    Summable (fun k => (1 + ‖intVec k‖) ^ q * ‖a k‖) ∧
      (∑' k, (1 + ‖intVec k‖) ^ q * ‖a k‖) ≤
        2 ^ q * (Real.sqrt (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2) *
          Real.sqrt (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-(r-q)))) := by
  obtain ⟨hs, hb⟩ := fourier_weighted_l1_of_sobolev hgap ha
  have hterm (k : Fin 2 → ℤ) :
      (1 + ‖intVec k‖) ^ q * ‖a k‖ ≤ 2 ^ q * (fourierSobolevWeight k ^ q * ‖a k‖) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + ‖intVec k‖)
      (one_add_norm_intVec_le_fourier_weight k) hq
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (fourierSobolevWeight_nonneg k)] at h
    exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (by ring)
  have hresult : Summable (fun k => (1 + ‖intVec k‖) ^ q * ‖a k‖) :=
    (hs.mul_left (2 ^ q)).of_nonneg_of_le (fun k => by positivity) hterm
  refine ⟨hresult, ?_⟩
  calc
    _ ≤ ∑' k, 2 ^ q * (fourierSobolevWeight k ^ q * ‖a k‖) :=
      Summable.tsum_le_tsum hterm hresult (hs.mul_left _)
    _ = 2 ^ q * ∑' k, fourierSobolevWeight k ^ q * ‖a k‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

/-- A uniform Sobolev energy controls coefficient tails by the tail of
the genuinely summable lattice kernel. This is useful for joint
time-space continuity without a pointwise summable coefficient envelope. -/
theorem fourier_l1_tail_bound {a : (Fin 2 → ℤ) → ℂ} {r B : ℝ}
    (hr : 1 < r)
    (ha : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2))
    (hbound : (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2) ≤ B)
    (S : Finset (Fin 2 → ℤ)) :
    (∑' k, if k ∈ S then 0 else ‖a k‖) ≤ Real.sqrt B *
      Real.sqrt (∑' k : Fin 2 → ℤ, if k ∈ S then 0 else (1 + fourierEigenvalue k) ^ (-r)) := by
  classical
  let E := fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2
  let K := fun k : Fin 2 → ℤ => if k ∈ S then 0 else (1 + fourierEigenvalue k) ^ (-r)
  let F := fun k : Fin 2 → ℤ => if k ∈ S then 0 else ‖a k‖
  have hE : ∀ k, 0 ≤ E k := fun k =>
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hK : ∀ k, 0 ≤ K k := by
    intro k
    dsimp [K]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  have hKs : Summable K := (summable_fourier_weight_rpow_neg hr).of_nonneg_of_le hK (fun k => by
    by_cases hk : k ∈ S
    · simpa only [K, if_pos hk] using
        Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k] : 0 ≤ 1 + fourierEigenvalue k) (-r)
    · simpa only [K, if_neg hk] using le_refl ((1 + fourierEigenvalue k) ^ (-r)))
  have hF : ∀ k, 0 ≤ F k := by intro k; dsimp [F]; split_ifs <;> positivity
  have hproduct (k : Fin 2 → ℤ) : Real.sqrt (E k) * Real.sqrt (K k) = F k := by
    by_cases hk : k ∈ S
    · simp only [K, F, if_pos hk, Real.sqrt_zero, mul_zero]
    · dsimp [K, F]
      simp only [if_neg hk]
      let b := 1 + fourierEigenvalue k
      have hb : 0 < b := by dsimp [b]; positivity [fourierEigenvalue_nonneg k]
      have hp : Real.sqrt (b ^ r) * Real.sqrt (b ^ (-r)) = 1 := by
        simp_rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hb.le]
        rw [← Real.rpow_add hb]
        simp only [show r * (1 / 2) + -r * (1 / 2) = 0 by ring, Real.rpow_zero]
      change Real.sqrt (b ^ r * ‖a k‖ ^ 2) * Real.sqrt (b ^ (-r)) = ‖a k‖
      rw [Real.sqrt_mul (Real.rpow_nonneg hb.le _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      calc
        _ = (Real.sqrt (b ^ r) * Real.sqrt (b ^ (-r))) * ‖a k‖ := by ring
        _ = _ := by rw [hp, one_mul]
  have hfinite (T : Finset (Fin 2 → ℤ)) :
      ∑ k ∈ T, F k ≤ Real.sqrt B * Real.sqrt (∑' k, K k) := by
    calc
      _ = ∑ k ∈ T, Real.sqrt (E k) * Real.sqrt (K k) :=
        Finset.sum_congr rfl (fun k _ => (hproduct k).symm)
      _ ≤ Real.sqrt (∑ k ∈ T, E k) * Real.sqrt (∑ k ∈ T, K k) :=
        Real.sum_sqrt_mul_sqrt_le T hE hK
      _ ≤ _ := mul_le_mul
        (Real.sqrt_le_sqrt ((ha.sum_le_tsum T (fun k _ => hE k)).trans hbound))
        (Real.sqrt_le_sqrt (hKs.sum_le_tsum T (fun k _ => hK k)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact Real.tsum_le_of_sum_le hF hfinite

/-- The inhomogeneous square-root Laplace weight is subadditive up to the
explicit factor needed for every nonnegative power. -/
theorem fourierSobolevWeight_power_add_bound (k l : Fin 2 → ℤ) {r : ℝ}
    (hr : 0 ≤ r) :
    fourierSobolevWeight (k+l) ^ r ≤ 2 ^ r *
      (fourierSobolevWeight k ^ r + fourierSobolevWeight l ^ r) := by
  have h := Real.rpow_le_rpow (fourierSobolevWeight_nonneg _)
    (fourierSobolevWeight_add_le k l) hr
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    ((fourierSobolevWeight_nonneg k).trans (le_max_left _ _))] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total (fourierSobolevWeight k) (fourierSobolevWeight l) with hkl | hlk
  · rw [max_eq_right hkl]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _)
  · rw [max_eq_left hlk]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (fourierSobolevWeight_nonneg l) _)

private def algebraSubEquiv (k : Fin 2 → ℤ) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun l := k-l
  invFun l := k-l
  left_inv l := by dsimp; abel
  right_inv l := by dsimp; abel

/-- The genuine infinite Fourier convolution is an `H^r` algebra for `r>1`
on the two-dimensional unit torus. Absolute convergence is part of the
conclusion and the constant is a proved finite lattice-kernel sum. -/
theorem fourier_sobolev_convolution_algebra
    (a b : (Fin 2 → ℤ) → ℂ) {r : ℝ} (hr : 1 < r)
    (ha : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2))
    (hb : Summable (fun k => (1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2)) :
    (∀ k, Summable (fun l => ‖a l * b (k-l)‖)) ∧
    Summable (fun k => (1 + fourierEigenvalue k) ^ r *
      ‖∑' l, a l * b (k-l)‖ ^ 2) ∧
    (∑' k, (1 + fourierEigenvalue k) ^ r * ‖∑' l, a l * b (k-l)‖ ^ 2) ≤
      4 * (2 ^ r) ^ 2 *
        (∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-r)) *
        (∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2) *
        (∑' k, (1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2) := by
  let Apos := fun k => fourierSobolevWeight k ^ r * ‖a k‖
  let Bpos := fun k => fourierSobolevWeight k ^ r * ‖b k‖
  let A := fun k => ‖a k‖
  let B := fun k => ‖b k‖
  let Ea := ∑' k, (1 + fourierEigenvalue k) ^ r * ‖a k‖ ^ 2
  let Eb := ∑' k, (1 + fourierEigenvalue k) ^ r * ‖b k‖ ^ 2
  let K := ∑' k : Fin 2 → ℤ, (1 + fourierEigenvalue k) ^ (-r)
  let C : ℝ := 2 ^ r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAp : ∀ k, 0 ≤ Apos k := fun k =>
    mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _)
  have hBp : ∀ k, 0 ≤ Bpos k := fun k =>
    mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _)
  have hA : ∀ k, 0 ≤ A k := fun k => norm_nonneg _
  have hB : ∀ k, 0 ≤ B k := fun k => norm_nonneg _
  have hAs : Summable (fun k => Apos k ^ 2) := by
    simpa only [Apos, fourierSobolevWeight_fractional_energy_eq] using ha
  have hBs : Summable (fun k => Bpos k ^ 2) := by
    simpa only [Bpos, fourierSobolevWeight_fractional_energy_eq] using hb
  have hAe : (∑' k, Apos k ^ 2) = Ea := by
    simp only [Ea, Apos, fourierSobolevWeight_fractional_energy_eq]
  have hBe : (∑' k, Bpos k ^ 2) = Eb := by
    simp only [Eb, Bpos, fourierSobolevWeight_fractional_energy_eq]
  obtain ⟨hAl1, hAbound⟩ := fourier_weighted_l1_of_sobolev (a := a) (q := 0)
    (by simpa only [sub_zero] using hr) ha
  obtain ⟨hBl1, hBbound⟩ := fourier_weighted_l1_of_sobolev (a := b) (q := 0)
    (by simpa only [sub_zero] using hr) hb
  have hAl1 : Summable A := by simpa only [Real.rpow_zero, one_mul, A] using hAl1
  have hBl1 : Summable B := by simpa only [Real.rpow_zero, one_mul, B] using hBl1
  have hAb : (∑' k, A k) ≤ Real.sqrt Ea * Real.sqrt K := by
    simpa only [Real.rpow_zero, one_mul, sub_zero, A, Ea, K] using hAbound
  have hBb : (∑' k, B k) ≤ Real.sqrt Eb * Real.sqrt K := by
    simpa only [Real.rpow_zero, one_mul, sub_zero, B, Eb, K] using hBbound
  obtain ⟨hconv1, hsq1, hb1⟩ := discrete_young_l2_l1_nonneg Apos B hAp hB hAs hBl1
  obtain ⟨hconv2, hsq2, hb2⟩ := discrete_young_l2_l1_nonneg Bpos A hBp hA hBs hAl1
  let C1 := fun k => ∑' l, Apos l * B (k-l)
  let C2 := fun k => ∑' l, Bpos l * A (k-l)
  have hC1 : ∀ k, 0 ≤ C1 k := fun k => tsum_nonneg fun l => mul_nonneg (hAp l) (hB _)
  have hC2 : ∀ k, 0 ≤ C2 k := fun k => tsum_nonneg fun l => mul_nonneg (hBp l) (hA _)
  have hrev (k : Fin 2 → ℤ) : Summable (fun l => A l * Bpos (k-l)) := by
    have hs := (algebraSubEquiv k).summable_iff.mpr (hconv2 k)
    change Summable (fun l => Bpos (k-l) * A (k-(k-l))) at hs
    have he (l : Fin 2 → ℤ) : k-(k-l) = l := by abel
    simpa only [he, mul_comm] using hs
  have hswap (k : Fin 2 → ℤ) : (∑' l, A l * Bpos (k-l)) = C2 k := by
    have hs := (algebraSubEquiv k).tsum_eq (fun l => Bpos l * A (k-l))
    change (∑' l, Bpos (k-l) * A (k-(k-l))) = C2 k at hs
    have he (l : Fin 2 → ℤ) : k-(k-l) = l := by abel
    simpa only [he, mul_comm] using hs
  have hterm (k l : Fin 2 → ℤ) :
      fourierSobolevWeight k ^ r * ‖a l * b (k-l)‖ ≤
        C * (Apos l * B (k-l) + A l * Bpos (k-l)) := by
    have hw := fourierSobolevWeight_power_add_bound l (k-l) (by linarith : 0 ≤ r)
    have he : l+(k-l) = k := by abel
    rw [he] at hw
    apply (mul_le_mul_of_nonneg_right hw (norm_nonneg (a l * b (k-l)))).trans_eq
    simp only [Apos, Bpos, A, B, C, norm_mul]
    ring
  have hdom (k : Fin 2 → ℤ) :
      Summable (fun l => C * (Apos l * B (k-l) + A l * Bpos (k-l))) :=
    ((hconv1 k).add (hrev k)).mul_left C
  have habs (k : Fin 2 → ℤ) : Summable (fun l => ‖a l * b (k-l)‖) := by
    apply (hdom k).of_nonneg_of_le (fun l => norm_nonneg _)
    intro l
    have hw := Real.one_le_rpow (one_le_fourierSobolevWeight k) (by linarith : 0 ≤ r)
    have hn : ‖a l * b (k-l)‖ ≤ fourierSobolevWeight k ^ r * ‖a l * b (k-l)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (a l * b (k-l)))
    exact hn.trans (hterm k l)
  have hpoint (k : Fin 2 → ℤ) :
      fourierSobolevWeight k ^ r * ‖∑' l, a l * b (k-l)‖ ≤ C * (C1 k + C2 k) := by
    calc
      _ ≤ fourierSobolevWeight k ^ r * ∑' l, ‖a l * b (k-l)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (habs k))
          (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _)
      _ = ∑' l, fourierSobolevWeight k ^ r * ‖a l * b (k-l)‖ := tsum_mul_left.symm
      _ ≤ ∑' l, C * (Apos l * B (k-l) + A l * Bpos (k-l)) :=
        Summable.tsum_le_tsum (hterm k) ((habs k).mul_left _) (hdom k)
      _ = _ := by rw [tsum_mul_left, (hconv1 k).tsum_add (hrev k), hswap k]
  have hsquare (k : Fin 2 → ℤ) :
      (fourierSobolevWeight k ^ r * ‖∑' l, a l * b (k-l)‖) ^ 2 ≤
        2 * C ^ 2 * (C1 k ^ 2 + C2 k ^ 2) := by
    have h := (sq_le_sq₀
      (mul_nonneg (Real.rpow_nonneg (fourierSobolevWeight_nonneg k) _) (norm_nonneg _))
      (mul_nonneg hC (add_nonneg (hC1 k) (hC2 k)))).mpr (hpoint k)
    have htwo : (C1 k + C2 k) ^ 2 ≤ 2 * (C1 k ^ 2 + C2 k ^ 2) := by
      nlinarith [sq_nonneg (C1 k-C2 k)]
    calc
      _ ≤ C ^ 2 * (C1 k+C2 k) ^ 2 := by simpa only [mul_pow] using h
      _ ≤ C ^ 2 * (2 * (C1 k ^ 2+C2 k ^ 2)) :=
        mul_le_mul_of_nonneg_left htwo (sq_nonneg C)
      _ = _ := by ring
  have hmajor : Summable (fun k => 2 * C ^ 2 * (C1 k ^ 2+C2 k ^ 2)) :=
    (hsq1.add hsq2).mul_left _
  have hresult : Summable (fun k => (fourierSobolevWeight k ^ r *
      ‖∑' l, a l * b (k-l)‖) ^ 2) :=
    hmajor.of_nonneg_of_le (fun k => sq_nonneg _) hsquare
  have hEa0 : 0 ≤ Ea := tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hEb0 : 0 ≤ Eb := tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _) (sq_nonneg _)
  have hK0 : 0 ≤ K := tsum_nonneg fun k =>
    Real.rpow_nonneg (by positivity [fourierEigenvalue_nonneg k]) _
  have hA2 : (∑' k, A k) ^ 2 ≤ Ea * K := by
    have h := (sq_le_sq₀ (tsum_nonneg hA)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hAb
    simpa only [mul_pow, Real.sq_sqrt hEa0, Real.sq_sqrt hK0] using h
  have hB2 : (∑' k, B k) ^ 2 ≤ Eb * K := by
    have h := (sq_le_sq₀ (tsum_nonneg hB)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hBb
    simpa only [mul_pow, Real.sq_sqrt hEb0, Real.sq_sqrt hK0] using h
  have hbound : (∑' k, (fourierSobolevWeight k ^ r * ‖∑' l, a l * b (k-l)‖) ^ 2) ≤
      4 * C ^ 2 * K * Ea * Eb := by
    rw [hAe] at hb1
    rw [hBe] at hb2
    calc
      _ ≤ ∑' k, 2 * C ^ 2 * (C1 k ^ 2+C2 k ^ 2) :=
        Summable.tsum_le_tsum hsquare hresult hmajor
      _ = 2 * C ^ 2 * ((∑' k, C1 k ^ 2)+∑' k, C2 k ^ 2) := by
        rw [tsum_mul_left, hsq1.tsum_add hsq2]
      _ ≤ 2 * C ^ 2 * ((∑' k, B k) ^ 2 * Ea + (∑' k, A k) ^ 2 * Eb) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by positivity)
      _ ≤ 2 * C ^ 2 * ((Eb*K)*Ea+(Ea*K)*Eb) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right hB2 hEa0) (mul_le_mul_of_nonneg_right hA2 hEb0))
          (by positivity)
      _ = _ := by ring
  refine ⟨habs, ?_, ?_⟩
  · simpa only [fourierSobolevWeight_fractional_energy_eq] using hresult
  · simpa only [fourierSobolevWeight_fractional_energy_eq, C, K, Ea, Eb] using hbound

end AnomDiss
