module

public import RequestProject.FourierPolynomial
public import RequestProject.HeatCalc
public import RequestProject.ScalarHeatFractionalSmoothing
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Actual spatial reconstruction of absolutely summable Fourier series

The reconstructed function is the genuine character series on the covering
space. Summable coefficients give a bounded continuous periodic function;
a summable first frequency moment gives its actual continuous Fréchet
derivative and its true unit-torus partial derivative series.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

def complexFourierSeriesTerm (a : (Fin 2 → ℤ) → ℂ) (k : Fin 2 → ℤ) (x : Pt 2) : ℂ :=
  a k * expChar (intVec k) x

def complexFourierSeries (a : (Fin 2 → ℤ) → ℂ) (x : Pt 2) : ℂ :=
  ∑' k, complexFourierSeriesTerm a k x

lemma contDiff_complexFourierSeriesTerm (a : (Fin 2 → ℤ) → ℂ) (k : Fin 2 → ℤ) :
    ContDiff ℝ ∞ (complexFourierSeriesTerm a k) :=
  contDiff_const.mul (contDiff_expChar (intVec k))

@[simp] lemma norm_complexFourierSeriesTerm (a : (Fin 2 → ℤ) → ℂ)
    (k : Fin 2 → ℤ) (x : Pt 2) : ‖complexFourierSeriesTerm a k x‖ = ‖a k‖ := by
  simp only [complexFourierSeriesTerm, norm_mul, norm_expChar, mul_one]

/-- The coefficient series converges at every spatial point. -/
theorem summable_complexFourierSeriesTerm {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (x : Pt 2) :
    Summable (fun k => complexFourierSeriesTerm a k x) :=
  ha.of_norm_bounded (fun k => (norm_complexFourierSeriesTerm a k x).le)

theorem continuous_complexFourierSeries {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) : Continuous (complexFourierSeries a) := by
  exact continuous_tsum
    (fun k => (contDiff_complexFourierSeriesTerm a k).continuous) ha
    (fun k x => (norm_complexFourierSeriesTerm a k x).le)

theorem norm_complexFourierSeries_le {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (x : Pt 2) :
    ‖complexFourierSeries a x‖ ≤ ∑' k, ‖a k‖ := by
  have hn : Summable (fun k => ‖complexFourierSeriesTerm a k x‖) := by
    simpa only [norm_complexFourierSeriesTerm] using ha
  simpa only [complexFourierSeries, norm_complexFourierSeriesTerm] using
    norm_tsum_le_tsum_norm hn

theorem isPeriodic_complexFourierSeries (a : (Fin 2 → ℤ) → ℂ) :
    IsPeriodic (complexFourierSeries a) := by
  intro x m
  apply tsum_congr
  intro k
  simp only [complexFourierSeriesTerm, isPeriodic_expChar k x m]

/-- Each differentiated mode contains the full physical multiplier
`2π i k_j` for the unit-period torus. -/
lemma pd_complexFourierSeriesTerm (a : (Fin 2 → ℤ) → ℂ)
    (k : Fin 2 → ℤ) (j : Fin 2) (x : Pt 2) :
    pd j (complexFourierSeriesTerm a k) x =
      (2 * π * Complex.I * (k j : ℂ)) * a k * expChar (intVec k) x := by
  change pd j (fun y => a k * expChar (intVec k) y) x = _
  rw [pd_mul_const_complex _ _ j
    ((contDiff_expChar _).differentiable (by simp))]
  dsimp only
  rw [pd_expChar]
  simp only [intVec, Complex.ofReal_intCast]
  ring

lemma norm_pd_complexFourierSeriesTerm_le (a : (Fin 2 → ℤ) → ℂ)
    (k : Fin 2 → ℤ) (j : Fin 2) (x : Pt 2) :
    ‖pd j (complexFourierSeriesTerm a k) x‖ ≤
      ‖(2 * π * Complex.I : ℂ)‖ * (‖intVec k‖ * ‖a k‖) := by
  have hk : ‖(k j : ℂ)‖ ≤ ‖intVec k‖ := by
    simpa only [Complex.norm_intCast, ← Real.norm_eq_abs, intVec] using
      norm_le_pi_norm (intVec k) j
  rw [pd_complexFourierSeriesTerm]
  rw [norm_mul, norm_expChar, mul_one, norm_mul, norm_mul]
  calc
    ‖(2 * π * Complex.I : ℂ)‖ * ‖(k j : ℂ)‖ * ‖a k‖ ≤
        ‖(2 * π * Complex.I : ℂ)‖ * ‖intVec k‖ * ‖a k‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

lemma norm_fderiv_complexFourierSeriesTerm_le (a : (Fin 2 → ℤ) → ℂ)
    (k : Fin 2 → ℤ) (x : Pt 2) :
    ‖fderiv ℝ (complexFourierSeriesTerm a k) x‖ ≤
      (2 * ‖(2 * π * Complex.I : ℂ)‖) * (‖intVec k‖ * ‖a k‖) := by
  have h := norm_clm_pt2_le (fderiv ℝ (complexFourierSeriesTerm a k) x)
  change ‖fderiv ℝ (complexFourierSeriesTerm a k) x‖ ≤
    ‖pd 0 (complexFourierSeriesTerm a k) x‖ +
      ‖pd 1 (complexFourierSeriesTerm a k) x‖ at h
  exact (h.trans (add_le_add (norm_pd_complexFourierSeriesTerm_le a k 0 x)
    (norm_pd_complexFourierSeriesTerm_le a k 1 x))).trans_eq (by ring)

theorem summable_fderiv_complexFourierSeriesTerm {a : (Fin 2 → ℤ) → ℂ}
    (hd : Summable (fun k => ‖intVec k‖ * ‖a k‖)) (x : Pt 2) :
    Summable (fun k => fderiv ℝ (complexFourierSeriesTerm a k) x) :=
  (hd.mul_left (2 * ‖(2 * π * Complex.I : ℂ)‖)).of_norm_bounded
    (fun k => norm_fderiv_complexFourierSeriesTerm_le a k x)

/-- The derivative is derived from the actual summable series. -/
theorem hasFDerivAt_complexFourierSeries {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖))
    (hd : Summable (fun k => ‖intVec k‖ * ‖a k‖)) (x : Pt 2) :
    HasFDerivAt (complexFourierSeries a)
      (∑' k, fderiv ℝ (complexFourierSeriesTerm a k) x) x := by
  apply hasFDerivAt_tsum (hd.mul_left (2 * ‖(2 * π * Complex.I : ℂ)‖))
    (fun k y => ((contDiff_complexFourierSeriesTerm a k).differentiable (by simp) y).hasFDerivAt)
    (fun k y => norm_fderiv_complexFourierSeriesTerm_le a k y)
    (summable_complexFourierSeriesTerm ha (0 : Pt 2))

/-- A finite first frequency moment gives true `C¹` regularity of the
reconstructed field, rather than a formal derivative series alone. -/
theorem contDiff_one_complexFourierSeries {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖))
    (hd : Summable (fun k => ‖intVec k‖ * ‖a k‖)) :
    ContDiff ℝ 1 (complexFourierSeries a) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_complexFourierSeries ha hd x).differentiableAt, ?_⟩
  have he : fderiv ℝ (complexFourierSeries a) =
      fun x => ∑' k, fderiv ℝ (complexFourierSeriesTerm a k) x :=
    funext fun x => (hasFDerivAt_complexFourierSeries ha hd x).fderiv
  rw [he]
  exact continuous_tsum
    (fun k => ((contDiff_complexFourierSeriesTerm a k).of_le
      (natCast_le_infty 1)).continuous_fderiv one_ne_zero)
    (hd.mul_left (2 * ‖(2 * π * Complex.I : ℂ)‖))
    (fun k x => norm_fderiv_complexFourierSeriesTerm_le a k x)

/-- The genuine spatial partial is exactly the absolutely convergent
physical derivative character series. -/
theorem pd_complexFourierSeries {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖))
    (hd : Summable (fun k => ‖intVec k‖ * ‖a k‖)) (j : Fin 2) (x : Pt 2) :
    pd j (complexFourierSeries a) x =
      ∑' k, (2 * π * Complex.I * (k j : ℂ)) * a k * expChar (intVec k) x := by
  unfold pd
  rw [(hasFDerivAt_complexFourierSeries ha hd x).fderiv]
  change ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℝ) : Pt 2)
      (∑' k, fderiv ℝ (complexFourierSeriesTerm a k) x) = _
  rw [(ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℝ) : Pt 2)).map_tsum
    (summable_fderiv_complexFourierSeriesTerm hd x)]
  apply tsum_congr
  intro k
  exact pd_complexFourierSeriesTerm a k j x

theorem summable_pd_complexFourierSeries {a : (Fin 2 → ℤ) → ℂ}
    (hd : Summable (fun k => ‖intVec k‖ * ‖a k‖)) (j : Fin 2) (x : Pt 2) :
    Summable (fun k => (2 * π * Complex.I * (k j : ℂ)) * a k * expChar (intVec k) x) := by
  have hs := (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℝ) : Pt 2)).summable
    (summable_fderiv_complexFourierSeriesTerm hd x)
  exact hs.congr (fun k => pd_complexFourierSeriesTerm a k j x)

/-- An explicit global character Hölder bound, including the zero mode. -/
lemma expChar_intVec_holder {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (k : Fin 2 → ℤ) (x y : Pt 2) :
    ‖expChar (intVec k) x - expChar (intVec k) y‖ ≤
      (2 ^ (1 - β) * (2 * ‖(2 * π * Complex.I : ℂ)‖) ^ β) *
        (1 + ‖intVec k‖) ^ β * ‖x - y‖ ^ β := by
  let D : ℝ := 2 * ‖(2 * π * Complex.I : ℂ)‖
  let W : ℝ := 1 + ‖intVec k‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hfd : ∀ z, ‖fderiv ℝ (expChar (intVec k)) z‖ ≤ D * W := by
    intro z
    have h := norm_fderiv_complexFourierSeriesTerm_le (fun _ => 1) k z
    have he : complexFourierSeriesTerm (fun _ => 1) k = expChar (intVec k) := by
      funext v
      simp only [complexFourierSeriesTerm, one_mul]
    rw [he] at h
    calc
      _ ≤ D * ‖intVec k‖ := by simpa only [norm_one, mul_one, D] using h
      _ ≤ D * W := mul_le_mul_of_nonneg_left
        (show ‖intVec k‖ ≤ W by change ‖intVec k‖ ≤ 1 + ‖intVec k‖; linarith) hD
  have hA : ‖expChar (intVec k) x - expChar (intVec k) y‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by simp only [norm_expChar]; norm_num)
  have hB : ‖expChar (intVec k) x - expChar (intVec k) y‖ ≤ D * W * ‖x-y‖ :=
    (convex_univ : Convex ℝ (univ : Set (Pt 2))).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (contDiff_expChar _).differentiable (by simp) z)
      (fun z _ => hfd z) (mem_univ y) (mem_univ x)
  apply (le_rpow_interpolation (norm_nonneg _) hA hB hβ₀ hβ₁).trans_eq
  rw [Real.mul_rpow (mul_nonneg hD hW) (norm_nonneg _), Real.mul_rpow hD hW]
  dsimp [D, W]
  ring

def fourierSeriesDerivativeHolderConstant (β : ℝ) : ℝ :=
  ‖(2 * π * Complex.I : ℂ)‖ *
    (2 ^ (1 - β) * (2 * ‖(2 * π * Complex.I : ℂ)‖) ^ β)

theorem fourierSeriesDerivativeHolderConstant_nonneg (β : ℝ) :
    0 ≤ fourierSeriesDerivativeHolderConstant β := by
  unfold fourierSeriesDerivativeHolderConstant
  positivity

/-- A summable `(1+|k|)^(1+β)` moment gives true `C¹` regularity and
an explicit common β-Hölder bound for both actual spatial partials. -/
theorem contDiff_one_and_pd_holder_complexFourierSeries_quantitative
    {a : (Fin 2 → ℤ) → ℂ} {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hm : Summable (fun k => (1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖)) :
    ContDiff ℝ 1 (complexFourierSeries a) ∧
      ∀ j x y,
        ‖pd j (complexFourierSeries a) x - pd j (complexFourierSeries a) y‖ ≤
          (fourierSeriesDerivativeHolderConstant β *
            (∑' k, (1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖)) * ‖x-y‖ ^ β := by
  have hW (k : Fin 2 → ℤ) : 1 ≤ 1 + ‖intVec k‖ := by linarith [norm_nonneg (intVec k)]
  have hpow (k : Fin 2 → ℤ) : 1 + ‖intVec k‖ ≤ (1 + ‖intVec k‖) ^ (1 + β) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hW k) (show (1 : ℝ) ≤ 1 + β by linarith)
  have ha : Summable (fun k => ‖a k‖) := hm.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by
    calc
      ‖a k‖ = 1 * ‖a k‖ := by ring
      _ ≤ (1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖ :=
        mul_le_mul_of_nonneg_right ((hW k).trans (hpow k)) (norm_nonneg _))
  have hd : Summable (fun k => ‖intVec k‖ * ‖a k‖) :=
    hm.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun k =>
      mul_le_mul_of_nonneg_right ((by linarith : ‖intVec k‖ ≤ 1 + ‖intVec k‖).trans
        (hpow k)) (norm_nonneg _))
  refine ⟨contDiff_one_complexFourierSeries ha hd, ?_⟩
  let C : ℝ := ‖(2 * π * Complex.I : ℂ)‖
  let K : ℝ := 2 ^ (1 - β) * (2 * C) ^ β
  let M : ℝ := ∑' k, (1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖
  have hC : 0 ≤ C := norm_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change ∀ j x y,
    ‖pd j (complexFourierSeries a) x - pd j (complexFourierSeries a) y‖ ≤
      (C * K * M) * ‖x-y‖ ^ β
  intro j x y
  have hsx := summable_pd_complexFourierSeries hd j x
  have hsy := summable_pd_complexFourierSeries hd j y
  rw [pd_complexFourierSeries ha hd, pd_complexFourierSeries ha hd, ← hsx.tsum_sub hsy]
  have hb : ∀ k : Fin 2 → ℤ,
      ‖(2 * π * Complex.I * (k j : ℂ)) * a k * expChar (intVec k) x -
        (2 * π * Complex.I * (k j : ℂ)) * a k * expChar (intVec k) y‖ ≤
      (C * K * ‖x-y‖ ^ β) * ((1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖) := by
    intro k
    have hk₀ : ‖(k j : ℂ)‖ ≤ ‖intVec k‖ := by
      simpa only [Complex.norm_intCast, ← Real.norm_eq_abs, intVec] using
        norm_le_pi_norm (intVec k) j
    have hk : ‖(k j : ℂ)‖ ≤ 1 + ‖intVec k‖ := hk₀.trans (by linarith)
    have hc := expChar_intVec_holder hβ₀ hβ₁ k x y
    change _ ≤ K * (1 + ‖intVec k‖) ^ β * ‖x-y‖ ^ β at hc
    rw [← mul_sub, norm_mul, norm_mul, norm_mul]
    calc
      C * ‖(k j : ℂ)‖ * ‖a k‖ *
          ‖expChar (intVec k) x - expChar (intVec k) y‖ ≤
          C * (1 + ‖intVec k‖) * ‖a k‖ *
            (K * (1 + ‖intVec k‖) ^ β * ‖x-y‖ ^ β) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC) (norm_nonneg _))
          hc (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [Real.rpow_add (by positivity : 0 < 1 + ‖intVec k‖), Real.rpow_one]
        ring
  have hh := tsum_of_norm_bounded (hm.mul_left (C * K * ‖x-y‖ ^ β)).hasSum hb
  exact hh.trans_eq (by rw [tsum_mul_left]; dsimp [M]; ring)

/-- The quantitative estimate can be used uniformly in another parameter
when the same coefficient moment bound holds throughout that parameter. -/
theorem pd_holder_complexFourierSeries_of_moment_bound
    {a : (Fin 2 → ℤ) → ℂ} {β B : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hm : Summable (fun k => (1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖))
    (hB : (∑' k, (1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖) ≤ B)
    (j : Fin 2) (x y : Pt 2) :
    ‖pd j (complexFourierSeries a) x - pd j (complexFourierSeries a) y‖ ≤
      (fourierSeriesDerivativeHolderConstant β * B) * ‖x-y‖ ^ β := by
  exact ((contDiff_one_and_pd_holder_complexFourierSeries_quantitative hβ₀ hβ₁ hm).2 j x y).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB (fourierSeriesDerivativeHolderConstant_nonneg β))
      (Real.rpow_nonneg (norm_nonneg _) _))

/-- A summable `(1+|k|)^(1+β)` moment gives true `C¹` regularity and
a single global β-Hölder bound for both actual spatial partials. -/
theorem contDiff_one_and_pd_holder_complexFourierSeries
    {a : (Fin 2 → ℤ) → ℂ} {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hm : Summable (fun k => (1 + ‖intVec k‖) ^ (1 + β) * ‖a k‖)) :
    ContDiff ℝ 1 (complexFourierSeries a) ∧
      ∃ H, 0 ≤ H ∧ ∀ j x y,
        ‖pd j (complexFourierSeries a) x - pd j (complexFourierSeries a) y‖ ≤
          H * ‖x-y‖ ^ β := by
  obtain ⟨hc, hh⟩ := contDiff_one_and_pd_holder_complexFourierSeries_quantitative hβ₀ hβ₁ hm
  exact ⟨hc, _, mul_nonneg (fourierSeriesDerivativeHolderConstant_nonneg β)
    (tsum_nonneg fun k => by positivity), hh⟩

end AnomDiss
