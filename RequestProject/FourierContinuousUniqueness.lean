module

public import RequestProject.FourierSeriesRegularity
public import RequestProject.PulseAverage

/-!
# Pointwise Fourier uniqueness for continuous periodic functions

Parseval detects the true cell `L²` norm. A zero norm forces a continuous
function to vanish throughout the closed cell, and periodicity transfers
this conclusion to the covering space. Absolutely summable Fourier
coefficients therefore reconstruct the original continuous function.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- A continuous periodic complex function with zero genuine cell square
norm vanishes pointwise, including the boundary of every fundamental cell. -/
theorem periodic_complex_eq_zero_of_integral_norm_sq_eq_zero
    {f : Pt 2 → ℂ} (hf : Continuous f) (hp : IsPeriodic f)
    (hz : (∫ x in cell 2, ‖f x‖ ^ 2) = 0) : f = 0 := by
  let G : Pt 2 → ℝ := fun x => ‖f x‖ ^ 2
  have hG : Continuous G := hf.norm.pow 2
  have hG0 : 0 ≤ G := fun x => sq_nonneg _
  have hae : G =ᵐ[(volume : Measure (Pt 2)).restrict (cell 2)] 0 :=
    (integral_eq_zero_iff_of_nonneg hG0 hG.integrableOn_Icc).1 hz
  have hcell : cell 2 = Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) 1) := by
    simpa [cell] using (Set.pi_univ_Icc (0 : Pt 2) 1).symm
  have hclosure : closure (interior (cell 2)) = cell 2 := by
    rw [hcell, interior_pi_set (Set.finite_univ), closure_pi_set]
    simp only [interior_Icc, closure_Ioo (zero_ne_one' ℝ)]
  have heq : EqOn G 0 (cell 2) := Measure.eqOn_of_ae_eq hae hG.continuousOn
    continuousOn_const (by rw [hclosure])
  have hfcell : ∀ x ∈ cell 2, f x = 0 := by
    intro x hx
    have hs : ‖f x‖ ^ 2 = 0 := heq hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  funext x
  obtain ⟨y, hy, n, rfl⟩ := exists_cell_rep x
  simpa only [hp y n, Pi.zero_apply] using hfcell y hy

/-- Vanishing of every actual integral Fourier coefficient forces a
continuous periodic complex function to vanish everywhere. -/
theorem continuous_periodic_eq_zero_of_fc_eq_zero {f : Pt 2 → ℂ}
    (hf : Continuous f) (hp : IsPeriodic f)
    (hfc : ∀ k : Fin 2 → ℤ, fc f k = 0) : f = 0 := by
  have hP := parseval_cell_complex f hf hp
  apply periodic_complex_eq_zero_of_integral_norm_sq_eq_zero hf hp
  simpa only [hfc, norm_zero, zero_pow (by norm_num : 2 ≠ 0), tsum_zero] using hP.tsum_eq.symm

/-- Equality of every genuine Fourier coefficient implies equality of
the original continuous periodic functions at every spatial point. -/
theorem continuous_periodic_eq_of_fc_eq {f g : Pt 2 → ℂ}
    (hf : Continuous f) (hfp : IsPeriodic f) (hg : Continuous g) (hgp : IsPeriodic g)
    (hcoeff : ∀ k : Fin 2 → ℤ, fc f k = fc g k) : f = g := by
  have hp : IsPeriodic (fun x => f x - g x) := by
    intro x n
    change f (x + intVec n) - g (x + intVec n) = f x - g x
    rw [hfp x n, hgp x n]
  have hz : (fun x => f x - g x) = 0 :=
    continuous_periodic_eq_zero_of_fc_eq_zero (hf.sub hg) hp (fun k => by
      rw [← fc_sub f g hf hg k, hcoeff k, sub_self])
  funext x
  have hx := congrFun hz x
  exact sub_eq_zero.mp hx

/-- Termwise integration of any genuinely absolutely summable character
series recovers the original coefficients. This is independent of any
Navier–Stokes construction. -/
theorem fc_tsum_character_series {a : (Fin 2 → ℤ) → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (m : Fin 2 → ℤ) :
    fc (complexFourierSeries a) m = a m := by
  let F := fun (k : Fin 2 → ℤ) (x : Pt 2) =>
    a k * expChar (intVec k) x * expChar (-intVec m) x
  have hi (k) : Integrable (F k) (volume.restrict (cell 2)) := by
    have hc : Continuous (F k) :=
      (continuous_const.mul (continuous_expChar (intVec k))).mul
        (continuous_expChar (-intVec m))
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hnorm (k) : (fun x => ‖F k x‖) = fun _ : Pt 2 => ‖a k‖ := by
    funext x
    simp only [F, norm_mul, norm_expChar, mul_one]
  have hvol : volume (cell 2) = 1 := by simp [cell, Real.volume_Icc_pi]
  have hs : Summable (fun k => ∫ x in cell 2, ‖F k x‖) := by
    simpa only [hnorm, integral_const, Measure.real, Measure.restrict_apply_univ,
      hvol, ENNReal.toReal_one, one_smul] using ha
  have he : (fun x => complexFourierSeries a x * expChar (-intVec m) x) =
      fun x => ∑' k, F k x := by
    funext x
    simp only [complexFourierSeries, complexFourierSeriesTerm, F, tsum_mul_right]
  rw [fc, he, ← integral_tsum_of_summable_integral_norm hi hs]
  have hterm (k) : (∫ x in cell 2, F k x) = a k * (if k = m then 1 else 0) := by
    simp only [F, mul_assoc]
    rw [integral_const_mul]
    change a k * fc (expChar (intVec k)) m = _
    rw [fc_expChar]
  simp only [hterm, mul_ite, mul_one, mul_zero, tsum_ite_eq]

/-- Any continuous periodic function with absolutely summable Fourier
coefficients equals its genuine Fourier series pointwise. -/
theorem complexFourierSeries_fc_eq {f : Pt 2 → ℂ}
    (hf : Continuous f) (hp : IsPeriodic f)
    (ha : Summable (fun k => ‖fc f k‖)) : complexFourierSeries (fc f) = f := by
  apply continuous_periodic_eq_of_fc_eq (continuous_complexFourierSeries ha)
    (isPeriodic_complexFourierSeries (fc f)) hf hp
  intro k
  exact fc_tsum_character_series ha k

/-- An absolutely summable coefficient family which matches a continuous
periodic function reconstructs that actual function. -/
theorem complexFourierSeries_eq_of_fc_eq {a : (Fin 2 → ℤ) → ℂ} {f : Pt 2 → ℂ}
    (ha : Summable (fun k => ‖a k‖)) (hf : Continuous f) (hp : IsPeriodic f)
    (hcoeff : ∀ k : Fin 2 → ℤ, a k = fc f k) : complexFourierSeries a = f := by
  apply continuous_periodic_eq_of_fc_eq (continuous_complexFourierSeries ha)
    (isPeriodic_complexFourierSeries a) hf hp
  intro k
  rw [fc_tsum_character_series ha, hcoeff k]

end AnomDiss
