module

public import RequestProject.FourierSeriesRegularity
public import RequestProject.FourierTimeInterpolation

/-! # Actual series and derivative differences from absolute moments -/

@[expose] public section
open MeasureTheory Set Filter Topology Real
noncomputable section
namespace AnomDiss

theorem norm_complexFourierSeries_sub_le_first_moment
    {a b : (Fin 2 → ℤ) → ℂ} {M : ℝ}
    (ha : Summable (fun k => ‖a k‖)) (hb : Summable (fun k => ‖b k‖))
    (hd : Summable (fun k => (1+‖intVec k‖)*‖a k-b k‖))
    (hM : (∑' k, (1+‖intVec k‖)*‖a k-b k‖) ≤ M) (x : Pt 2) :
    ‖complexFourierSeries a x-complexFourierSeries b x‖ ≤ M := by
  have hs := (summable_complexFourierSeriesTerm ha x).sub (summable_complexFourierSeriesTerm hb x)
  have hp (k : Fin 2 → ℤ) :
      ‖complexFourierSeriesTerm a k x-complexFourierSeriesTerm b k x‖ ≤
        (1+‖intVec k‖)*‖a k-b k‖ := by
    have he : complexFourierSeriesTerm a k x-complexFourierSeriesTerm b k x =
        (a k-b k)*expChar (intVec k) x := by simp only [complexFourierSeriesTerm]; ring
    rw [he, norm_mul, norm_expChar, mul_one]
    nlinarith [mul_nonneg (norm_nonneg (intVec k)) (norm_nonneg (a k-b k))]
  unfold complexFourierSeries
  rw [← (summable_complexFourierSeriesTerm ha x).tsum_sub (summable_complexFourierSeriesTerm hb x)]
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((Summable.tsum_le_tsum hp hs.norm hd).trans hM)

theorem norm_pd_complexFourierSeries_sub_le_first_moment
    {a b : (Fin 2 → ℤ) → ℂ} {M : ℝ}
    (ha : Summable (fun k => ‖a k‖)) (hb : Summable (fun k => ‖b k‖))
    (hda : Summable (fun k => ‖intVec k‖*‖a k‖))
    (hdb : Summable (fun k => ‖intVec k‖*‖b k‖))
    (hd : Summable (fun k => (1+‖intVec k‖)*‖a k-b k‖))
    (hM : (∑' k, (1+‖intVec k‖)*‖a k-b k‖) ≤ M) (j : Fin 2) (x : Pt 2) :
    ‖pd j (complexFourierSeries a) x-pd j (complexFourierSeries b) x‖ ≤
      ‖(2*π*Complex.I : ℂ)‖*M := by
  let C : ℝ := ‖(2*π*Complex.I : ℂ)‖
  have hsa := summable_pd_complexFourierSeries hda j x
  have hsb := summable_pd_complexFourierSeries hdb j x
  have hs := hsa.sub hsb
  have hp (k : Fin 2 → ℤ) :
      ‖(2*π*Complex.I*(k j : ℂ))*a k*expChar (intVec k) x-
        (2*π*Complex.I*(k j : ℂ))*b k*expChar (intVec k) x‖ ≤
        C*((1+‖intVec k‖)*‖a k-b k‖) := by
    have he : (2*π*Complex.I*(k j : ℂ))*a k*expChar (intVec k) x-
        (2*π*Complex.I*(k j : ℂ))*b k*expChar (intVec k) x =
        (2*π*Complex.I)*(k j : ℂ)*(a k-b k)*expChar (intVec k) x := by ring
    have hk : ‖(k j : ℂ)‖ ≤ 1+‖intVec k‖ := by
      have hh : ‖(k j : ℂ)‖ ≤ ‖intVec k‖ := by
        simpa only [Complex.norm_intCast, ← Real.norm_eq_abs, intVec] using norm_le_pi_norm (intVec k) j
      linarith
    rw [he, norm_mul, norm_expChar, mul_one, norm_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) (norm_nonneg _)).trans_eq (by dsimp [C]; ring)
  rw [pd_complexFourierSeries ha hda, pd_complexFourierSeries hb hdb,
    ← hsa.tsum_sub hsb]
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  apply (Summable.tsum_le_tsum hp hs.norm (hd.mul_left C)).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)

end AnomDiss
