module

public import RequestProject.HeatDuhamelTimeHolder
public import RequestProject.ParabolicHolderOperations

/-!
# Full parabolic regularity of the actual ordinary heat Duhamel integral

All fields refer to the genuine Gaussian integral. Spatial cancellation,
the true time equation and the proved endpoint time estimates provide the
original parabolic Hölder predicate without a PDE existence premise.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal
noncomputable section

namespace AnomDiss

theorem heatDuhamel_isParabolicC12 {ν β T : ℝ} (hν : 0 < ν) (hT : 0 < T)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (hFpar : ParHolder T β F) : IsParabolicC12 T β (heatDuhamel ν F) := by
  have hC0 : 0 ≤ C := (norm_nonneg (F 0 0)).trans (hC 0 0)
  let A := 4 * H * gmom (β + 1) * (2 * ν) ^ ((β - 1) / 2) / (β + 1)
  let B := 2 * duhamelSpaceDerivativeScale ν H β / β
  have hA0 : 0 ≤ A := by
    have hg := gmom_nonneg (β + 1)
    dsimp only [A]
    positivity
  have hB0 : 0 ≤ B := div_nonneg
    (mul_nonneg (by norm_num) (duhamelSpaceDerivativeScale_nonneg hν.le hH)) hβ0.le
  have hb1 : ∀ i, BddOn T (fun t => pd i (heatDuhamel ν F t)) := by
    intro i
    refine ⟨A * T ^ ((β + 1) / 2), fun t ht x => ?_⟩
    exact (norm_pd_heatDuhamel_holder_le hν hF hp hC hH hβ0 hholder i ht.1 x).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ht.1 ht.2 (by linarith : 0 ≤ (β + 1) / 2)) hA0)
  have hb2 : ∀ i j, BddOn T (fun t => pd i (pd j (heatDuhamel ν F t))) := by
    intro i j
    refine ⟨B * T ^ (β / 2), fun t ht x => ?_⟩
    exact (norm_pd2_heatDuhamel_holder_le hν hF hp hC hH hβ0 hholder i j ht.1 x).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ht.1 ht.2 (by linarith : 0 ≤ β / 2)) hB0)
  have hpar2 : ∀ i j, ParHolder T β (fun t => pd i (pd j (heatDuhamel ν F t))) := by
    intro i j
    apply parHolder_of_spatial_time
    · refine ⟨4 * duhamelSpaceDerivativeScale ν H β / β +
        2 * duhamelThirdDerivativeScale ν H β / (1 - β), fun t ht x y => ?_⟩
      exact pd2_heatDuhamel_spatial_schauder hν hF hp hC hH hβ0 hβ1 hholder i j ht.1 x y
    · exact timeHolder_pd2_heatDuhamel_holder hν hF hp hC hH hβ0 hβ1 hholder T i j
  have hdt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      dt T (heatDuhamel ν F) t x = ν • lap (heatDuhamel ν F t) x + F t x :=
    fun t ht x => dt_heatDuhamel_Icc hν hF hp hC hH hβ0 hholder hT ht x
  have hdtpar : ParHolder T β (dt T (heatDuhamel ν F)) := by
    have hlap : ParHolder T β (fun t x => lap (heatDuhamel ν F t) x) := by
      simpa only [lap, Fin.sum_univ_two] using (hpar2 0 0).add (hpar2 1 1)
    have hh := (hlap.clm (ν • ContinuousLinearMap.id ℝ ℂ)).add hFpar
    obtain ⟨K, hK⟩ := hh
    refine ⟨K, fun t ht s hs x y => ?_⟩
    simpa only [hdt t ht x, hdt s hs y, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply] using hK t ht s hs x y
  have hdtbdd : BddOn T (dt T (heatDuhamel ν F)) := by
    refine ⟨ν * (2 * (B * T ^ (β / 2))) + C, fun t ht x => ?_⟩
    rw [hdt t ht x]
    calc
      ‖ν • lap (heatDuhamel ν F t) x + F t x‖ ≤
          ‖ν • lap (heatDuhamel ν F t) x‖ + ‖F t x‖ := norm_add_le _ _
      _ ≤ ν * (2 * (B * T ^ (β / 2))) + C := by
        rw [norm_smul, Real.norm_of_nonneg hν.le, lap, Fin.sum_univ_two]
        apply add_le_add _ (hC t x)
        apply mul_le_mul_of_nonneg_left _ hν.le
        exact (norm_add_le _ _).trans (by
          have h0 := norm_pd2_heatDuhamel_holder_le hν hF hp hC hH hβ0 hholder 0 0 ht.1 x
          have h1 := norm_pd2_heatDuhamel_holder_le hν hF hp hC hH hβ0 hholder 1 1 ht.1 x
          have hpow := Real.rpow_le_rpow ht.1 ht.2 (by linarith : 0 ≤ β / 2)
          have hm := mul_le_mul_of_nonneg_left hpow hB0
          change ‖pd 0 (pd 0 (heatDuhamel ν F t)) x‖ +
            ‖pd 1 (pd 1 (heatDuhamel ν F t)) x‖ ≤ _
          dsimp only [B] at hm
          linarith)
  exact {
    smooth_x := fun t ht => contDiff_two_heatDuhamel_holder hν hF hp hC hH hβ0 hholder ht.1
    diff_t := fun x t ht =>
      (hasDerivWithinAt_heatDuhamel_Icc hν hF hp hC hH hβ0 hholder hT.le ht x).differentiableWithinAt
    bdd := ⟨C * T, fun t ht x => (norm_heatDuhamel_le ν hC t x).trans (by
      rw [abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left ht.2 hC0)⟩
    bdd_dt := hdtbdd
    holder_dt := hdtpar
    bdd_d1 := hb1
    holder_d1_time := fun i =>
      timeHolder_pd_heatDuhamel_holder hν hF hp hC hH hβ0 hβ1 hholder T i
    bdd_d2 := hb2
    holder_d2 := hpar2 }

end AnomDiss
