module

public import RequestProject.ScalarHessianSchauder
public import RequestProject.HeatSemigroup
public import RequestProject.HeatHolderFirstOrder

/-!
# Time Hölder estimates for the homogeneous heat evolution

The semigroup identity and the actual Gaussian approximation estimate turn
spatial Hölder continuity into time Hölder continuity, including time zero.
In particular, initial `C^{2+β}` data give the required time estimate for
the actual Hessian of the homogeneous part of the scalar mild solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem heatOp_time_increment_holder {f : Pt 2 → ℂ} (hf : Continuous f)
    {C H β ν s h : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (hν : 0 ≤ ν) (hs : 0 ≤ s) (hh : 0 ≤ h) (x : Pt 2) :
    ‖heatOp (Real.toNNReal (2 * ν * (s + h))) f x -
      heatOp (Real.toNNReal (2 * ν * s)) f x‖ ≤
        (2 * H * gmom β * (2 * ν) ^ (β / 2)) * h ^ (β / 2) := by
  let vs := Real.toNNReal (2 * ν * s)
  let vh := Real.toNNReal (2 * ν * h)
  have hv : Real.toNNReal (2 * ν * (s + h)) = vh + vs := by
    dsimp only [vh, vs]
    rw [← Real.toNNReal_add (by positivity : 0 ≤ 2 * ν * h)
      (by positivity : 0 ≤ 2 * ν * s)]
    congr 1
    ring
  have hc : Continuous (heatOp vs f) := continuous_gavg hf hC vs
  have hb : ∀ y, ‖heatOp vs f y‖ ≤ C := fun y => norm_heatOp_le hC vs y
  have hhld : ∀ y z, ‖heatOp vs f y - heatOp vs f z‖ ≤ H * ‖y - z‖ ^ β :=
    heatOp_holder_distance hf hC hholder vs
  rw [hv, heatOp_semigroup hf hC]
  have he := heatOp_holder_initial_error hc hb hβ hH hhld vh x
  have hp : (vh : ℝ) ^ (β / 2) = (2 * ν) ^ (β / 2) * h ^ (β / 2) := by
    change (Real.toNNReal (2 * ν * h) : ℝ) ^ (β / 2) = _
    rw [Real.coe_toNNReal _ (by positivity)]
    exact Real.mul_rpow (by positivity) hh
  rw [hp] at he
  simpa only [vs, mul_assoc] using he

theorem heatOp_timeHolder {f : Pt 2 → ℂ} (hf : Continuous f)
    {C H β ν T : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (hν : 0 ≤ ν) :
    TimeHolder T (β / 2) (fun t => heatOp (Real.toNNReal (2 * ν * t)) f) := by
  refine ⟨2 * H * gmom β * (2 * ν) ^ (β / 2), ?_⟩
  intro t ht s hs x
  rcases le_total s t with hst | hts
  · have he := heatOp_time_increment_holder hf hC hH hβ hholder hν hs.1
      (sub_nonneg.2 hst) x
    simpa only [add_sub_cancel, abs_of_nonneg (sub_nonneg.2 hst)] using he
  · have he := heatOp_time_increment_holder hf hC hH hβ hholder hν ht.1
      (sub_nonneg.2 hts) x
    rw [norm_sub_rev, abs_sub_comm]
    simpa only [add_sub_cancel, abs_of_nonneg (sub_nonneg.2 hts)] using he

/-- The genuine Hessian of the homogeneous heat solution has the endpoint
time estimate required by parabolic `C^{1+β/2,2+β}` regularity. -/
theorem pd2_heatOp_timeHolder {f : Pt 2 → ℂ} {β ν T : ℝ}
    (hf : IsHolderC2 β f) (hp : IsPeriodic f) (hβ : 0 < β) (hν : 0 ≤ ν)
    (i j : Fin 2) :
    TimeHolder T (β / 2)
      (fun t => pd i (pd j (heatOp (Real.toNNReal (2 * ν * t)) f))) := by
  obtain ⟨hf2, H, hH⟩ := hf
  have hc : Continuous (pd i (pd j f)) :=
    continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf2 j) i
  obtain ⟨C, hC⟩ := (isQP_pd2 (isQP_zero_iff.2 hp) hf2 i j).bdd hc
  have hhld : ∀ x y, ‖pd i (pd j f) x - pd i (pd j f) y‖ ≤
      max H 0 * ‖x - y‖ ^ β := fun x y =>
    (hH i j x y).trans (mul_le_mul_of_nonneg_right (le_max_left H 0)
      (Real.rpow_nonneg (norm_nonneg _) _))
  unfold TimeHolder
  simp_rw [pd2_heatOp (isQP_zero_iff.2 hp) hf2]
  exact heatOp_timeHolder hc hC (le_max_right H 0) hβ hhld hν

/-- First spatial partials gain the full `(1+β)/2` time exponent from
the Hölder continuity of the initial Hessian and Gaussian cancellation. -/
theorem pd_heatOp_time_increment_holder {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {H β ν s h : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hholder : ∀ i j x y,
      ‖pd i (pd j f) x - pd i (pd j f) y‖ ≤ H * ‖x - y‖ ^ β)
    (hν : 0 ≤ ν) (hs : 0 ≤ s) (hh : 0 ≤ h) (j : Fin 2) (x : Pt 2) :
    ‖pd j (heatOp (Real.toNNReal (2 * ν * (s + h))) f) x -
      pd j (heatOp (Real.toNNReal (2 * ν * s)) f) x‖ ≤
        (4 * H * gmom (1 + β) * (2 * ν) ^ ((1 + β) / 2)) * h ^ ((1 + β) / 2) := by
  let vs := Real.toNNReal (2 * ν * s)
  let vh := Real.toNNReal (2 * ν * h)
  have hv : Real.toNNReal (2 * ν * (s + h)) = vh + vs := by
    dsimp only [vh, vs]
    rw [← Real.toNNReal_add (by positivity : 0 ≤ 2 * ν * h)
      (by positivity : 0 ≤ 2 * ν * s)]
    congr 1
    ring
  have hqp : IsQP 0 f := isQP_zero_iff.2 hp
  obtain ⟨C, hC⟩ := hqp.bdd hf.continuous
  have hA2 : ContDiff ℝ 2 (heatOp vs f) := contDiff_heatOp hqp hf vs
  have hAp : IsPeriodic (heatOp vs f) := isQP_zero_iff.1 (heatOp_isQP hqp vs)
  have hg1 : ContDiff ℝ 1 (pd j (heatOp vs f)) :=
    contDiff_pd_of_C2 _ hA2 j
  obtain ⟨B, hB⟩ := (isQP_zero_iff.2 (isPeriodic_pd _ hAp j)).bdd hg1.continuous
  have hhld : ∀ i y z, ‖pd i (pd j (heatOp vs f)) y -
      pd i (pd j (heatOp vs f)) z‖ ≤ H * ‖y - z‖ ^ β :=
    fun i y z => pd2_heatOp_holder_of_C2 hf hp hholder vs i j y z
  have hsemigroup : heatOp (vh + vs) f = heatOp vh (heatOp vs f) :=
    funext fun y => heatOp_semigroup hf.continuous hC vh vs y
  rw [hv, hsemigroup,
    pd_heatOp_C1 (isQP_zero_iff.2 hAp) (hA2.of_le (by norm_num))]
  have he := heatOp_C1_holder_initial_error hg1 hB hH hβ hhld vh x
  have heq : (vh : ℝ) ^ ((1 + β) / 2) =
      (2 * ν) ^ ((1 + β) / 2) * h ^ ((1 + β) / 2) := by
    change (Real.toNNReal (2 * ν * h) : ℝ) ^ ((1 + β) / 2) = _
    rw [Real.coe_toNNReal _ (by positivity)]
    exact Real.mul_rpow (by positivity) hh
  rw [heq] at he
  simpa only [vs, mul_assoc] using he

theorem pd_heatOp_timeHolder {f : Pt 2 → ℂ} {β ν T : ℝ}
    (hf : IsHolderC2 β f) (hp : IsPeriodic f) (hβ : 0 ≤ β) (hν : 0 ≤ ν)
    (j : Fin 2) :
    TimeHolder T ((1 + β) / 2)
      (fun t => pd j (heatOp (Real.toNNReal (2 * ν * t)) f)) := by
  obtain ⟨hf2, H, hH⟩ := hf
  have hhld : ∀ i j x y, ‖pd i (pd j f) x - pd i (pd j f) y‖ ≤
      max H 0 * ‖x - y‖ ^ β := fun i j x y =>
    (hH i j x y).trans (mul_le_mul_of_nonneg_right (le_max_left H 0)
      (Real.rpow_nonneg (norm_nonneg _) _))
  refine ⟨4 * max H 0 * gmom (1 + β) * (2 * ν) ^ ((1 + β) / 2), ?_⟩
  intro t ht s hs x
  rcases le_total s t with hst | hts
  · have he := pd_heatOp_time_increment_holder hf2 hp (le_max_right H 0) hβ hhld
      hν hs.1 (sub_nonneg.2 hst) j x
    simpa only [add_sub_cancel, abs_of_nonneg (sub_nonneg.2 hst)] using he
  · have he := pd_heatOp_time_increment_holder hf2 hp (le_max_right H 0) hβ hhld
      hν ht.1 (sub_nonneg.2 hts) j x
    rw [norm_sub_rev, abs_sub_comm]
    simpa only [add_sub_cancel, abs_of_nonneg (sub_nonneg.2 hts)] using he

end AnomDiss
