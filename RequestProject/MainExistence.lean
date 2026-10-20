module

public import RequestProject.ExistenceInterfaces

/-!
# Main theorem from the horizontal existence problem actually used

The horizontal analytic input concerns only time interval `[0,1]`, initial
data zero, the constructed forces `gForce w`, and exponent `1/2`. No global
existence theorem for arbitrary smooth initial data or arbitrary forces, and
no regularity assertion for all exponents, is assumed here.

The horizontal existence assertion and the scalar existence assertion are
explicit premises in this module. `MainWithScalarExistence` supplies the
proved scalar interface; horizontal classical existence remains open.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- The horizontal existence and regularity problem needed by the construction.
Energy identities and uniqueness are deliberately not part of this input. -/
def HorizontalZeroDataExistence : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ w : Phase,
    ∃ (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
      IsClassicalNS 1 ν 0 (gForce w) v p ∧
      IsParabolicC12 1 (1 / 2) v ∧ IsParabolicC01 1 (1 / 2) p

/-- The broad analytic interface implies the concrete zero-data problem; the
converse is not assumed or needed for the theorem below. -/
theorem horizontalZeroDataExistence_of_NSClassicalExistence (hex : NSClassicalExistence) :
    HorizontalZeroDataExistence := by
  intro ν hν w
  obtain ⟨hadm, hmean⟩ := force_regularity.1 w
  obtain ⟨v, p, hreg, hns⟩ := hex 1 ν one_pos hν 0 (gForce w) contDiff_const
    (fun _ _ => rfl) (fun x => by simp [divergence, pd]) (by simp)
    hadm.toIsTimeSmoothForce hmean
  exact ⟨v, p, hns, hreg (1 / 2) (by norm_num) (by norm_num)⟩

/-- The broad external 2D Navier--Stokes result supplies the concrete
zero-data interface used by the construction. -/
theorem horizontalZeroDataExistence_of_ExternalNS2D (hNS : ExternalNS2D) :
    HorizontalZeroDataExistence := by
  intro ν hν w
  obtain ⟨hadm, hmean⟩ := force_regularity.1 w
  obtain ⟨v, p, hreg, hns, -, -⟩ := hNS 1 ν one_pos hν 0 (gForce w) contDiff_const
    (fun _ _ => rfl) (fun x => by simp [divergence, pd]) (by simp)
    hadm.toIsTimeSmoothForce hmean
  exact ⟨v, p, hns, hreg (1 / 2) (by norm_num) (by norm_num)⟩

/-- The same anomalous-dissipation conclusion as `main_theorem`, using only
zero-data horizontal existence for the constructed force and fixed exponent.
The scalar existence/regularity interface has no uniqueness premise. -/
theorem main_theorem_from_zero_data_existence (hNS : HorizontalZeroDataExistence)
    (hScExist : ScalarClassicalExistence) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x := by
  have hSc : ExternalScalar := externalScalar_of_existence hScExist
  obtain ⟨N₁, Cv, hN₁, hbound⟩ := uniform_horizontal_bound
  obtain ⟨wstar, Nseq, hmono, hge, hsel⟩ := phase_selection hSc ε hε0 hε1 N₁
  obtain ⟨-, -, hθs, hθp, hθl2, hθmax, -, -⟩ := initial_frequency ε hε0
  obtain ⟨-, -, hνpos, hνanti, hνlim, -, -⟩ := viscosity_properties
  have hN1 : ∀ m, 1 ≤ Nseq m := fun m => le_trans hN₁ (hge m)
  set ν : ℕ → ℝ := fun m => nuN (Nseq m) with hνdef
  have hνm : ∀ m, 0 < ν m := fun m => hνpos _ (hN1 m)
  choose v p hv hvreg hpreg using fun m => hNS (ν m) (hνm m) wstar
  have hvC01 : ∀ m, IsParabolicC01 1 (1 / 2) (v m) := fun m =>
    (hvreg m).toC01 zero_le_one (by norm_num) (by norm_num)
  choose θ hθreg hθ huniq using fun m =>
    hSc 1 (ν m) (1 / 2) one_pos (hνm m) (by norm_num) (by norm_num) (v m)
      (hv m).periodic_u (hvC01 m) (hv m).div_free (theta0 ε) hθp
      (holderC2_of_smooth_periodic _ hθs hθp (by norm_num) (by norm_num))
  have hsc := fun m => scalar_energy_max 1 (ν m) (1 / 2) (hνm m) (v m)
    (hv m).periodic_u (hvC01 m) (hv m).div_free (theta0 ε) (θ m) (hθ m)
  obtain ⟨hu0s, hu0p, hu0d, hu0l⟩ := embed_initial (theta0 ε) hθs hθp
  refine ⟨embedU 0 (theta0 ε), fun t => embedU (gForce wstar t) 0, ν, hu0s, hu0p, hu0d,
    by rw [hu0l, hθl2], embed_force_admissible _ (force_regularity.1 wstar).1, hνm, ?_, ?_,
    fun m t => embedU (v m t) (θ m t), fun m t x => p m t (proj3 x), ?_, ?_, ?_⟩
  · intro a b hab
    exact hνanti (mem_Ici.2 (hN1 a)) (mem_Ici.2 (hN1 b)) (hmono hab)
  · exact hνlim.comp hmono.tendsto_atTop
  · intro m
    exact (two_to_three_embedding 1 (ν m) (1 / 2) one_pos (by norm_num) (by norm_num)
      0 (gForce wstar) (v m) (p m) (hv m) (hvreg m) (hpreg m)
      (theta0 ε) (θ m) (hθ m) (hθreg m)).1
  · refine ⟨Cv + Real.sqrt 2, fun m t ht x => ?_⟩
    exact embedU_norm_le _ _ x _ _
      (hbound wstar (Nseq m) (hge m) (v m) (p m) (hv m) t ht (proj3 x))
      ((hsc m).1 (Real.sqrt 2) hθmax t ht (proj3 x))
  · intro m
    have hemb := two_to_three_embedding 1 (ν m) (1 / 2) one_pos (by norm_num) (by norm_num)
      0 (gForce wstar) (v m) (p m) (hv m) (hvreg m) (hpreg m)
      (theta0 ε) (θ m) (hθ m) (hθreg m)
    have h1 : (∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (embedU (v m t) (θ m t)) x) =
        ∫ t in (0 : ℝ)..1, ((∫ x in cell 2, gradSqV (v m t) x) +
          ∫ x in cell 2, gradSq (θ m t) x) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le zero_le_one] at ht
      exact hemb.2 t ht
    have hA := intervalIntegrable_gradSqV 1 (1 / 2) zero_le_one (by norm_num) (v m) (hvreg m)
    have hB := intervalIntegrable_gradSq 1 (1 / 2) zero_le_one (by norm_num) (θ m) (hθreg m)
    obtain ⟨hT0, hT1⟩ := TN_le_one (Nseq m)
    have hBsplit : (∫ t in (0 : ℝ)..1, ∫ x in cell 2, gradSq (θ m t) x) =
        (∫ t in (0 : ℝ)..TN (Nseq m), ∫ x in cell 2, gradSq (θ m t) x) +
          ∫ t in TN (Nseq m)..1, ∫ x in cell 2, gradSq (θ m t) x := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact hB.mono_set (by
          rw [uIcc_of_le hT0, uIcc_of_le zero_le_one]
          exact Icc_subset_Icc le_rfl hT1)
      · exact hB.mono_set (by
          rw [uIcc_of_le hT1, uIcc_of_le zero_le_one]
          exact Icc_subset_Icc hT0 le_rfl)
    have hAnn : 0 ≤ ∫ t in (0 : ℝ)..1, ∫ x in cell 2, gradSqV (v m t) x := by
      refine intervalIntegral.integral_nonneg zero_le_one (fun t _ => ?_)
      refine setIntegral_nonneg measurableSet_Icc (fun x _ => ?_)
      unfold gradSqV
      positivity
    have hBnn : 0 ≤ ∫ t in TN (Nseq m)..1, ∫ x in cell 2, gradSq (θ m t) x := by
      refine intervalIntegral.integral_nonneg hT1 (fun t _ => ?_)
      refine setIntegral_nonneg measurableSet_Icc (fun x _ => ?_)
      unfold gradSq
      positivity
    have hdiss := (hsc m).2 (TN (Nseq m)) ⟨hT0, hT1⟩
    have hsel' := hsel m (v m) (p m) (hv m) (θ m) (hθ m)
    rw [hθl2] at hdiss
    unfold dissipation at hdiss
    show (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1,
      ∫ x in cell 3, gradSqV (embedU (v m t) (θ m t)) x
    rw [h1, intervalIntegral.integral_add hA hB, hBsplit]
    have hνpos' := hνm m
    nlinarith [mul_nonneg hνpos'.le hAnn, mul_nonneg hνpos'.le hBnn]

end AnomDiss
