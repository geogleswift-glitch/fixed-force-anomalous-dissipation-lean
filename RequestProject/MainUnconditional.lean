module

public import RequestProject.MainRegularity
public import RequestProject.TrueHorizontalProved

/-!
# The unconditional fixed-force anomalous-dissipation construction

Both analytic existence inputs are proved in this development. The same
velocity and pressure witnesses have every exponent required by the
manuscript. The only parameters of the main theorem are the numerical
error tolerance and its defining inequalities.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
namespace AnomDiss

theorem main_theorem_unconditional (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∀ m β, 0 < β → β < 1 →
          IsParabolicC12 1 β (u m) ∧ IsParabolicC01 1 β (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x := by
  obtain ⟨N₁, Cv, hN₁, hbound⟩ := uniform_horizontal_bound
  obtain ⟨wstar, Nseq, hmono, hge, hsel⟩ := phase_selection externalScalar_proved ε hε0 hε1 N₁
  obtain ⟨-, -, hθs, hθp, hθl2, hθmax, -, -⟩ := initial_frequency ε hε0
  obtain ⟨-, -, hνpos, hνanti, hνlim, -, -⟩ := viscosity_properties
  have hN1 : ∀ m, 1 ≤ Nseq m := fun m => le_trans hN₁ (hge m)
  set ν : ℕ → ℝ := fun m => nuN (Nseq m) with hνdef
  have hνm : ∀ m, 0 < ν m := fun m => hνpos _ (hN1 m)
  have hex := fun m => true_horizontal_existence_proved (ν m) (hνm m) wstar
  choose v p hv hreg hE hsc using hex
  choose θ hθ huniq hmax hen using fun m => hsc m (theta0 ε) hθs hθp
  have hθall : ∀ m β, 0 < β → β < 1 → IsParabolicC12 1 β (θ m) := by
    intro m β hβ0 hβ1
    have hvC01 : IsParabolicC01 1 β (v m) :=
      (hreg m β hβ0 hβ1).1.toC01 zero_le_one hβ0 hβ1
    obtain ⟨θβ, hθβreg, hθβ, hθβuniq⟩ := externalScalar_proved 1 (ν m) β one_pos (hνm m) hβ0 hβ1
      (v m) (hv m).periodic_u hvC01 (hv m).div_free (theta0 ε) hθp
      (holderC2_of_smooth_periodic _ hθs hθp hβ0.le hβ1.le)
    exact hθβreg.congr (hθβuniq (θ m) (hθ m))
  obtain ⟨hu0s, hu0p, hu0d, hu0l⟩ := embed_initial (theta0 ε) hθs hθp
  refine ⟨embedU 0 (theta0 ε), fun t => embedU (gForce wstar t) 0, ν, hu0s, hu0p, hu0d,
    by rw [hu0l, hθl2], embed_force_admissible _ (force_regularity.1 wstar).1, hνm, ?_, ?_,
    fun m t => embedU (v m t) (θ m t), fun m t x => p m t (proj3 x), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact hνanti (mem_Ici.2 (hN1 a)) (mem_Ici.2 (hN1 b)) (hmono hab)
  · exact hνlim.comp hmono.tendsto_atTop
  · intro m
    obtain ⟨β, hβ0, hβ1, hθreg⟩ := (hθ m).regular
    exact (two_to_three_embedding 1 (ν m) β one_pos hβ0 hβ1 0 (gForce wstar) (v m) (p m) (hv m)
      (hreg m β hβ0 hβ1).1 (hreg m β hβ0 hβ1).2 (theta0 ε) (θ m) (hθ m) hθreg).1
  · intro m β hβ0 hβ1
    exact ⟨parabolicC12_embedU one_pos hβ0 (hreg m β hβ0 hβ1).1 (hθall m β hβ0 hβ1),
      parabolicC01_comp_proj3 hβ0 (hreg m β hβ0 hβ1).2⟩
  · refine ⟨Cv + Real.sqrt 2, fun m t ht x => ?_⟩
    exact embedU_norm_le _ _ x _ _
      (hbound wstar (Nseq m) (hge m) (v m) (p m) (hv m) t ht (proj3 x))
      (hmax m (Real.sqrt 2) hθmax t ht (proj3 x))
  · intro m
    obtain ⟨β, hβ0, hβ1, hθreg⟩ := (hθ m).regular
    have hemb := two_to_three_embedding 1 (ν m) β one_pos hβ0 hβ1 0 (gForce wstar) (v m) (p m)
      (hv m) (hreg m β hβ0 hβ1).1 (hreg m β hβ0 hβ1).2 (theta0 ε) (θ m) (hθ m) hθreg
    have h1 : (∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (embedU (v m t) (θ m t)) x) =
        ∫ t in (0 : ℝ)..1, ((∫ x in cell 2, gradSqV (v m t) x) +
          ∫ x in cell 2, gradSq (θ m t) x) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le zero_le_one] at ht
      exact hemb.2 t ht
    have hA := intervalIntegrable_gradSqV 1 β zero_le_one hβ0 (v m) (hreg m β hβ0 hβ1).1
    have hB := intervalIntegrable_gradSq 1 β zero_le_one hβ0 (θ m) hθreg
    obtain ⟨hT0, hT1⟩ := TN_le_one (Nseq m)
    have hBsplit : (∫ t in (0 : ℝ)..1, ∫ x in cell 2, gradSq (θ m t) x) =
        (∫ t in (0 : ℝ)..TN (Nseq m), ∫ x in cell 2, gradSq (θ m t) x) +
          ∫ t in TN (Nseq m)..1, ∫ x in cell 2, gradSq (θ m t) x := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact hB.mono_set (by rw [uIcc_of_le hT0, uIcc_of_le zero_le_one]
                              exact Icc_subset_Icc le_rfl hT1)
      · exact hB.mono_set (by rw [uIcc_of_le hT1, uIcc_of_le zero_le_one]
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
    have hdiss := hen m (TN (Nseq m)) ⟨hT0, hT1⟩
    have hsel' := hsel m (v m) (p m) (hv m) (θ m) (hθ m)
    rw [hθl2] at hdiss
    unfold dissipation at hdiss
    show (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1,
      ∫ x in cell 3, gradSqV (embedU (v m t) (θ m t)) x
    rw [h1, intervalIntegral.integral_add hA hB, hBsplit]
    have hνpos' := hνm m
    nlinarith [mul_nonneg hνpos'.le hAnn, mul_nonneg hνpos'.le hBnn]



end AnomDiss
