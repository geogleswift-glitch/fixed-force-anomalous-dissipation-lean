module

public import RequestProject.Kernel

/-!
# Basic facts about the comparison scalar used in Section 7

Specification, regularity and `L²` bounds of the chosen comparison scalar, and measurability of
its Fourier coefficients in the phase sequence.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

lemma compScalar_spec (hSc : ExternalScalar) (N : ℕ) (hN : 1 ≤ N) (w : Phase)
    (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) :
    IsComparisonScalar N w θ₀ (compScalar N w θ₀) :=
  Classical.epsilon_spec (comparison_scalar_identities hSc N hN w θ₀ hθ₀ hp).1

lemma compScalar_terminal_le (hSc : ExternalScalar) (N : ℕ) (hN : 1 ≤ N) (w : Phase)
    (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) :
    l2sq (compScalar N w θ₀ (TN N)) ≤ l2sq θ₀ := by
  have h := (comparison_scalar_identities hSc N hN w θ₀ hθ₀ hp).2.2 _
    (compScalar_spec hSc N hN w θ₀ hθ₀ hp)
  have hT := TN_bounds N
  have he := h.2 (TN N) ⟨hT.1, le_rfl⟩
  have hd := dissipation_nonneg' (nuN N) (viscosity_properties.2.2.1 N hN).le
    (compScalar N w θ₀) (TN N) hT.1
  linarith


lemma compScalar_regular (hSc : ExternalScalar) (N : ℕ) (hN : 1 ≤ N) (w : Phase)
    (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) (j : ℕ) (hj : 1 ≤ j)
    (hjN : j ≤ N + 1) :
    Continuous (compScalar N w θ₀ (sj j)) ∧ IsPeriodic (compScalar N w θ₀ (sj j)) := by
  have hs := compScalar_spec hSc N hN w θ₀ hθ₀ hp
  rcases Nat.lt_or_ge j 2 with h | h
  · obtain rfl : j = 1 := by omega
    rw [sj_one, hs.1]; exact ⟨hθ₀.continuous, hp⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hq := (hs.2 i (by omega) (by omega)).2
    have hη : ηs i ∈ Icc 0 (ηs i) := ⟨ηs_nonneg i, le_rfl⟩
    have e : sj (i + 1) = sj i + δs i + ηs i := sj_succ i (by omega)
    rw [e]
    obtain ⟨β, -, -, hreg⟩ := hq.regular
    exact ⟨(hreg.smooth_x _ hη).continuous, hq.periodic _ hη⟩

lemma fc_sq_le (h : Pt 2 → ℝ) (hc : Continuous h) (hp : IsPeriodic h) (ℓ : Fin 2 → ℤ) :
    ‖fc (fun x => (h x : ℂ)) ℓ‖ ^ 2 ≤ l2sq h := by
  have := parseval_cell h hc hp
  exact (this.summable.le_tsum ℓ (fun _ _ => sq_nonneg _)).trans_eq this.tsum_eq

lemma compScalar_l2_le (hSc : ExternalScalar) (N : ℕ) (hN : 1 ≤ N) (w : Phase)
    (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) (t : ℝ)
    (ht : t ∈ Icc 0 (TN N)) :
    l2sq (compScalar N w θ₀ t) ≤ l2sq θ₀ := by
  have h := (comparison_scalar_identities hSc N hN w θ₀ hθ₀ hp).2.2 _
    (compScalar_spec hSc N hN w θ₀ hθ₀ hp)
  have he := h.2 t ht
  have hd := dissipation_nonneg' (nuN N) (viscosity_properties.2.2.1 N hN).le
    (compScalar N w θ₀) t ht.1
  linarith


/-- Measurability of the Fourier coefficients `ω ↦ (θ̄_ω^{ν_N}(s_j))^(m)` of the comparison
scalar started from any smooth periodic `θ₀`, at the stage times `s_j`, `1 ≤ j ≤ N + 1`.
The proof shows that these coefficients depend continuously on `ω` (product topology). -/
theorem compScalar_fourier_measurable_gen (hSc : ExternalScalar) (θ₀ : Pt 2 → ℝ)
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) (N : ℕ) (hN : 1 ≤ N)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N + 1) (m : Fin 2 → ℤ) :
    Measurable fun w => fc (fun x => (compScalar N w θ₀ (sj j) x : ℂ)) m := by
  obtain ⟨B, -, hB⟩ := periodic_bound θ₀ hθ₀.continuous hp
  have hM : ∀ x, |θ₀ x| ≤ B := fun x => by simpa [Real.norm_eq_abs] using hB x
  set F : Phase → ℂ := fun w => fc (fun x => (compScalar N w θ₀ (sj j) x : ℂ)) m with hF
  set c := B ^ 2 / (2 * nuN N)
  have key : ∀ w w₀ : Phase, ‖F w - F w₀‖ ^ 2 ≤ c * ∑ i ∈ Finset.Ico 1 j,
      ∫ t in (0 : ℝ)..δs i, l2sqV (fun x =>
        VpulseB (nuN N) i (w i) (sj i + t) x - VpulseB (nuN N) i (w₀ i) (sj i + t) x) := by
    intro w w₀
    have hr := compScalar_regular hSc N hN w θ₀ hθ₀ hp j hj hjN
    have hr₀ := compScalar_regular hSc N hN w₀ θ₀ hθ₀ hp j hj hjN
    have hch := comparison_chain hN w w₀ θ₀ hM _ _
      (compScalar_spec hSc N hN w θ₀ hθ₀ hp)
      (compScalar_spec hSc N hN w₀ θ₀ hθ₀ hp) j hj hjN
    refine le_trans (le_of_eq ?_) ((fc_sq_le _ (hr.1.fun_sub hr₀.1)
      (fun x n => by simp only [hr.2 x n, hr₀.2 x n]) m).trans hch)
    congr 2
    simp only [hF, fc]
    rw [← integral_sub]
    · congr 1; funext x; push_cast; ring
    · exact ((Complex.continuous_ofReal.comp hr.1).mul
        (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc
    · exact ((Complex.continuous_ofReal.comp hr₀.1).mul
        (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc
  refine Continuous.measurable (continuous_iff_continuousAt.2 fun w₀ => ?_)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set G : Phase → ℝ := fun w => c * ∑ i ∈ Finset.Ico 1 j, ∫ t in (0 : ℝ)..δs i, l2sqV (fun x =>
    VpulseB (nuN N) i (w i) (sj i + t) x - VpulseB (nuN N) i (w₀ i) (sj i + t) x) with hG
  have hGc : Continuous G := continuous_const.mul (continuous_finset_sum _ fun i _ =>
    (continuous_stage_discrepancy (nuN N) i (w₀ i)).comp (continuous_apply i))
  have hG0 : G w₀ = 0 := by simp [hG, l2sqV]
  have hlim : Tendsto (fun w => Real.sqrt (G w)) (𝓝 w₀) (𝓝 0) := by
    have := (Real.continuous_sqrt.comp hGc).tendsto w₀
    simpa [Function.comp_def, hG0] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun w => norm_nonneg _) (fun w => ?_)
  have := Real.abs_le_sqrt (key w w₀)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- Measurability of the Fourier coefficients `ω ↦ (θ̄_ω^{ν_N}(s_j))^(m)` of the comparison
scalar at the stage times `s_j`, `1 ≤ j ≤ N + 1` (used implicitly in Section 7 whenever an
expectation over `ω` is taken; cf. the first part of the proof of Lemma 7.9). -/
theorem compScalar_fourier_measurable (hSc : ExternalScalar) (ε : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N + 1) (m : Fin 2 → ℤ) :
    Measurable fun w => fc (fun x => (compScalar N w (theta0 ε) (sj j) x : ℂ)) m :=
  compScalar_fourier_measurable_gen hSc _ (theta0_contDiff ε) (theta0_periodic ε) N hN j hj hjN m

end AnomDiss
