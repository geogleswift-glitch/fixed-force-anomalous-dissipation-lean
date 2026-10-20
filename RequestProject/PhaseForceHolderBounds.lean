module

public import RequestProject.HolderTimeContinuity
public import RequestProject.ParabolicHolderOperations

/-!
# Uniform Hölder bounds for the actual constructed forces

The proved decay of the disjoint force pieces gives one spatial Hölder
bound for every phase and every time. Their true time derivatives also
give uniform time Lipschitz bounds. These estimates concern the actual
force in the main construction, without a Navier--Stokes premise.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff
noncomputable section

namespace AnomDiss

theorem forceD_uniform_holderBd {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (r : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ (w : Phase) (t : ℝ), HolderBd α (forceD w r t) K := by
  let X : ℕ → ℝ := fun j => kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2)
  have hb := Metric.isBounded_range_of_tendsto (fun j => X j / ηs j) (piece_decay hα1 r)
  obtain ⟨B, hB⟩ := hb.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg (X 0 / ηs 0)).trans (hB _ (mem_range_self 0))
  have hτ : 0 ≤ τstar := by unfold τstar; positivity
  have hX : ∀ j : ℕ, 1 ≤ j → X j ≤ B * τstar := by
    intro j hj
    have hη := ηs_pos j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hηle : ηs j ≤ τstar := by
      unfold ηs
      exact div_le_self hτ (by nlinarith : (1 : ℝ) ≤ (j : ℝ) ^ 2)
    have hY : X j / ηs j ≤ B :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB _ (mem_range_self j))
    calc
      X j = (X j / ηs j) * ηs j := by field_simp
      _ ≤ B * ηs j := mul_le_mul_of_nonneg_right hY hη.le
      _ ≤ B * τstar := mul_le_mul_of_nonneg_left hηle hB0
  obtain ⟨C, hC0, hC⟩ := fpiece_bound hα0 hα1.le r
  refine ⟨C * (B * τstar), by positivity, fun w t => ?_⟩
  rcases forceD_single w r t with hz | ⟨j, hj, _, he⟩
  · rw [hz]
    exact HolderBd.zero.mono (by positivity)
  · rw [he]
    exact (hC w j hj t).mono (by
      simpa only [X, mul_assoc] using mul_le_mul_of_nonneg_left (hX j hj) hC0)

theorem hasDerivAt_of_holderNorm_slope {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α t : ℝ}
    {f : ℝ → Pt d → E} {f' : Pt d → E}
    (hd : Tendsto (fun h : ℝ => holderNorm α
      (h⁻¹ • (f (t + h) - f t) - f')) (𝓝[≠] 0) (𝓝 0)) (x : Pt d) :
    HasDerivAt (fun s => f s x) (f' x) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hd
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      ‖h⁻¹ • (f (t + h) x - f t x) - f' x‖ ≤
        (holderNorm α (h⁻¹ • (f (t + h) - f t) - f')).toReal := by
    filter_upwards [hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))]
      with h hh
    exact norm_le_holderNorm_toReal (hh.trans (by simp)) x
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb
    (by simpa [Function.comp_def] using hr)

theorem gForce_timeHolder_one (w : Phase) (T : ℝ) : TimeHolder T 1 (gForce w) := by
  obtain ⟨B, _, hB⟩ := forceD_uniform_holderBd (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) 1
  have hd : ∀ t x, HasDerivAt (fun s => gForce w s x) (forceD w 1 t x) t := by
    intro t x
    have he := hasDerivAt_of_holderNorm_slope
      (forceD_deriv (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) w 0 t) x
    simpa only [forceD_zero_eq, zero_add] using he
  refine ⟨B, fun t ht s hs x => ?_⟩
  have he := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hd r x).hasDerivWithinAt) (fun r _ => (hB w r).1 x) hs ht
  simpa only [Real.norm_eq_abs, Real.rpow_one] using he

/-- The actual fixed force has the full parabolic Hölder modulus at every
admissible exponent on any finite time slab. -/
theorem gForce_parHolder (w : Phase) (T : ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ParHolder T β (gForce w) := by
  obtain ⟨K, _, hK⟩ := forceD_uniform_holderBd hβ0 hβ1 0
  have hb : BddOn T (gForce w) := by
    refine ⟨K, fun t ht x => ?_⟩
    simpa only [forceD_zero_eq] using (hK w t).1 x
  apply parHolder_of_spatial_time
  · refine ⟨K, fun t ht x y => ?_⟩
    simpa only [forceD_zero_eq] using (hK w t).2 x y
  · exact (gForce_timeHolder_one w T).lower_of_bdd hb (by linarith) (by linarith)

end AnomDiss
