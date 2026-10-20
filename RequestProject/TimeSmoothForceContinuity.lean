module

public import RequestProject.Basic

/-!
# Joint continuity of time-smooth Hölder-valued forces

The derivative in the specified Hölder norm implies a local uniform time
bound. Together with continuous spatial slices this proves genuine joint
continuity, and hence supplies the forcing input for the finite ODE systems.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem enorm_le_holderNorm (α : ℝ) (f : Pt d → E) (x : Pt d) :
    ‖f x‖ₑ ≤ holderNorm α f :=
  (le_iSup (fun y => ‖f y‖ₑ) x).trans (le_add_right le_rfl)

omit [NormedSpace ℝ E] in
theorem norm_le_holderNorm_toReal {α : ℝ} {f : Pt d → E}
    (hf : holderNorm α f < ⊤) (x : Pt d) : ‖f x‖ ≤ (holderNorm α f).toReal := by
  rw [← ENNReal.toReal_ofReal (norm_nonneg (f x)), ofReal_norm_eq_enorm]
  exact ENNReal.toReal_mono hf.ne (enorm_le_holderNorm α f x)

/-- Differentiability in the manuscript's Hölder norm gives a genuine local
time increment estimate, uniform over the entire lifted torus. -/
theorem IsSmoothHolderValued.locally_uniform_time_bound {α : ℝ}
    {f : ℝ → Pt d → E} (hf : IsSmoothHolderValued α f) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ h in 𝓝 (0 : ℝ),
      ∀ x, ‖f (t + h) x - f t x‖ ≤ |h| * C := by
  obtain ⟨D, hD0, hDfin, hDlim⟩ := hf
  let C : ℝ := 1 + (holderNorm α (D 1 t)).toReal
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      holderNorm α (h⁻¹ • (D 0 (t + h) - D 0 t) - D 1 t) < 1 :=
    (hDlim 0 t).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  have hp : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ∀ x, ‖f (t + h) x - f t x‖ ≤ |h| * C := by
    filter_upwards [hb, self_mem_nhdsWithin] with h hh hne
    have hh0 : h ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    intro x
    have herr : ‖h⁻¹ • (D 0 (t + h) x - D 0 t x) - D 1 t x‖ ≤ 1 := by
      have hbound := enorm_le_holderNorm α (h⁻¹ • (D 0 (t + h) - D 0 t) - D 1 t) x
      have hle : ENNReal.ofReal
          ‖h⁻¹ • (D 0 (t + h) x - D 0 t x) - D 1 t x‖ ≤ ENNReal.ofReal 1 := by
        simpa only [Pi.sub_apply, Pi.smul_apply, ofReal_norm_eq_enorm,
          ENNReal.ofReal_one] using hbound.trans hh.le
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp hle
    have hquo : ‖h⁻¹ • (D 0 (t + h) x - D 0 t x)‖ ≤ C := by
      exact (norm_le_norm_sub_add _ _).trans (add_le_add herr (norm_le_holderNorm_toReal (hDfin 1 t) x))
    rw [hD0] at hquo
    calc
      ‖f (t + h) x - f t x‖ = ‖h • (h⁻¹ • (f (t + h) x - f t x))‖ := by
        rw [smul_smul, mul_inv_cancel₀ hh0, one_smul]
      _ = |h| * ‖h⁻¹ • (f (t + h) x - f t x)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |h| * C := mul_le_mul_of_nonneg_left hquo (abs_nonneg h)
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_nhdsWithin_iff.mp hp] with h hh
  by_cases hh0 : h = 0
  · intro x
    simp only [hh0, add_zero, sub_self, norm_zero, abs_zero, zero_mul, le_rfl]
  · exact hh (by simpa only [mem_compl_iff, mem_singleton_iff] using hh0)

/-- Uniform time increments and continuous slices imply joint continuity.
No separate continuity theorem is used as a substitute for joint continuity. -/
theorem IsSmoothHolderValued.continuous_uncurry {α : ℝ} {f : ℝ → Pt d → E}
    (hf : IsSmoothHolderValued α f) (hc : ∀ t, Continuous (f t)) :
    Continuous (fun q : ℝ × Pt d => f q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  obtain ⟨C, _, hb⟩ := hf.locally_uniform_time_bound t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hdelta : Tendsto (fun q : ℝ × Pt d => q.1 - t) (𝓝 (t, x)) (𝓝 0) := by
    have hc : Continuous (fun q : ℝ × Pt d => q.1 - t) :=
      continuous_fst.sub continuous_const
    simpa only [sub_self] using hc.tendsto (t, x)
  have hbq : ∀ᶠ q : ℝ × Pt d in 𝓝 (t, x),
      ∀ y, ‖f q.1 y - f t y‖ ≤ |q.1 - t| * C := by
    filter_upwards [hdelta.eventually hb] with q hq
    intro y
    have heq : t + (q.1 - t) = q.1 := by ring
    simpa only [heq] using hq y
  have htime : Tendsto (fun q : ℝ × Pt d => |q.1 - t| * C) (𝓝 (t, x)) (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using hdelta.abs.mul_const C
  have hspace : Tendsto (fun q : ℝ × Pt d => ‖f t q.2 - f t x‖)
      (𝓝 (t, x)) (𝓝 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp
      ((hc t).continuousAt.tendsto.comp (continuous_snd.tendsto (t, x)))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using htime.add hspace)
  filter_upwards [hbq] with q hq
  calc
    ‖f q.1 q.2 - f t x‖ = ‖(f q.1 q.2 - f t q.2) + (f t q.2 - f t x)‖ := by
      congr 1
      abel
    _ ≤ ‖f q.1 q.2 - f t q.2‖ + ‖f t q.2 - f t x‖ := norm_add_le _ _
    _ ≤ |q.1 - t| * C + ‖f t q.2 - f t x‖ := add_le_add (hq q.2) le_rfl

theorem IsSmoothHolderValued.holderNorm_finite {α : ℝ} {f : ℝ → Pt d → E}
    (hf : IsSmoothHolderValued α f) (t : ℝ) : holderNorm α (f t) < ⊤ := by
  obtain ⟨D, hD0, hDfin, _⟩ := hf
  simpa only [hD0] using hDfin 0 t

/-- The prescribed continuous slices, with their proved uniform bounds,
viewed in the actual Banach space of bounded continuous functions. -/
def IsSmoothHolderValued.asBCF {α : ℝ} {f : ℝ → Pt d → E}
    (hf : IsSmoothHolderValued α f) (hc : ∀ t, Continuous (f t)) (t : ℝ) : Pt d →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (f t) (hc t)
    (holderNorm α (f t)).toReal (norm_le_holderNorm_toReal (hf.holderNorm_finite t))

@[simp] theorem IsSmoothHolderValued.asBCF_apply {α : ℝ} {f : ℝ → Pt d → E}
    (hf : IsSmoothHolderValued α f) (hc : ∀ t, Continuous (f t)) (t : ℝ) (x : Pt d) :
    hf.asBCF hc t x = f t x := rfl

theorem IsSmoothHolderValued.continuous_asBCF {α : ℝ} {f : ℝ → Pt d → E}
    (hf : IsSmoothHolderValued α f) (hc : ∀ t, Continuous (f t)) :
    Continuous (hf.asBCF hc) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨C, hC, hb⟩ := hf.locally_uniform_time_bound t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hdelta : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hcont : Continuous (fun s : ℝ => s - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hcont.tendsto t
  have hnorm : ∀ᶠ s in 𝓝 t, ‖hf.asBCF hc s - hf.asBCF hc t‖ ≤ |s - t| * C := by
    filter_upwards [hdelta.eventually hb] with s hs
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (abs_nonneg _) hC)).mpr
    intro x
    change ‖f s x - f t x‖ ≤ _
    have heq : t + (s - t) = s := by ring
    simpa only [heq] using hs x
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hnorm
    (by simpa only [abs_zero, zero_mul] using hdelta.abs.mul_const C)

theorem IsTimeSmoothForce.continuous_uncurry {f : ℝ → Pt d → Pt d}
    (hf : IsTimeSmoothForce f) : Continuous (fun q : ℝ × Pt d => f q.1 q.2) :=
  (hf.smooth_holder (1 / 2) (by norm_num) (by norm_num)).continuous_uncurry
    (fun t => (hf.smooth_slice t).continuous)

end AnomDiss
