module

public import RequestProject.HeatEvolution

/-!
# Heat evolution at the initial endpoint

The initial endpoint uses a right derivative. Spatial differentiation commutes
with the genuine Gaussian average, so the positive-time heat equation extends
continuously to the initial value for periodic `C²` data.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem continuous_heatOp_variance_space {f : Pt 2 → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun p : ℝ≥0 × Pt 2 => heatOp p.1 f p.2) := by
  simp_rw [heatOp_eq_scaled hf]
  refine continuous_of_dominated (bound := fun _ => C)
    (fun p => by
      have hshift : Continuous (fun ζ : Pt 2 => p.2 + Real.sqrt (p.1 : ℝ) • ζ) := by
        fun_prop
      simpa only [Function.comp_def] using
        (hf.comp hshift).aestronglyMeasurable (μ := gauss2 1))
    (fun _ => Eventually.of_forall fun ζ => hC _)
    (integrable_const C) (Eventually.of_forall fun ζ => ?_)
  have hshift : Continuous (fun p : ℝ≥0 × Pt 2 => p.2 + Real.sqrt (p.1 : ℝ) • ζ) := by
    fun_prop
  simpa only [Function.comp_def] using hf.comp hshift

theorem lap_heatOp_C2 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) (v : ℝ≥0) (x : Pt 2) :
    lap (heatOp v f) x = heatOp v (lap f) x := by
  have hqp : IsQP 0 f := isQP_zero_iff.2 hp
  have hi (i : Fin 2) : Integrable (fun ζ => pd i (pd i f) (x + ζ)) (gauss2 v) := by
    have hc := continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf i) i
    obtain ⟨C, hC⟩ := (isQP_pd2 hqp hf i i).bdd hc
    exact integrable_gauss2_of_bdd hc hC v x
  unfold lap
  simp_rw [pd2_heatOp hqp hf]
  unfold heatOp
  rw [integral_finset_sum _ fun i _ => hi i]

theorem continuous_lap_C2 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f) :
    Continuous (lap f) :=
  continuous_finset_sum _ fun i _ =>
    continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf i) i

theorem periodic_lap_C2 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) : IsPeriodic (lap f) := by
  intro x m
  unfold lap
  apply Finset.sum_congr rfl
  intro i _
  exact (isQP_zero_iff.1 (isQP_pd2 (isQP_zero_iff.2 hp) hf i i)) x m

/-- The correct one-sided heat derivative at the initial endpoint. -/
theorem hasDerivWithinAt_heatOp_zero {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {ν : ℝ} (hν : 0 ≤ ν) (x : Pt 2) :
    HasDerivWithinAt (fun s => heatOp (Real.toNNReal (2 * ν * s)) f x)
      (ν • lap f x) (Ici 0) 0 := by
  obtain ⟨C, hC⟩ := (isQP_zero_iff.2 hp).bdd hf.continuous
  have hc : Continuous (fun s : ℝ => heatOp (Real.toNNReal (2 * ν * s)) f x) :=
    (continuous_heatOp_variance_space hf.continuous hC).comp
      ((continuous_real_toNNReal.comp (continuous_const.mul continuous_id)).prodMk
        continuous_const)
  have hlc := continuous_lap_C2 hf
  obtain ⟨D, hD⟩ := (isQP_zero_iff.2 (periodic_lap_C2 hf hp)).bdd hlc
  have hdcont : Continuous (fun s : ℝ =>
      ν • heatOp (Real.toNNReal (2 * ν * s)) (lap f) x) := by
    refine (continuous_const : Continuous (fun _ : ℝ => ν)).fun_smul ?_
    simpa only [Function.comp_def] using
      (continuous_heatOp_variance_space hlc hD).comp
        (by fun_prop : Continuous fun s : ℝ => (Real.toNNReal (2 * ν * s), x))
  have hlim : Tendsto (fun s : ℝ =>
      ν • heatOp (Real.toNNReal (2 * ν * s)) (lap f) x) (𝓝[>] 0)
      (𝓝 (ν • lap f x)) := by
    simpa [heatOp_zero hlc] using
      (hdcont.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun s hs => (hasDerivAt_heatOp_C2 hf hp hν hs x).differentiableAt.differentiableWithinAt)
    hc.continuousAt.continuousWithinAt self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [(hasDerivAt_heatOp_C2 hf hp hν hs x).deriv, lap_heatOp_C2 hf hp]

/-- The heat equation holds with one-sided time derivatives on a closed time slab. -/
theorem hasDerivWithinAt_heatOp_Icc {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : Pt 2) :
    HasDerivWithinAt (fun s => heatOp (Real.toNNReal (2 * ν * s)) f x)
      (ν • lap (heatOp (Real.toNNReal (2 * ν * t)) f) x) (Icc 0 T) t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    have he₀ : heatOp 0 f = f := funext (heatOp_zero hf.continuous)
    simpa only [mul_zero, Real.toNNReal_zero, he₀] using
      (hasDerivWithinAt_heatOp_zero hf hp hν x).mono Icc_subset_Ici_self
  · exact (hasDerivAt_heatOp_C2 hf hp hν h x).hasDerivWithinAt

theorem dt_heatOp_Icc {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {ν T t : ℝ} (hν : 0 ≤ ν) (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (x : Pt 2) :
    dt T (fun s => heatOp (Real.toNNReal (2 * ν * s)) f) t x =
      ν • lap (heatOp (Real.toNNReal (2 * ν * t)) f) x := by
  exact (hasDerivWithinAt_heatOp_Icc hf hp hν ht x).derivWithin
    (uniqueDiffOn_Icc hT t ht)

end AnomDiss
