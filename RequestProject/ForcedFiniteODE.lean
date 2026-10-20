module

public import RequestProject.FlowTools

/-!
# Finite-dimensional dissipative ODEs with continuous forcing

A smooth spatial cutoff gives a bounded Lipschitz field. The cutoff preserves
dissipativity, so its solution has an energy bound independent of the cutoff
radius. Choosing the cutoff to be one on the resulting ball gives a solution
of the original nonlinear equation throughout the prescribed time interval.
-/

@[expose] public section

open Set Filter Topology Real
open scoped NNReal ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A dissipative `C¹` nonlinear field with bounded continuous forcing has a
solution on every finite forward interval. The energy bound is independent
of any growth bound on the nonlinear field. -/
theorem exists_dissipative_forced_ode (g : E → E) (hg : ContDiff ℝ 1 g)
    (hdiss : ∀ x, ⟪x, g x⟫_ℝ ≤ 0) (b : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hb : ContinuousOn b (Icc 0 T)) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ t ∈ Icc 0 T, ‖b t‖ ≤ B) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧
      (∀ t ∈ Icc 0 T, HasDerivAt u (g (u t) + b t) t) ∧
      ∀ t ∈ Icc 0 T, ‖u t‖ ^ 2 ≤ (‖x₀‖ ^ 2 + B ^ 2 * t) * Real.exp t := by
  let Q : ℝ := (‖x₀‖ ^ 2 + B ^ 2 * T) * Real.exp T
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let R : ℝ := Real.sqrt Q + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  let gc : E → E := fun x => χ x • g x
  have hgc : ContDiff ℝ 1 gc := χ.contDiff.smul hg
  have hgcSupport : HasCompactSupport gc := χ.hasCompactSupport.smul_right
  obtain ⟨M, hM⟩ := hgcSupport.exists_bound_of_continuous hgc.continuous
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgcSupport hgc (by simp)
  let c : ℝ → ℝ := fun t => max 0 (min t T)
  have hc : Continuous c := by fun_prop
  have hcm : ∀ t, c t ∈ Icc 0 T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcid : ∀ t ∈ Icc 0 T, c t = t := by
    intro t ht
    dsimp [c]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hbc : Continuous (fun t => b (c t)) := hb.comp_continuous hc hcm
  let V : ℝ → E → E := fun t x => gc x + b (c t)
  have hV : GoodField V ⟨max M 0 + B, by positivity⟩ K := by
    refine ⟨fun x => continuous_const.add hbc, fun t x => ?_, fun t => ?_⟩
    · exact (norm_add_le _ _).trans (add_le_add ((hM x).trans (le_max_left _ _))
        (hbnd (c t) (hcm t)))
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simpa [V, dist_eq_norm] using hK.dist_le_mul x y
  let u : ℝ → E := fun t => gflow V 0 t x₀
  have hu0 : u 0 = x₀ := hV.gflow_self 0 x₀
  have hud : ∀ t, HasDerivAt u (V t (u t)) t := fun t => hV.hasDerivAt_gflow 0 t x₀
  have huc : Continuous u := hV.continuous_gflow_time 0 x₀
  have hcutdiss : ∀ x, ⟪x, gc x⟫_ℝ ≤ 0 := by
    intro x
    dsimp [gc]
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos χ.nonneg (hdiss x)
  let e : ℝ → ℝ := fun t => ‖u t‖ ^ 2
  let ed : ℝ → ℝ := fun t => 2 * ⟪u t, V t (u t)⟫_ℝ
  have hed : ∀ t, HasDerivAt e (ed t) t := fun t => (hud t).norm_sq
  have hedb : ∀ t, ed t ≤ e t + B ^ 2 := by
    intro t
    have h1 := hcutdiss (u t)
    have h2 := real_inner_le_norm (u t) (b (c t))
    have h3 := hbnd (c t) (hcm t)
    have h4 : ‖u t‖ * ‖b (c t)‖ ≤ ‖u t‖ * B :=
      mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    have h5 := sq_nonneg (‖u t‖ - B)
    dsimp [ed, V, e]
    rw [inner_add_right]
    nlinarith
  have henergy : ∀ t ∈ Icc 0 T, e t ≤ (‖x₀‖ ^ 2 + B ^ 2 * t) * Real.exp t := by
    have hgr := le_gronwallBound_of_liminf_deriv_right_le (f := e) (f' := ed)
      (δ := ‖x₀‖ ^ 2) (K := 1) (ε := B ^ 2) (a := 0) (b := T)
      (huc.norm.pow 2).continuousOn
      (fun t _ r hr => (hed t).hasDerivWithinAt.liminf_right_slope_le hr)
      (by simp only [e, hu0]; exact le_rfl)
      (fun t _ => by simpa only [one_mul] using hedb t)
    intro t ht
    have hbd := (hgr t ht).trans (gronwallBound_le (by norm_num : (0 : ℝ) ≤ 1)
      (sq_nonneg B))
    simpa only [sub_zero, one_mul] using hbd
  have hubd : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ R := by
    intro t ht
    have hle : e t ≤ Q := (henergy t ht).trans (by
      dsimp [Q]
      exact mul_le_mul (by gcongr; exact ht.2) (Real.exp_le_exp.mpr ht.2)
        (Real.exp_pos _).le (by positivity))
    exact (Real.le_sqrt_of_sq_le hle).trans (by dsimp [R]; linarith)
  refine ⟨u, hu0, fun t ht => ?_, henergy⟩
  have hχ : χ (u t) = 1 := χ.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hubd t ht)
  have hv : V t (u t) = g (u t) + b t := by
    dsimp [V, gc]
    rw [hχ, one_smul, hcid t ht]
  simpa only [hv] using hud t

/-- Continuity on the finite interval supplies the forcing bound used above;
no global bound on the forcing or the nonlinear field is assumed. -/
theorem exists_dissipative_forced_ode_of_continuous (g : E → E)
    (hg : ContDiff ℝ 1 g) (hdiss : ∀ x, ⟪x, g x⟫_ℝ ≤ 0)
    (b : ℝ → E) (T : ℝ) (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T)) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧ ∀ t ∈ Icc 0 T, HasDerivAt u (g (u t) + b t) t := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hb
  obtain ⟨u, hu0, hu, -⟩ := exists_dissipative_forced_ode g hg hdiss b T hT hb
    (max B 0) (le_max_right _ _) (fun t ht => (hB t ht).trans (le_max_left _ _)) x₀
  exact ⟨u, hu0, hu⟩

end AnomDiss
