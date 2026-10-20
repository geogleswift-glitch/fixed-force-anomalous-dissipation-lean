module

public import RequestProject.HeatStep
public import RequestProject.FlowBasic

/-!
# The flows used in the Lie splitting

Bounds on the eigenfields `eField c`, the damped controls `B_{μ,ω}` on the unit time interval
(extended constantly outside `[0,1]`), and the canonical inverse flow maps `ψ_i` of the
splitting with `n` steps.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-! ### Bounds on the eigenfields -/

lemma abs_sc_le (α β t : ℝ) : |sc α β t| ≤ |α| + |β| := by
  unfold sc
  calc |α * Real.sin (2 * π * t) + β * Real.cos (2 * π * t)|
      ≤ |α * Real.sin (2 * π * t)| + |β * Real.cos (2 * π * t)| := abs_add_le _ _
    _ ≤ |α| * 1 + |β| * 1 := by
        rw [abs_mul, abs_mul]
        gcongr
        · exact Real.abs_sin_le_one _
        · exact Real.abs_cos_le_one _
    _ = |α| + |β| := by ring

lemma abs_sc_sub_le (α β t t' : ℝ) :
    |sc α β t - sc α β t'| ≤ 2 * π * (|α| + |β|) * |t - t'| := by
  unfold sc
  have h1 := Real.abs_sin_sub_sin_le (2 * π * t) (2 * π * t')
  have h2 := Real.abs_cos_sub_cos_le (2 * π * t) (2 * π * t')
  have e : |2 * π * t - 2 * π * t'| = 2 * π * |t - t'| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
  rw [e] at h1 h2
  calc |α * Real.sin (2 * π * t) + β * Real.cos (2 * π * t) -
        (α * Real.sin (2 * π * t') + β * Real.cos (2 * π * t'))|
      = |α * (Real.sin (2 * π * t) - Real.sin (2 * π * t')) +
          β * (Real.cos (2 * π * t) - Real.cos (2 * π * t'))| := by ring_nf
    _ ≤ |α| * (2 * π * |t - t'|) + |β| * (2 * π * |t - t'|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
    _ = 2 * π * (|α| + |β|) * |t - t'| := by ring

lemma coef_abs_le (c : Fin 4 → ℝ) (i : Fin 4) : |c i| ≤ ‖c‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c i

lemma norm_eField_le (c : Fin 4 → ℝ) (x : Pt 2) : ‖eField c x‖ ≤ 2 * ‖c‖ := by
  rw [eField_eq]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  fin_cases k
  · simp only [pair2, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.norm_eq_abs]
    refine (abs_sc_le _ _ _).trans ?_
    linarith [coef_abs_le c 0, coef_abs_le c 1]
  · simp only [pair2, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.norm_eq_abs]
    refine (abs_sc_le _ _ _).trans ?_
    linarith [coef_abs_le c 2, coef_abs_le c 3]

lemma norm_eField_sub_le (c : Fin 4 → ℝ) (x y : Pt 2) :
    ‖eField c x - eField c y‖ ≤ 4 * π * ‖c‖ * ‖x - y‖ := by
  rw [eField_eq]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have hx1 : |x 1 - y 1| ≤ ‖x - y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (x - y) 1
  have hx0 : |x 0 - y 0| ≤ ‖x - y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (x - y) 0
  fin_cases k
  · simp only [pair2, Fin.zero_eta, Fin.isValue, Pi.sub_apply, Matrix.cons_val_zero,
      Real.norm_eq_abs]
    refine (abs_sc_sub_le _ _ _ _).trans ?_
    have := coef_abs_le c 0; have := coef_abs_le c 1
    calc 2 * π * (|c 0| + |c 1|) * |x 1 - y 1| ≤ 2 * π * (2 * ‖c‖) * ‖x - y‖ := by
          gcongr; linarith
      _ = 4 * π * ‖c‖ * ‖x - y‖ := by ring
  · simp only [pair2, Fin.mk_one, Fin.isValue, Pi.sub_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Real.norm_eq_abs]
    refine (abs_sc_sub_le _ _ _ _).trans ?_
    have := coef_abs_le c 2; have := coef_abs_le c 3
    calc 2 * π * (|c 2| + |c 3|) * |x 0 - y 0| ≤ 2 * π * (2 * ‖c‖) * ‖x - y‖ := by
          gcongr; linarith
      _ = 4 * π * ‖c‖ * ‖x - y‖ := by ring

lemma eField_sub_coef (c c' : Fin 4 → ℝ) (x : Pt 2) :
    eField c x - eField c' x = eField (c - c') x := by
  simp only [eField, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-! ### The damped controls on the unit interval -/

variable {L M : ℕ} {S : ℕ → ℝ}

/-- Clamping to `[0,1]`. -/
def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

lemma clamp01_mem (s : ℝ) : clamp01 s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma clamp01_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : clamp01 s = s := by
  simp [clamp01, hs.1, hs.2]

lemma continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

lemma abs_clamp01_sub_le (s s' : ℝ) : |clamp01 s - clamp01 s'| ≤ |s - s'| := by
  unfold clamp01
  have h1 := abs_max_sub_max_le_max (0:ℝ) (min s 1) 0 (min s' 1)
  have h2 := abs_min_sub_min_le_max s 1 s' 1
  simp only [sub_self, abs_zero, sub_self] at h1 h2
  refine h1.trans ?_
  rw [max_eq_right (abs_nonneg _)]
  refine h2.trans ?_
  rw [max_eq_left (abs_nonneg _)]

/-- The field used for the splitting flows: `B_{μ,ω}` on `[0,1]`, extended constantly. -/
def splitField (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ) (x : Pt 2) : Pt 2 :=
  dampedB cf μ w (clamp01 s) x

lemma splitField_eq_of_mem (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : splitField cf μ w s = dampedB cf μ w s := by
  funext x; simp [splitField, clamp01_of_mem hs]

/-- A uniform bound for the control coefficients. -/
def coefBound (cf : ControlFamily L M S) : ℝ := max 0 (Classical.choose (cf.mixed 0))

/-- A uniform bound for the time derivative of the control coefficients. -/
def coefDerivBound (cf : ControlFamily L M S) : ℝ := max 0 (Classical.choose (cf.mixed 1))

lemma coefBound_nonneg (cf : ControlFamily L M S) : 0 ≤ coefBound cf := le_max_left _ _

lemma coefDerivBound_nonneg (cf : ControlFamily L M S) : 0 ≤ coefDerivBound cf := le_max_left _ _

lemma norm_coef_le (cf : ControlFamily L M S) (w : Fin L → Bool × Pt 2) (s : ℝ) :
    ‖cf.coef w s‖ ≤ coefBound cf := by
  have := Classical.choose_spec (cf.mixed 0) w s
  simp only [iteratedDeriv_zero] at this
  exact this.trans (le_max_right _ _)

lemma norm_deriv_coef_le (cf : ControlFamily L M S) (w : Fin L → Bool × Pt 2) (s : ℝ) :
    ‖deriv (cf.coef w) s‖ ≤ coefDerivBound cf := by
  have := Classical.choose_spec (cf.mixed 1) w s
  have h2 : iteratedDeriv 1 (cf.coef w) s = deriv (cf.coef w) s := by rw [iteratedDeriv_one]
  rw [← h2]
  exact this.trans (le_max_right _ _)

lemma norm_dampedCoef_le (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖dampedCoef cf μ w s‖ ≤ 2 * coefBound cf := by
  unfold dampedCoef
  have hint : ‖∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r‖ ≤
      coefBound cf * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    rw [uIoc_of_le hs.1] at hr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-μ * (s - r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hμ.1, hr.2])
    calc Real.exp (-μ * (s - r)) * ‖cf.coef w.1 r‖ ≤ 1 * coefBound cf := by
          gcongr
          · exact norm_coef_le cf w.1 r
      _ = coefBound cf := one_mul _
  have hs0 : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2
  calc ‖cf.coef w.1 s - μ • ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r‖
      ≤ ‖cf.coef w.1 s‖ + |μ| * ‖∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ coefBound cf + 1 * (coefBound cf * 1) := by
        gcongr
        · exact norm_coef_le cf w.1 s
        · rw [abs_of_nonneg hμ.1]; exact hμ.2
        · exact hint.trans (by gcongr; exact coefBound_nonneg cf)
    _ = 2 * coefBound cf := by ring

lemma norm_dampedCoef_sub_le (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hs' : s' ∈ Icc (0 : ℝ) 1) :
    ‖dampedCoef cf μ w s - dampedCoef cf μ w s'‖ ≤
      (coefDerivBound cf + 2 * coefBound cf) * |s - s'| := by
  have hd : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (dampedCoef cf μ w)
      (deriv (cf.coef w.1) r - μ • dampedCoef cf μ w r) (Icc 0 1) r :=
    fun r _ => (hasDerivAt_dampedCoef cf μ w r).hasDerivWithinAt
  have hb : ∀ r ∈ Icc (0 : ℝ) 1, ‖deriv (cf.coef w.1) r - μ • dampedCoef cf μ w r‖ ≤
      coefDerivBound cf + 2 * coefBound cf := by
    intro r hr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1]
    calc ‖deriv (cf.coef w.1) r‖ + μ * ‖dampedCoef cf μ w r‖
        ≤ coefDerivBound cf + 1 * (2 * coefBound cf) :=
          add_le_add (norm_deriv_coef_le cf w.1 r)
            (mul_le_mul hμ.2 (norm_dampedCoef_le cf hμ w hr) (norm_nonneg _) zero_le_one)
      _ = coefDerivBound cf + 2 * coefBound cf := by ring
  have := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hs' hs
  rwa [Real.norm_eq_abs] at this

/-- The spatial bound `M` of the splitting field. -/
def splitM (cf : ControlFamily L M S) : ℝ≥0 := ⟨4 * coefBound cf, by
  have := coefBound_nonneg cf; positivity⟩

/-- The spatial Lipschitz constant `K` of the splitting field. -/
def splitK (cf : ControlFamily L M S) : ℝ≥0 := ⟨8 * π * coefBound cf, by
  have := coefBound_nonneg cf; positivity⟩

/-- The time-Lipschitz constant of the splitting field. -/
def splitLt (cf : ControlFamily L M S) : ℝ := 2 * (coefDerivBound cf + 2 * coefBound cf)

lemma splitField_apply (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ)
    (x : Pt 2) : splitField cf μ w s x = eField (dampedCoef cf μ w (clamp01 s)) (x - w.2) := by
  simp [splitField, dampedB_eq]

theorem splitField_good (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) : GoodField (splitField cf μ w) (splitM cf) (splitK cf) where
  cont x := by
    have hc : Continuous (dampedCoef cf μ w) :=
      continuous_iff_continuousAt.2 fun s => (hasDerivAt_dampedCoef cf μ w s).continuousAt
    simp_rw [splitField_apply, ← eFieldCLM_apply]
    exact (eFieldCLM (x - w.2)).continuous.comp (hc.comp continuous_clamp01)
  bound s x := by
    rw [splitField_apply]
    refine (norm_eField_le _ _).trans ?_
    have := norm_dampedCoef_le cf hμ w (clamp01_mem s)
    change 2 * ‖dampedCoef cf μ w (clamp01 s)‖ ≤ 4 * coefBound cf
    linarith
  lip s := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, splitField_apply, splitField_apply]
    refine (norm_eField_sub_le _ _ _).trans ?_
    have := norm_dampedCoef_le cf hμ w (clamp01_mem s)
    have e : x - w.2 - (y - w.2) = x - y := by abel
    rw [e]
    simp only [splitK, NNReal.coe_mk]
    calc 4 * π * ‖dampedCoef cf μ w (clamp01 s)‖ * ‖x - y‖
        ≤ 4 * π * (2 * coefBound cf) * ‖x - y‖ := by gcongr
      _ = 8 * π * coefBound cf * ‖x - y‖ := by ring

lemma splitField_time_lip (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (s s' : ℝ) (x : Pt 2) :
    ‖splitField cf μ w s x - splitField cf μ w s' x‖ ≤ splitLt cf * |s - s'| := by
  rw [splitField_apply, splitField_apply, eField_sub_coef]
  refine (norm_eField_le _ _).trans ?_
  have h1 := norm_dampedCoef_sub_le cf hμ w (clamp01_mem s) (clamp01_mem s')
  have h2 := abs_clamp01_sub_le s s'
  have h3 : 0 ≤ coefDerivBound cf + 2 * coefBound cf := by
    have := coefDerivBound_nonneg cf; have := coefBound_nonneg cf; linarith
  simp only [splitLt]
  nlinarith

end AnomDiss
