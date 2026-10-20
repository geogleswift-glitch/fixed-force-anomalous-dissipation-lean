module

public import RequestProject.SplitRep

/-!
# Joint continuity (hence measurability) of the canonical split maps

The control coefficients depend continuously on the block parameters, uniformly in time; hence
so do the splitting fields, their flows, and the split maps `Ψ_n`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- Flows of a family of good fields depending uniformly continuously on a parameter are jointly
continuous in the parameter and the initial point. -/
lemma continuous_gflow_param {Ω E : Type*} [TopologicalSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {V : Ω → ℝ → E → E} {M K : ℝ≥0}
    (hV : ∀ w, GoodField (V w) M K)
    (hcont : ∀ w₀, ∀ ε > 0, ∀ᶠ w in 𝓝 w₀, ∀ s x, ‖V w s x - V w₀ s x‖ ≤ ε) (t₀ t : ℝ) :
    Continuous fun p : Ω × E => gflow (V p.1) t₀ t p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨w₀, x₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set T := |t - t₀|
  set A := T * Real.exp (K * T) + 1
  set B := Real.exp (K * T)
  have hA : 0 < A := by positivity
  have hB : 0 < B := Real.exp_pos _
  have h1 := hcont w₀ (ε / (2 * A)) (by positivity)
  have h2 : ∀ᶠ x in 𝓝 x₀, dist x x₀ < ε / (2 * B) :=
    Metric.ball_mem_nhds x₀ (by positivity)
  have h1' := (continuousAt_fst (p := (w₀, x₀))).eventually h1
  have h2' := (continuousAt_snd (p := (w₀, x₀))).eventually h2
  filter_upwards [h1', h2'] with p hp1 hp2
  calc dist (gflow (V p.1) t₀ t p.2) (gflow (V w₀) t₀ t x₀)
      ≤ dist (gflow (V p.1) t₀ t p.2) (gflow (V w₀) t₀ t p.2) +
          dist (gflow (V w₀) t₀ t p.2) (gflow (V w₀) t₀ t x₀) := dist_triangle _ _ _
    _ ≤ ε / (2 * A) * T * Real.exp (K * T) + B * dist p.2 x₀ := by
        gcongr
        · exact (hV p.1).dist_gflow_field_le (hV w₀) (by positivity) t₀ t
            (fun s _ x => hp1 s x) p.2
        · have := (hV w₀).dist_gflow_le t₀ t p.2 x₀
          simpa [B, mul_comm] using this
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_le_of_lt
        · rw [show ε / (2 * A) * T * Real.exp (K * T) = ε / 2 * ((T * Real.exp (K * T)) / A) by
            field_simp]
          have : T * Real.exp (K * T) / A ≤ 1 := by
            rw [div_le_one hA]; linarith
          nlinarith
        · rw [show ε / 2 = B * (ε / (2 * B)) by field_simp]
          exact mul_lt_mul_of_pos_left hp2 hB
    _ = ε := by ring

variable {L M : ℕ} {S : ℕ → ℝ}

/-- The control coefficients depend continuously on the block parameters, uniformly in time. -/
lemma coef_uniform (cf : ControlFamily L M S) (w₀ : Fin L → Bool × Pt 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 w₀, ∀ r, ‖cf.coef w r - cf.coef w₀ r‖ ≤ ε := by
  set ιs : Fin L → Bool := fun i => (w₀ i).1
  set p₀ : Fin L → Pt 2 := fun i => (w₀ i).2
  set f : (Fin L → Pt 2) → Icc cf.a₀ cf.b₀ → (Fin 4 → ℝ) :=
    fun p r => cf.coef (fun i => (ιs i, p i)) r
  have hf : Continuous (Function.uncurry f) :=
    (cf.smooth ιs).continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hU := (Metric.tendstoUniformly_iff.1 (hf.tendstoUniformly f p₀)) ε hε
  have hpos : Continuous fun w : Fin L → Bool × Pt 2 => fun i => (w i).2 :=
    continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  have hbool : Continuous fun w : Fin L → Bool × Pt 2 => fun i => (w i).1 :=
    continuous_pi fun i => continuous_fst.comp (continuous_apply i)
  have h1 : ∀ᶠ w in 𝓝 w₀, ∀ r, dist (f p₀ r) (f (fun i => (w i).2) r) < ε :=
    hpos.continuousAt.eventually hU
  have h2 : ∀ᶠ w in 𝓝 w₀, (fun i => (w i).1) = ιs :=
    hbool.continuousAt.eventually (isOpen_discrete {ιs} |>.mem_nhds rfl)
  have hw₀ : w₀ = fun i => (ιs i, p₀ i) := funext fun i => rfl
  filter_upwards [h1, h2] with w hw1 hw2
  have hw : w = fun i => (ιs i, (w i).2) := funext fun i => by
    rw [← congrFun hw2 i]
  intro r
  by_cases hr : r ∈ Icc cf.a₀ cf.b₀
  · have := hw1 ⟨r, hr⟩
    rw [dist_comm, dist_eq_norm] at this
    simp only [f] at this
    rw [hw, hw₀]; exact this.le
  · rw [cf.support w r hr, cf.support w₀ r hr, sub_zero, norm_zero]; exact hε.le

/-- The damped coefficients depend continuously on the parameter, uniformly on `[0,1]`. -/
lemma dampedCoef_uniform (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w₀ : BlockParam L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 w₀, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖dampedCoef cf μ w s - dampedCoef cf μ w₀ s‖ ≤ ε := by
  have h := (continuous_fst.continuousAt (x := w₀)).eventually (coef_uniform cf w₀.1 (half_pos hε))
  filter_upwards [h] with w hw s hs
  have hc := (cf.contDiff_coef w.1).continuous
  have hc₀ := (cf.contDiff_coef w₀.1).continuous
  have hi : ∀ v : Fin L → Bool × Pt 2, IntervalIntegrable
      (fun r => Real.exp (-μ * (s - r)) • cf.coef v r) volume 0 s := fun v =>
    (by have := (cf.contDiff_coef v).continuous; fun_prop :
      Continuous fun r => Real.exp (-μ * (s - r)) • cf.coef v r).intervalIntegrable _ _
  have hint : ‖(∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r) -
      ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w₀.1 r‖ ≤ ε / 2 * |s - 0| := by
    rw [← intervalIntegral.integral_sub (hi w.1) (hi w₀.1)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    rw [uIoc_of_le hs.1] at hr
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-μ * (s - r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hμ.1, hr.2])
    calc Real.exp (-μ * (s - r)) * ‖cf.coef w.1 r - cf.coef w₀.1 r‖ ≤ 1 * (ε / 2) := by
          gcongr
          exact hw r
      _ = ε / 2 := one_mul _
  have hs0 : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2
  unfold dampedCoef
  calc ‖cf.coef w.1 s - μ • (∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r) -
        (cf.coef w₀.1 s - μ • ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w₀.1 r)‖
      = ‖(cf.coef w.1 s - cf.coef w₀.1 s) - μ • ((∫ r in (0 : ℝ)..s,
          Real.exp (-μ * (s - r)) • cf.coef w.1 r) -
          ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w₀.1 r)‖ := by
        rw [smul_sub]; congr 1; abel
    _ ≤ ‖cf.coef w.1 s - cf.coef w₀.1 s‖ + |μ| * ‖(∫ r in (0 : ℝ)..s,
          Real.exp (-μ * (s - r)) • cf.coef w.1 r) -
          ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w₀.1 r‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ε / 2 + 1 * (ε / 2 * 1) := by
        gcongr
        · exact hw s
        · rw [abs_of_nonneg hμ.1]; exact hμ.2
        · exact hint.trans (by gcongr)
    _ = ε := by ring

/-- The splitting fields depend continuously on the parameter, uniformly in time and space. -/
lemma splitField_uniform (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w₀ : BlockParam L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 w₀, ∀ s x, ‖splitField cf μ w s x - splitField cf μ w₀ s x‖ ≤ ε := by
  have hC := coefBound_nonneg cf
  set A : ℝ := 8 * π * coefBound cf + 1
  have hA : 0 < A := by positivity
  have h1 := dampedCoef_uniform cf hμ w₀ (by positivity : 0 < ε / 4)
  have h2 : ∀ᶠ w in 𝓝 w₀, dist w.2 w₀.2 < ε / (2 * A) :=
    (continuous_snd.continuousAt (x := w₀)).eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [h1, h2] with w hw1 hw2 s x
  rw [splitField_apply, splitField_apply]
  set c := dampedCoef cf μ w (clamp01 s)
  set c₀ := dampedCoef cf μ w₀ (clamp01 s)
  have hc₀ : ‖c₀‖ ≤ 2 * coefBound cf := norm_dampedCoef_le cf hμ w₀ (clamp01_mem s)
  have e : eField c (x - w.2) - eField c₀ (x - w₀.2) =
      eField (c - c₀) (x - w.2) + (eField c₀ (x - w.2) - eField c₀ (x - w₀.2)) := by
    rw [← eField_sub_coef]; abel
  rw [e]
  have hd : ‖x - w.2 - (x - w₀.2)‖ = dist w.2 w₀.2 := by
    rw [dist_eq_norm, ← norm_neg]; congr 1; abel
  calc ‖eField (c - c₀) (x - w.2) + (eField c₀ (x - w.2) - eField c₀ (x - w₀.2))‖
      ≤ 2 * ‖c - c₀‖ + 4 * π * ‖c₀‖ * dist w.2 w₀.2 := by
        refine (norm_add_le _ _).trans (add_le_add (norm_eField_le _ _) ?_)
        rw [← hd]; exact norm_eField_sub_le _ _ _
    _ ≤ 2 * (ε / 4) + A * (ε / (2 * A)) := by
        gcongr
        · exact hw1 _ (clamp01_mem s)
        · calc 4 * π * ‖c₀‖ ≤ 4 * π * (2 * coefBound cf) := by gcongr
            _ ≤ A := by simp only [A]; linarith
    _ = ε := by field_simp; ring

/-- Joint continuity of the canonical inverse flow maps in the parameter and the point. -/
lemma continuous_canonPsi_param (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (n i : ℕ) : Continuous fun p : BlockParam L × Pt 2 => canonPsi cf μ p.1 n i p.2 :=
  continuous_gflow_param (V := fun w => splitField cf μ w) (fun w => splitField_good cf hμ w)
    (fun w₀ _ hε => splitField_uniform cf hμ w₀ hε) _ _

/-- Joint continuity of the split maps built from a jointly continuous family of maps. -/
lemma continuous_splitMap_param {Ω : Type*} [TopologicalSpace Ω] {ψ : Ω → ℕ → Pt 2 → Pt 2}
    (hψ : ∀ i, Continuous fun p : Ω × Pt 2 => ψ p.1 i p.2) (j : ℕ) :
    Continuous fun p : (Ω × (ℕ → Pt 2)) × Pt 2 => splitMap (ψ p.1.1) p.1.2 j p.2 := by
  induction j with
  | zero => exact continuous_snd
  | succ j ih =>
    have h1 : Continuous fun p : (Ω × (ℕ → Pt 2)) × Pt 2 =>
        (p.1, ψ p.1.1 (j + 1) (p.2 + p.1.2 (j + 1))) :=
      continuous_fst.prodMk ((hψ (j + 1)).comp (continuous_fst.fst.prodMk
        (continuous_snd.add ((continuous_apply (j + 1)).comp continuous_fst.snd))))
    exact ih.comp h1

/-- Joint measurability of the split maps in the parameter, the increments and the point. -/
theorem measurable_canonSplit (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (n : ℕ) : Measurable (Function.uncurry fun (o : BlockParam L × (ℕ → Pt 2)) =>
      splitMap (canonPsi cf μ o.1 n) o.2 n) :=
  (continuous_splitMap_param (ψ := fun w => canonPsi cf μ w n)
    (fun i => continuous_canonPsi_param cf hμ n i) n).measurable

end AnomDiss
