module

public import RequestProject.SplitFourierBound
public import RequestProject.FlowSmoothMain

/-!
# The damped field `B_{μ,ω}` is a smooth field

`B_{μ,ω}(s, x) = ∑ᵢ cᵢ(s) eᵢ(x - z₀)` is jointly `C^∞`, and its spatial derivatives of order `k`
are bounded by `4 (1 + μ) ‖c‖_∞ (2π)^k`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff NNReal

noncomputable section

namespace AnomDiss

/-! ### Trigonometric profiles -/

/-- A smooth function `ℝ → ℝ` all of whose derivatives are bounded by `1`. -/
def UnitTrig (g : ℝ → ℝ) : Prop := ContDiff ℝ ∞ g ∧ ∀ k x, |iteratedDeriv k g x| ≤ 1

lemma unitTrig_sin : UnitTrig Real.sin :=
  ⟨Real.contDiff_sin, fun k x => Real.abs_iteratedDeriv_sin_le_one k x⟩

lemma unitTrig_cos : UnitTrig Real.cos :=
  ⟨Real.contDiff_cos, fun k x => Real.abs_iteratedDeriv_cos_le_one k x⟩

lemma norm_iteratedFDeriv_trig_comp {g : ℝ → ℝ} (hg : UnitTrig g) (ℓ : Pt 2 →L[ℝ] ℝ) (e : Pt 2)
    (k : ℕ) (y : Pt 2) :
    ‖iteratedFDeriv ℝ k (fun y => g (ℓ y) • e) y‖ ≤ ‖ℓ‖ ^ k * ‖e‖ := by
  have hk : (k : WithTop ℕ∞) ≤ ∞ := natCast_le_inf k
  have hgl : ContDiff ℝ ∞ (g ∘ ℓ) := hg.1.comp ℓ.contDiff
  have e1 : (fun y => g (ℓ y) • e) = ContinuousLinearMap.toSpanSingleton ℝ e ∘ (g ∘ ℓ) := by
    funext y; simp
  rw [e1]
  refine ((ContinuousLinearMap.toSpanSingleton ℝ e).norm_iteratedFDeriv_comp_left
    hgl.contDiffAt hk).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton, mul_comm]
  gcongr
  rw [ℓ.iteratedFDeriv_comp_right hg.1 y hk]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : ‖iteratedFDeriv ℝ k g (ℓ y)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]; exact hg.2 k _
  calc ‖iteratedFDeriv ℝ k g (ℓ y)‖ * ‖ℓ‖ ^ k ≤ 1 * ‖ℓ‖ ^ k := by gcongr
    _ = _ := one_mul _

/-- The linear form `y ↦ 2π y_k`. -/
def twoPiProj (k : Fin 2) : Pt 2 →L[ℝ] ℝ := (2 * Real.pi) • prj k

lemma norm_twoPiProj_le (k : Fin 2) : ‖twoPiProj k‖ ≤ 2 * Real.pi := by
  unfold twoPiProj
  refine (norm_smul_le (2 * Real.pi) (prj k)).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 2 * Real.pi * ‖prj k‖ ≤ 2 * Real.pi * 1 := by
        gcongr; exact norm_prj_le k
    _ = _ := mul_one _

/-- The trigonometric profile, linear form and direction of the eigenfield `eᵢ`. -/
def eTrig (i : Fin 4) : ℝ → ℝ := if i = 0 ∨ i = 2 then Real.sin else Real.cos

def eLin (i : Fin 4) : Pt 2 →L[ℝ] ℝ := if i = 0 ∨ i = 1 then twoPiProj 1 else twoPiProj 0

def eVec (i : Fin 4) : Pt 2 := if i = 0 ∨ i = 1 then ev0 else ev1

lemma unitTrig_eTrig (i : Fin 4) : UnitTrig (eTrig i) := by
  unfold eTrig; split_ifs
  · exact unitTrig_sin
  · exact unitTrig_cos

lemma norm_eLin_le (i : Fin 4) : ‖eLin i‖ ≤ 2 * Real.pi := by
  unfold eLin; split_ifs <;> exact norm_twoPiProj_le _

lemma norm_eVec_le (i : Fin 4) : ‖eVec i‖ ≤ 1 := by
  unfold eVec; split_ifs
  · exact norm_ev0
  · exact norm_ev1

lemma eBasis_eq (i : Fin 4) : eBasis i = fun y => eTrig i (eLin i y) • eVec i := by
  funext y
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [eBasis, eTrig, eLin, eVec, twoPiProj, ev0, ev1, mul_comm]

lemma eBasis_iteratedFDeriv_le_pow (i : Fin 4) (k : ℕ) (y : Pt 2) :
    ‖iteratedFDeriv ℝ k (eBasis i) y‖ ≤ (2 * Real.pi) ^ k := by
  rw [eBasis_eq]
  refine (norm_iteratedFDeriv_trig_comp (unitTrig_eTrig i) (eLin i) (eVec i) k y).trans ?_
  calc ‖eLin i‖ ^ k * ‖eVec i‖ ≤ (2 * Real.pi) ^ k * 1 := by
        gcongr
        · exact norm_eLin_le i
        · exact norm_eVec_le i
    _ = _ := mul_one _

/-- Derivative bounds for a translated element of `𝓔`. -/
lemma norm_iteratedFDeriv_eField_sub_le (v : Fin 4 → ℝ) (z : Pt 2) (k : ℕ) (x : Pt 2) :
    ‖iteratedFDeriv ℝ k (fun x => eField v (x - z)) x‖ ≤ 4 * ‖v‖ * (2 * Real.pi) ^ k := by
  have hk : (k : WithTop ℕ∞) ≤ ∞ := natCast_le_inf k
  rw [iteratedFDeriv_comp_sub (f := eField v)]
  have e : eField v = fun y => ∑ i ∈ Finset.univ, v i • eBasis i y := by
    funext y; rfl
  rw [e, iteratedFDeriv_sum (fun i _ => ((contDiff_eBasis i).const_smul (v i)).of_le hk)]
  rw [Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      ‖iteratedFDeriv ℝ k (fun y => v i • eBasis i y) (x - z)‖ ≤ ‖v‖ * (2 * Real.pi) ^ k := by
    intro i _
    rw [iteratedFDeriv_const_smul_apply' ((contDiff_eBasis i).of_le hk).contDiffAt, norm_smul]
    gcongr
    · exact norm_le_pi_norm v i
    · exact eBasis_iteratedFDeriv_le_pow i k _
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring_nf; rfl

/-! ### The damped coefficients -/

variable {L M : ℕ} {S : ℕ → ℝ}

lemma deriv_dampedCoef (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) :
    deriv (dampedCoef cf μ w) = fun s => deriv (cf.coef w.1) s - μ • dampedCoef cf μ w s :=
  funext fun s => (hasDerivAt_dampedCoef cf μ w s).deriv

theorem dampedCoef_contDiff (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) :
    ContDiff ℝ ∞ (dampedCoef cf μ w) := by
  have hd : Differentiable ℝ (dampedCoef cf μ w) := fun s =>
    (hasDerivAt_dampedCoef cf μ w s).differentiableAt
  have hcd : ContDiff ℝ ∞ (deriv (cf.coef w.1)) :=
    (contDiff_infty_iff_deriv.1 (cf.contDiff_coef w.1)).2
  refine contDiff_infty.2 fun n => ?_
  induction n with
  | zero => exact contDiff_zero.2 hd.continuous
  | succ n ih =>
    have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (dampedCoef cf μ w) := by
      refine contDiff_succ_iff_deriv.2 ⟨hd, fun h => absurd h (by simp), ?_⟩
      rw [deriv_dampedCoef]
      exact (hcd.of_le (natCast_le_inf n)).sub (ih.const_smul μ)
    exact_mod_cast this

lemma norm_integral_damped_le (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L)
    (s : ℝ) : ‖∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r‖ ≤ coefBound cf := by
  have hC := coefBound_nonneg cf
  set f : ℝ → Fin 4 → ℝ := fun r => Real.exp (-μ * (s - r)) • cf.coef w.1 r with hf
  have hfc : Continuous f := by
    have := (cf.contDiff_coef w.1).continuous
    simp only [hf]; fun_prop
  have hzero : ∀ r, r ∉ Icc cf.a₀ cf.b₀ → f r = 0 := fun r hr => by
    simp [hf, cf.support w.1 r hr]
  have hbd : ∀ r, r ≤ s → ‖f r‖ ≤ coefBound cf := fun r hr => by
    simp only [hf]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-μ * (s - r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc Real.exp (-μ * (s - r)) * ‖cf.coef w.1 r‖ ≤ 1 * coefBound cf := by
          gcongr
          exact norm_coef_le cf w.1 r
      _ = coefBound cf := one_mul _
  rcases lt_or_ge s 0 with hs | hs
  · have hint : ∫ r in (0 : ℝ)..s, f r = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : Fin 4 → ℝ)) fun r hr => ?_]
      · simp
      · rw [uIcc_of_ge hs.le] at hr
        exact hzero r fun h => by linarith [h.1, hr.2, cf.ha₀]
    show ‖∫ r in (0 : ℝ)..s, f r‖ ≤ _
    rw [hint, norm_zero]; exact hC
  rcases le_or_gt s 1 with hs1 | hs1
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s) (f := f)
      (C := coefBound cf) fun r hr => by
        rw [uIoc_of_le hs] at hr; exact hbd r hr.2
    show ‖∫ r in (0 : ℝ)..s, f r‖ ≤ _
    refine this.trans ?_
    rw [sub_zero, abs_of_nonneg hs]
    nlinarith
  · have hsplit : ∫ r in (0 : ℝ)..s, f r = ∫ r in (0 : ℝ)..1, f r := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
        (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
      rw [intervalIntegral.integral_congr (a := 1) (b := s) (g := fun _ => (0 : Fin 4 → ℝ))
        fun r hr => ?_]
      · simp
      · rw [uIcc_of_le hs1.le] at hr
        exact hzero r fun h => by linarith [h.2, hr.1, cf.hb₀]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (f := f)
      (C := coefBound cf) fun r hr => by
        rw [uIoc_of_le zero_le_one] at hr; exact hbd r (by linarith [hr.2])
    show ‖∫ r in (0 : ℝ)..s, f r‖ ≤ _
    rw [hsplit]
    simpa using this

/-- `‖c_μ(s)‖ ≤ (1 + μ) ‖c‖_∞` for every `μ ≥ 0` and every time `s`. -/
lemma norm_dampedCoef_le_gen (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L)
    (s : ℝ) : ‖dampedCoef cf μ w s‖ ≤ (1 + μ) * coefBound cf := by
  unfold dampedCoef
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ]
  have h1 := norm_coef_le cf w.1 s
  have h2 := norm_integral_damped_le cf hμ w s
  nlinarith

/-- The derivative bounds of the damped field. -/
def dampedBd (cf : ControlFamily L M S) (μ : ℝ) (k : ℕ) : ℝ :=
  4 * ((1 + μ) * coefBound cf) * (2 * Real.pi) ^ k

/-- **`B_{μ,ω}` is a smooth field.** -/
theorem dampedB_smooth (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L) :
    SmoothField (dampedB cf μ w) (dampedBd cf μ) where
  smooth := by
    have e : Function.uncurry (dampedB cf μ w) = fun p : ℝ × Pt 2 =>
        ∑ i : Fin 4, dampedCoef cf μ w p.1 i • eBasis i (p.2 - w.2) := by
      funext p
      simp only [Function.uncurry, dampedB_eq, eField]
    rw [e]
    refine ContDiff.sum fun i _ => ContDiff.fun_smul ?_ ?_
    · exact (contDiff_apply ℝ ℝ i).comp ((dampedCoef_contDiff cf μ w).comp contDiff_fst)
    · exact (contDiff_eBasis i).comp (contDiff_snd.sub contDiff_const)
  bound k t x := by
    rw [dampedB_eq]
    refine (norm_iteratedFDeriv_eField_sub_le _ _ k x).trans ?_
    unfold dampedBd
    gcongr
    exact norm_dampedCoef_le_gen cf hμ w t

lemma SmoothField.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : ℝ → E → E} {B B' : ℕ → ℝ} (hV : SmoothField V B) (hB : ∀ k, B k ≤ B' k) :
    SmoothField V B' :=
  ⟨hV.smooth, fun k t x => (hV.bound k t x).trans (hB k)⟩

/-- Uniform bounds for `μ ∈ [0, 1]`. -/
theorem dampedB_smooth_unif (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) : SmoothField (dampedB cf μ w) (dampedBd cf 1) :=
  (dampedB_smooth cf hμ.1 w).mono fun k => by
    unfold dampedBd
    have := coefBound_nonneg cf
    gcongr
    exact hμ.2

end AnomDiss
