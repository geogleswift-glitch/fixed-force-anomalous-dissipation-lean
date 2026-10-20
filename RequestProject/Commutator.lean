module

public import RequestProject.H2Heat

/-!
# The heat–transport commutator in `L²`

`‖V·∇(H_v F) - H_v(V·∇F)‖²_{L²(𝕋²)} ≤ C K² v² ‖F‖²_{H²}` when `‖DV‖, ‖D²V‖ ≤ K`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- Stein's lemma for the Gaussian of variance `v`. -/
lemma stein_scaled {G : Pt 2 → ℂ} (hG : ContDiff ℝ 1 G) {C₀ C₁ : ℝ} (h₀ : ∀ x, ‖G x‖ ≤ C₀)
    (h₁ : ∀ x, ‖fderiv ℝ G x‖ ≤ C₁) (v : ℝ≥0) (x : Pt 2) (k : Fin 2) :
    ∫ ζ, ((ζ k : ℝ) : ℂ) * G (x + ζ) ∂(gauss2 v) = (v : ℂ) * ∫ ζ, pd k G (x + ζ) ∂(gauss2 v) := by
  set σ := Real.sqrt v with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ * σ = v := Real.mul_self_sqrt v.2
  have hpc : Continuous (pd k G) := continuous_pd_of_C1 G hG k
  rw [gauss2_eq_map v, integral_map (f := fun ζ : Pt 2 => ((ζ k : ℝ) : ℂ) * G (x + ζ)) (by fun_prop)
      ((Complex.continuous_ofReal.comp (continuous_apply k)).mul
        (hG.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable,
    integral_map (f := fun ζ : Pt 2 => pd k G (x + ζ)) (by fun_prop)
      (hpc.comp (continuous_const.add continuous_id)).aestronglyMeasurable]
  rw [← hσ]
  set G' : Pt 2 → ℂ := fun η => G (x + σ • η) with hG'
  have hA : ∀ η, HasFDerivAt (fun η : Pt 2 => x + σ • η) (σ • ContinuousLinearMap.id ℝ (Pt 2)) η :=
    fun η => ((hasFDerivAt_id η).const_smul σ).const_add x
  have hG'c : ContDiff ℝ 1 G' := hG.comp (by fun_prop)
  have hfd : ∀ η, fderiv ℝ G' η = (fderiv ℝ G (x + σ • η)).comp (σ • ContinuousLinearMap.id ℝ (Pt 2)) :=
    fun η => (((hG.differentiable one_ne_zero) _).hasFDerivAt.comp η (hA η)).fderiv
  have hfdb : ∀ η, ‖fderiv ℝ G' η‖ ≤ σ * C₁ := fun η => by
    rw [hfd]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ0]
    have hid : ‖ContinuousLinearMap.id ℝ (Pt 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h0 : 0 ≤ ‖fderiv ℝ G (x + σ • η)‖ := norm_nonneg _
    have hb := h₁ (x + σ • η)
    calc ‖fderiv ℝ G (x + σ • η)‖ * (σ * ‖ContinuousLinearMap.id ℝ (Pt 2)‖)
        ≤ C₁ * (σ * 1) := mul_le_mul hb (mul_le_mul_of_nonneg_left hid hσ0) (by positivity)
          (h0.trans hb)
      _ = σ * C₁ := by ring
  have hst := stein_2d hG'c (fun η => h₀ _) hfdb k
  have hpd : ∀ η, pd k G' η = (σ : ℂ) * pd k G (x + σ • η) := fun η => by
    show fderiv ℝ G' η (Pi.single k 1) = _
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, Complex.real_smul]
    rfl
  have e1 : (fun η : Pt 2 => (((σ • η) k : ℝ) : ℂ) * G (x + σ • η)) =
      fun η => (σ : ℂ) * (((η k : ℝ) : ℂ) * G' η) := by
    funext η; simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, hG']; ring
  simp only [e1, integral_const_mul, hst, hpd]
  rw [← mul_assoc, ← Complex.ofReal_mul, hσ2]

/-- Second-order Taylor bound. -/
lemma norm_taylor2_le {V : Pt 2 → Pt 2} (hV : ContDiff ℝ 2 V) {K : ℝ}
    (hK : ∀ x, ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ K) (x ζ : Pt 2) :
    ‖V (x + ζ) - V x - fderiv ℝ V x ζ‖ ≤ K * ‖ζ‖ ^ 2 := by
  have hd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set g : Pt 2 → Pt 2 := fun z => V z - fderiv ℝ V x z with hg
  have hgd : ∀ z, HasFDerivAt g (fderiv ℝ V z - fderiv ℝ V x) z := fun z =>
    (hd z).hasFDerivAt.sub (fderiv ℝ V x).hasFDerivAt
  have hb : ∀ z ∈ segment ℝ x (x + ζ), ‖fderiv ℝ V z - fderiv ℝ V x‖ ≤ K * ‖ζ‖ := by
    intro z hz
    have h1 := (convex_univ : Convex ℝ (univ : Set (Pt 2))).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hd2 w) (fun w _ => hK w) (mem_univ x) (mem_univ z)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_
      ((norm_nonneg (fderiv ℝ (fderiv ℝ V) x)).trans (hK x)))
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have : a • x + b • (x + ζ) - x = b • ζ := by
      rw [smul_add, ← add_assoc, ← add_smul, hab, one_smul]; abel
    rw [this, norm_smul, Real.norm_of_nonneg hb]
    nlinarith [norm_nonneg ζ]
  have := (convex_segment x (x + ζ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hgd z).hasFDerivWithinAt) hb (left_mem_segment ℝ x (x + ζ))
    (right_mem_segment ℝ x (x + ζ))
  simp only [hg, add_sub_cancel_left, map_add] at this
  have e : V (x + ζ) - (fderiv ℝ V x x + fderiv ℝ V x ζ) - (V x - fderiv ℝ V x x) =
      V (x + ζ) - V x - fderiv ℝ V x ζ := by abel
  rw [e] at this
  calc _ ≤ K * ‖ζ‖ * ‖ζ‖ := this
    _ = K * ‖ζ‖ ^ 2 := by ring

/-- Fourth moment of the Gaussian of variance `v`. -/
lemma integral_norm_pow4_gauss2 (v : ℝ≥0) :
    ∫ ζ, ‖ζ‖ ^ 4 ∂(gauss2 v) = (v : ℝ) ^ 2 * ∫ η, ‖η‖ ^ 4 ∂(gauss2 1) := by
  rw [gauss2_eq_map v, integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  congr 1; funext η
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  congr 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (NNReal.coe_nonneg v)]

lemma integrable_translate_of_bdd {E : Type*} [NormedAddCommGroup E] {u : Pt 2 → E}
    (hu : Continuous u) {C : ℝ} (hC : ∀ y, ‖u y‖ ≤ C) (v : ℝ≥0) (x : Pt 2) :
    Integrable (fun ζ => u (x + ζ)) (gauss2 v) :=
  Integrable.of_bound (hu.comp (continuous_const.add continuous_id)).aestronglyMeasurable C
    (Eventually.of_forall fun _ => hC _)

/-- The commutator as a Gaussian average. -/
lemma comm_identity {V : Pt 2 → Pt 2} (hV : Continuous V) {M : ℝ} (hM : ∀ y, ‖V y‖ ≤ M)
    {ξ : Pt 2} {F : Pt 2 → ℂ} (hF : ContDiff ℝ 2 F) (hqp : IsQP ξ F) (v : ℝ≥0) (x : Pt 2) :
    conv V (heatOp v F) x - heatOp v (conv V F) x =
      ∑ j, ∫ ζ, (V x j - V (x + ζ) j) • pd j F (x + ζ) ∂(gauss2 v) := by
  have h1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hGc : ∀ j, Continuous (pd j F) := fun j => continuous_pd_of_C1 _ h1 j
  have hGb : ∀ j, ∃ C, ∀ y, ‖pd j F y‖ ≤ C := fun j => (hqp.pd hd j).bdd (hGc j)
  choose C hC using hGb
  have hI1 : ∀ j, Integrable (fun ζ => pd j F (x + ζ)) (gauss2 v) := fun j =>
    integrable_translate_of_bdd (hGc j) (hC j) v x
  have hVj : ∀ j, Continuous fun y => V y j := fun j => (continuous_apply j).comp hV
  have hVjb : ∀ j y, ‖V y j‖ ≤ M := fun j y => (norm_le_pi_norm (V y) j).trans (hM y)
  have hI2 : ∀ j, Integrable (fun ζ => V (x + ζ) j • pd j F (x + ζ)) (gauss2 v) := fun j =>
    integrable_translate_of_bdd (u := fun y => V y j • pd j F y) ((hVj j).smul (hGc j))
      (C := M * C j) (fun y => by
        rw [norm_smul]
        exact mul_le_mul (hVjb j y) (hC j y) (norm_nonneg _) ((norm_nonneg _).trans (hVjb j y)))
      v x
  have e1 : conv V (heatOp v F) x = ∑ j, ∫ ζ, V x j • pd j F (x + ζ) ∂(gauss2 v) := by
    unfold conv
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pd_heatOp_C1 hqp h1, integral_smul]
    rfl
  have e2 : heatOp v (conv V F) x = ∑ j, ∫ ζ, V (x + ζ) j • pd j F (x + ζ) ∂(gauss2 v) := by
    unfold heatOp conv
    rw [integral_finset_sum _ fun j _ => hI2 j]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hA : Integrable (fun ζ => V x j • pd j F (x + ζ)) (gauss2 v) := (hI1 j).smul (V x j)
  rw [← integral_sub hA (hI2 j)]
  congr 1; funext ζ
  rw [sub_smul]

/-- Bound for one term of the commutator. -/
lemma comm_term_bound {V : Pt 2 → Pt 2} (hV : ContDiff ℝ 2 V) {K : ℝ}
    (hK1 : ∀ x, ‖fderiv ℝ V x‖ ≤ K) (hK2 : ∀ x, ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ K)
    {ξ : Pt 2} {G : Pt 2 → ℂ} (hG : ContDiff ℝ 1 G) (hqp : IsQP ξ G) (v : ℝ≥0) (x : Pt 2)
    (j : Fin 2) :
    ‖∫ ζ, (V x j - V (x + ζ) j) • G (x + ζ) ∂(gauss2 v)‖ ≤
      v * K * ∑ k, ‖heatOp v (pd k G) x‖ + K * ∫ ζ, ‖ζ‖ ^ 2 * ‖G (x + ζ)‖ ∂(gauss2 v) := by
  obtain ⟨C, hC⟩ := bdd_C1_of_isQP hqp hG
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK1 0)
  have hGc := hG.continuous
  have hGb : ∀ y, ‖G y‖ ≤ C := fun y => (hC y).1
  have hd : Differentiable ℝ V := hV.differentiable (by norm_num)
  set r : Pt 2 → Pt 2 := fun ζ => V (x + ζ) - V x - fderiv ℝ V x ζ with hr
  have hrc : Continuous r := by
    simp only [hr]
    exact ((hV.continuous.comp (continuous_const.add continuous_id)).sub continuous_const).sub
      (fderiv ℝ V x).continuous
  have hrb : ∀ ζ, ‖r ζ‖ ≤ K * ‖ζ‖ ^ 2 := fun ζ => norm_taylor2_le hV hK2 x ζ
  have hint1 := integrable_gauss2_norm_rpow v (p := 1) one_pos
  have hint2 := integrable_gauss2_norm_rpow v (p := 2) two_pos
  simp only [Real.rpow_one] at hint1
  have hint2' : Integrable (fun ζ : Pt 2 => ‖ζ‖ ^ 2) (gauss2 v) := by
    have e : (fun ζ : Pt 2 => ‖ζ‖ ^ (2 : ℝ)) = fun ζ => ‖ζ‖ ^ 2 :=
      funext fun ζ => Real.rpow_two _
    rwa [e] at hint2
  -- integrability
  have hIk : ∀ k : Fin 2, Integrable (fun ζ : Pt 2 => ((ζ k : ℝ) : ℂ) * G (x + ζ)) (gauss2 v) :=
    fun k => by
      refine (hint1.mul_const C).mono' ((Complex.continuous_ofReal.comp
        (continuous_apply k)).mul (hGc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun ζ => ?_)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (norm_le_pi_norm ζ k) (hGb _) (norm_nonneg _) (norm_nonneg _)
  have hIr : Integrable (fun ζ => r ζ j • G (x + ζ)) (gauss2 v) := by
    refine ((hint2'.const_mul K).mul_const C).mono' (((continuous_apply j).comp hrc).smul
      (hGc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun ζ => ?_)
    rw [norm_smul]
    exact mul_le_mul ((norm_le_pi_norm (r ζ) j).trans (hrb ζ)) (hGb _) (norm_nonneg _)
      (by positivity)
  -- decomposition
  have hsplit : ∀ ζ, (V x j - V (x + ζ) j) • G (x + ζ) =
      -(∑ k, (pd k V x j : ℂ) * (((ζ k : ℝ) : ℂ) * G (x + ζ))) - r ζ j • G (x + ζ) := by
    intro ζ
    have hD : fderiv ℝ V x ζ j = ∑ k, ζ k * pd k V x j := by
      rw [fderiv_apply_eq_sum_pd, Finset.sum_apply]
      simp [smul_eq_mul]
    have : V x j - V (x + ζ) j = -(fderiv ℝ V x ζ j) - r ζ j := by
      simp only [hr, Pi.sub_apply]; ring
    rw [this, hD, sub_smul, neg_smul, Finset.sum_smul]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.real_smul]; push_cast; ring
  simp_rw [hsplit]
  have hS : Integrable (fun ζ => -∑ k, (pd k V x j : ℂ) * (((ζ k : ℝ) : ℂ) * G (x + ζ)))
      (gauss2 v) := (integrable_finset_sum _ fun k _ => (hIk k).const_mul _).neg
  rw [integral_sub hS hIr, integral_neg, integral_finset_sum _ fun k _ => (hIk k).const_mul _]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hvn : ‖(v : ℂ)‖ = (v : ℝ) := by simp
    rw [integral_const_mul, stein_scaled hG (fun y => (hC y).1) (fun y => (hC y).2) v x k,
      norm_mul, norm_mul, Complex.norm_real, hvn]
    have hpk : ‖pd k V x j‖ ≤ K := by
      refine (norm_le_pi_norm (pd k V x) j).trans ?_
      unfold pd
      refine ((fderiv ℝ V x).le_opNorm _).trans ?_
      have h1 : ‖(Pi.single k 1 : Pt 2)‖ ≤ 1 :=
        (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
          by_cases h : i = k
          · subst h; simp
          · simp [h]
      nlinarith [hK1 x, norm_nonneg (fderiv ℝ V x)]
    have := norm_nonneg (∫ ζ, pd k G (x + ζ) ∂(gauss2 v))
    calc ‖pd k V x j‖ * ((v : ℝ) * ‖∫ ζ, pd k G (x + ζ) ∂(gauss2 v)‖)
        ≤ K * ((v : ℝ) * ‖∫ ζ, pd k G (x + ζ) ∂(gauss2 v)‖) := by gcongr
      _ = v * K * ‖heatOp v (pd k G) x‖ := by unfold heatOp; ring
  · refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((hint2'.mul_const C).const_mul K |>.mono' (by
        exact (continuous_const.mul ((continuous_norm.pow 2).mul
          (hGc.comp (continuous_const.add continuous_id)).norm)).aestronglyMeasurable)
        (Eventually.of_forall fun ζ => ?_)) (Eventually.of_forall fun ζ => ?_)
    · rw [Real.norm_of_nonneg (by positivity)]
      have := hGb (x + ζ)
      have h0 : 0 ≤ ‖ζ‖ ^ 2 := by positivity
      calc K * (‖ζ‖ ^ 2 * ‖G (x + ζ)‖) ≤ K * (‖ζ‖ ^ 2 * C) := by gcongr
        _ = K * (‖ζ‖ ^ 2 * C) := rfl
    · simp only
      rw [norm_smul]
      calc ‖r ζ j‖ * ‖G (x + ζ)‖ ≤ K * ‖ζ‖ ^ 2 * ‖G (x + ζ)‖ :=
            mul_le_mul_of_nonneg_right ((norm_le_pi_norm (r ζ) j).trans (hrb ζ)) (norm_nonneg _)
        _ = K * (‖ζ‖ ^ 2 * ‖G (x + ζ)‖) := by ring

lemma sq_integral_le_of_memLp {P : Measure (Pt 2)} [IsProbabilityMeasure P] {u : Pt 2 → ℝ}
    (hu : MemLp u 2 P) : (∫ ζ, u ζ ∂P) ^ 2 ≤ ∫ ζ, u ζ ^ 2 ∂P := by
  have h1 := variance_nonneg u P
  rw [variance_eq_sub hu] at h1
  simp only [Pi.pow_apply] at h1
  linarith

lemma continuous_integral_translate {P : Measure (Pt 2)} {w : Pt 2 → ℝ} (hw : Integrable w P)
    {φ : Pt 2 → ℝ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ y, |φ y| ≤ C) :
    Continuous fun x => ∫ ζ, w ζ * φ (x + ζ) ∂P :=
  continuous_of_dominated (bound := fun ζ => |w ζ| * C)
    (fun x => hw.aestronglyMeasurable.mul (hφ.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _))
    (hw.abs.mul_const C) (Eventually.of_forall fun ζ =>
      continuous_const.mul (hφ.comp (continuous_id.add continuous_const)))

lemma abs_le_of_isQP_sq {ξ : Pt 2} {f : Pt 2 → ℂ} (hqp : IsQP ξ f) (hc : Continuous f) :
    ∃ C, ∀ y, |‖f y‖ ^ 2| ≤ C := by
  obtain ⟨C, hC⟩ := hqp.bdd hc
  exact ⟨C ^ 2, fun y => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2⟩

theorem commutator_L2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Pt 2 → Pt 2) (M K : ℝ) (ξ : Pt 2)
    (F : Pt 2 → ℂ) (v : ℝ≥0), ContDiff ℝ 2 V → (∀ x, ‖V x‖ ≤ M) → (∀ x, ‖fderiv ℝ V x‖ ≤ K) →
    (∀ x, ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ K) → ContDiff ℝ 2 F → IsQP ξ F →
    ∫ x in cell 2, ‖conv V (heatOp v F) x - heatOp v (conv V F) x‖ ^ 2 ≤
      C * K ^ 2 * (v : ℝ) ^ 2 * ∫ x in cell 2, h2Dens F x := by
  set M4 := ∫ η, ‖η‖ ^ 4 ∂(gauss2 1) with hM4
  have hM40 : 0 ≤ M4 := integral_nonneg fun _ => by positivity
  refine ⟨8 + 4 * M4, by positivity, ?_⟩
  intro V M K ξ F v hV hM hK1 hK2 hF hqp
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK1 0)
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have h1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  set G : Fin 2 → Pt 2 → ℂ := fun j => pd j F with hG
  have hGC : ∀ j, ContDiff ℝ 1 (G j) := fun j => contDiff_pd_of_C2 F hF j
  have hGq : ∀ j, IsQP ξ (G j) := fun j => hqp.pd hd j
  have hSc : ∀ k j, Continuous (pd k (G j)) := fun k j => continuous_pd_of_C1 _ (hGC j) k
  have hSq : ∀ k j, IsQP ξ (pd k (G j)) := fun k j => isQP_pd2 hqp hF k j
  have hGb : ∀ j, ∃ C, ∀ y, ‖G j y‖ ≤ C := fun j => (hGq j).bdd (hGC j).continuous
  have hSb : ∀ k j, ∃ C, ∀ y, ‖pd k (G j) y‖ ≤ C := fun k j => (hSq k j).bdd (hSc k j)
  choose CG hCG using hGb
  choose CS hCS using hSb
  -- the two densities
  set Φ : Pt 2 → ℝ := fun y => ∑ k, ∑ j, ‖pd k (G j) y‖ ^ 2 with hΦ
  set Ψ : Pt 2 → ℝ := fun y => ∑ j, ‖G j y‖ ^ 2 with hΨ
  have hΦc : Continuous Φ := continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun j _ =>
    (hSc k j).norm.pow 2
  have hΨc : Continuous Ψ := continuous_finset_sum _ fun j _ => (hGC j).continuous.norm.pow 2
  have hΦp : IsPeriodic Φ := fun y m => by
    simp only [hΦ]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
      (hSq k j).periodic_norm_sq y m
  have hΨp : IsPeriodic Ψ := fun y m => by
    simp only [hΨ]
    exact Finset.sum_congr rfl fun j _ => (hGq j).periodic_norm_sq y m
  obtain ⟨CΦ, hCΦ⟩ : ∃ C, ∀ y, |Φ y| ≤ C := by
    refine ⟨∑ k : Fin 2, ∑ j : Fin 2, CS k j ^ 2, fun y => ?_⟩
    rw [abs_of_nonneg (by positivity)]
    exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hCS k j y) 2
  obtain ⟨CΨ, hCΨ⟩ : ∃ C, ∀ y, |Ψ y| ≤ C := by
    refine ⟨∑ j : Fin 2, CG j ^ 2, fun y => ?_⟩
    rw [abs_of_nonneg (by positivity)]
    exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hCG j y) 2
  have hΦΨ : ∀ y, Φ y + Ψ y ≤ h2Dens F y := fun y => by
    unfold h2Dens
    simp only [hΦ, hΨ, hG]
    have := sq_nonneg ‖F y‖
    linarith
  have hint4 : Integrable (fun ζ : Pt 2 => ‖ζ‖ ^ 4) (gauss2 v) := by
    have h := integrable_gauss2_norm_rpow v (p := 4) (by norm_num)
    have e : (fun ζ : Pt 2 => ‖ζ‖ ^ (4 : ℝ)) = fun ζ => ‖ζ‖ ^ 4 :=
      funext fun ζ => by rw [← Real.rpow_natCast]; norm_num
    rwa [e] at h
  -- pointwise bound
  have hpt : ∀ x, ‖conv V (heatOp v F) x - heatOp v (conv V F) x‖ ^ 2 ≤
      8 * (v : ℝ) ^ 2 * K ^ 2 * ∫ ζ, 1 * Φ (x + ζ) ∂(gauss2 v) +
        4 * K ^ 2 * ∫ ζ, ‖ζ‖ ^ 4 * Ψ (x + ζ) ∂(gauss2 v) := by
    intro x
    rw [comm_identity hV.continuous hM hF hqp v x]
    set a : Fin 2 → Fin 2 → ℝ := fun k j => ‖heatOp v (pd k (G j)) x‖ with ha
    set b : Fin 2 → ℝ := fun j => ∫ ζ, ‖ζ‖ ^ 2 * ‖G j (x + ζ)‖ ∂(gauss2 v) with hb
    have hb0 : ∀ j, 0 ≤ b j := fun j => integral_nonneg fun _ => by positivity
    have hT : ‖∑ j, ∫ ζ, (V x j - V (x + ζ) j) • pd j F (x + ζ) ∂(gauss2 v)‖ ≤
        v * K * ∑ j, ∑ k, a k j + K * ∑ j, b j := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => comm_term_bound hV hK1 hK2 (hGC j) (hGq j) v x j
    have ha2 : ∀ k j, a k j ^ 2 ≤ ∫ ζ, ‖pd k (G j) (x + ζ)‖ ^ 2 ∂(gauss2 v) := fun k j =>
      sq_norm_heatOp_le (hSc k j) (hCS k j) v x
    have hb2 : ∀ j, b j ^ 2 ≤ ∫ ζ, ‖ζ‖ ^ 4 * ‖G j (x + ζ)‖ ^ 2 ∂(gauss2 v) := fun j => by
      have hm : MemLp (fun ζ : Pt 2 => ‖ζ‖ ^ 2 * ‖G j (x + ζ)‖) 2 (gauss2 v) := by
        have hcont : Continuous (fun ζ : Pt 2 => ‖ζ‖ ^ 2 * ‖G j (x + ζ)‖) :=
          (continuous_norm.pow 2).mul
            ((hGC j).continuous.comp (continuous_const.add continuous_id)).norm
        refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
        refine (hint4.mul_const (CG j ^ 2)).mono' (hcont.pow 2).aestronglyMeasurable
          (Eventually.of_forall fun ζ => ?_)
        have hp := pow_le_pow_left₀ (norm_nonneg _) (hCG j (x + ζ)) 2
        show ‖(‖ζ‖ ^ 2 * ‖G j (x + ζ)‖) ^ 2‖ ≤ ‖ζ‖ ^ 4 * CG j ^ 2
        rw [Real.norm_of_nonneg (by positivity)]
        calc (‖ζ‖ ^ 2 * ‖G j (x + ζ)‖) ^ 2 = ‖ζ‖ ^ 4 * ‖G j (x + ζ)‖ ^ 2 := by ring
          _ ≤ ‖ζ‖ ^ 4 * CG j ^ 2 := mul_le_mul_of_nonneg_left hp (by positivity)
      refine (sq_integral_le_of_memLp hm).trans (le_of_eq ?_)
      congr 1; funext ζ; ring
    -- combine
    have hsumA : ∑ j, ∑ k, a k j ^ 2 ≤ ∫ ζ, 1 * Φ (x + ζ) ∂(gauss2 v) := by
      have hI : ∀ k j, Integrable (fun ζ => ‖pd k (G j) (x + ζ)‖ ^ 2) (gauss2 v) := fun k j =>
        integrable_sq_norm_translate (hSc k j) (hCS k j) v x
      simp only [one_mul, hΦ]
      rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ => hI k j,
        Finset.sum_comm]
      exact Finset.sum_le_sum fun k _ => by
        rw [integral_finset_sum _ fun j _ => hI k j]
        exact Finset.sum_le_sum fun j _ => ha2 k j
    have hsumB : ∑ j, b j ^ 2 ≤ ∫ ζ, ‖ζ‖ ^ 4 * Ψ (x + ζ) ∂(gauss2 v) := by
      have hI : ∀ j, Integrable (fun ζ : Pt 2 => ‖ζ‖ ^ 4 * ‖G j (x + ζ)‖ ^ 2) (gauss2 v) :=
        fun j => (hint4.mul_const (CG j ^ 2)).mono' ((continuous_norm.pow 4).mul
            (((hGC j).continuous.comp (continuous_const.add continuous_id)).norm.pow 2)).aestronglyMeasurable
          (Eventually.of_forall fun ζ => by
            rw [Real.norm_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hCG j _) 2)
              (by positivity))
      simp only [hΨ, Finset.mul_sum]
      rw [integral_finset_sum _ fun j _ => hI j]
      exact Finset.sum_le_sum fun j _ => hb2 j
    have hA0 : 0 ≤ ∑ j, ∑ k, a k j := by positivity
    have hB0 : 0 ≤ ∑ j, b j := Finset.sum_nonneg fun j _ => hb0 j
    have hcsA : (∑ j, ∑ k, a k j) ^ 2 ≤ 4 * ∑ j, ∑ k, a k j ^ 2 := by
      simp only [Fin.sum_univ_two]
      nlinarith [sq_nonneg (a 0 0 - a 1 0), sq_nonneg (a 0 0 - a 0 1), sq_nonneg (a 0 0 - a 1 1),
        sq_nonneg (a 1 0 - a 0 1), sq_nonneg (a 1 0 - a 1 1), sq_nonneg (a 0 1 - a 1 1)]
    have hcsB : (∑ j, b j) ^ 2 ≤ 2 * ∑ j, b j ^ 2 := by
      simp only [Fin.sum_univ_two]
      nlinarith [sq_nonneg (b 0 - b 1)]
    have hT2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
    refine hT2.trans ?_
    have hv0 : (0 : ℝ) ≤ v := v.2
    have e1 : (v * K * ∑ j, ∑ k, a k j + K * ∑ j, b j) ^ 2 ≤
        2 * ((v : ℝ) * K) ^ 2 * (∑ j, ∑ k, a k j) ^ 2 + 2 * K ^ 2 * (∑ j, b j) ^ 2 := by
      nlinarith [sq_nonneg ((v : ℝ) * K * ∑ j, ∑ k, a k j - K * ∑ j, b j)]
    refine e1.trans ?_
    have hvK : 0 ≤ ((v : ℝ) * K) ^ 2 := sq_nonneg _
    have hK2' : 0 ≤ K ^ 2 := sq_nonneg _
    have f1 := mul_le_mul_of_nonneg_left (hcsA.trans (mul_le_mul_of_nonneg_left hsumA
      (by norm_num : (0 : ℝ) ≤ 4))) hvK
    have f2 := mul_le_mul_of_nonneg_left (hcsB.trans (mul_le_mul_of_nonneg_left hsumB
      (by norm_num : (0 : ℝ) ≤ 2))) hK2'
    nlinarith
  -- integrate
  have hRc : Continuous fun x => ‖conv V (heatOp v F) x - heatOp v (conv V F) x‖ ^ 2 := by
    have h1' : Continuous (conv V (heatOp v F)) :=
      continuous_conv hV.continuous ((contDiff_heatOp hqp hF v).of_le (by norm_num))
    have h2' : Continuous (heatOp v (conv V F)) :=
      continuous_gavg (continuous_conv hV.continuous h1) (fun y =>
        norm_conv_le hM (fun j y => (hCG j y).trans (by fin_cases j <;> simp)) y |>.trans
          (le_refl (2 * (M * max (CG 0) (CG 1))))) v
    exact (h1'.sub h2').norm.pow 2
  have hcA := continuous_integral_translate (integrable_const (1 : ℝ)) hΦc hCΦ (P := gauss2 v)
  have hcB := continuous_integral_translate hint4 hΨc hCΨ (P := gauss2 v)
  have hIA : IntegrableOn (fun x => 8 * (v : ℝ) ^ 2 * K ^ 2 * ∫ ζ, 1 * Φ (x + ζ) ∂(gauss2 v))
      (cell 2) := integrableOn_cell_of_continuous (continuous_const.mul hcA)
  have hIB : IntegrableOn (fun x => 4 * K ^ 2 * ∫ ζ, ‖ζ‖ ^ 4 * Ψ (x + ζ) ∂(gauss2 v))
      (cell 2) := integrableOn_cell_of_continuous (continuous_const.mul hcB)
  have hΦi := integrableOn_cell_of_continuous hΦc
  have hΨi := integrableOn_cell_of_continuous hΨc
  have hstep1 : ∫ x in cell 2, ‖conv V (heatOp v F) x - heatOp v (conv V F) x‖ ^ 2 ≤
      ∫ x in cell 2, (8 * (v : ℝ) ^ 2 * K ^ 2 * ∫ ζ, 1 * Φ (x + ζ) ∂(gauss2 v) +
        4 * K ^ 2 * ∫ ζ, ‖ζ‖ ^ 4 * Ψ (x + ζ) ∂(gauss2 v)) :=
    setIntegral_mono (integrableOn_cell_of_continuous hRc) (hIA.add hIB) hpt
  rw [integral_add hIA hIB, integral_const_mul, integral_const_mul,
    integral_cell_integral_translate (integrable_const _) hΦc hΦp,
    integral_cell_integral_translate hint4 hΨc hΨp, integral_norm_pow4_gauss2 v, ← hM4] at hstep1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hstep1
  have hΦ0 : 0 ≤ ∫ x in cell 2, Φ x := setIntegral_nonneg measurableSet_Icc fun y _ => by
    simp only [hΦ]; positivity
  have hΨ0 : 0 ≤ ∫ x in cell 2, Ψ x := setIntegral_nonneg measurableSet_Icc fun y _ => by
    simp only [hΨ]; positivity
  have hadd : ∫ x in cell 2, (Φ x + Ψ x) = (∫ x in cell 2, Φ x) + ∫ x in cell 2, Ψ x :=
    integral_add hΦi hΨi
  have hmono : ∫ x in cell 2, (Φ x + Ψ x) ≤ ∫ x in cell 2, h2Dens F x :=
    setIntegral_mono (hΦi.add hΨi) (integrableOn_cell_of_continuous (continuous_h2Dens hF)) hΦΨ
  have hsum : (∫ x in cell 2, Φ x) + ∫ x in cell 2, Ψ x ≤ ∫ x in cell 2, h2Dens F x := by
    linarith
  have hv0 : (0 : ℝ) ≤ v := v.2
  have hc1 : 0 ≤ (v : ℝ) ^ 2 * K ^ 2 := by positivity
  have hc2 : 0 ≤ (v : ℝ) ^ 2 * K ^ 2 * M4 := by positivity
  refine hstep1.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left (show ∫ x in cell 2, Φ x ≤ ∫ x in cell 2, h2Dens F x
    by linarith) hc1, mul_le_mul_of_nonneg_left (show ∫ x in cell 2, Ψ x ≤
    ∫ x in cell 2, h2Dens F x by linarith) hc2]

end AnomDiss
