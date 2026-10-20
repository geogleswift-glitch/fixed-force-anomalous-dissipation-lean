module

public import RequestProject.DriftRegularity

/-!
# Calculus for rescaled eigenfields

Derivatives of fields of the form `x ↦ a • F(k x - z)`, used for the isolated pulses of
Lemma 5.2.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasFDerivAt_affine2 (k : ℝ) (z x : Pt 2) :
    HasFDerivAt (fun y : Pt 2 => k • y - z) (k • ContinuousLinearMap.id ℝ (Pt 2)) x := by
  simpa using ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul k).sub_const z

lemma fderiv_affine_comp (F : Pt 2 → E) (hF : Differentiable ℝ F) (a k : ℝ) (z x : Pt 2) :
    fderiv ℝ (fun y => a • F (k • y - z)) x = (a * k) • fderiv ℝ F (k • x - z) := by
  have h : HasFDerivAt (fun y => a • F (k • y - z))
      (a • (fderiv ℝ F (k • x - z)).comp (k • ContinuousLinearMap.id ℝ (Pt 2))) x :=
    ((hF _).hasFDerivAt.comp x (hasFDerivAt_affine2 k z x)).const_smul a
  rw [h.fderiv]
  ext v
  simp [smul_smul]

lemma pd_affine_fun (F : Pt 2 → E) (hF : Differentiable ℝ F) (a k : ℝ) (z : Pt 2) (i : Fin 2) :
    pd i (fun y => a • F (k • y - z)) = fun x => (a * k) • pd i F (k • x - z) := by
  funext x
  unfold pd
  rw [fderiv_affine_comp F hF]
  rfl

lemma lap_affine (F : Pt 2 → E) (hF : ContDiff ℝ 2 F) (a k : ℝ) (z x : Pt 2) :
    lap (fun y => a • F (k • y - z)) x = (a * k ^ 2) • lap F (k • x - z) := by
  unfold lap
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_affine_fun F (hF.differentiable (by norm_num)),
    pd_affine_fun (pd i F) ((contDiff_pd_of_C2 F hF i).differentiable one_ne_zero)]
  simp only
  congr 1; ring

lemma conv_affine (F : Pt 2 → Pt 2) (hF : Differentiable ℝ F) (a k : ℝ) (z x : Pt 2) :
    conv (fun y => a • F (k • y - z)) (fun y => a • F (k • y - z)) x =
      (a ^ 2 * k) • conv F F (k • x - z) := by
  unfold conv
  simp only [pd_affine_fun F hF]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
  ring_nf

lemma grad_affine (φ : Pt 2 → ℝ) (hφ : Differentiable ℝ φ) (a k : ℝ) (z x : Pt 2) :
    grad (fun y => a * φ (k • y - z)) x = (a * k) • grad φ (k • x - z) := by
  have := pd_affine_fun φ hφ a k z
  funext i
  simp only [smul_eq_mul] at this
  simp only [grad, Pi.smul_apply, smul_eq_mul]
  rw [this]


/-! ### The pulse intervals -/

lemma Ij_unique {j j' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') {t : ℝ} (h : t ∈ Ij j) (h' : t ∈ Ij j') :
    j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := sj_lt_succ j hj
    have h2 := sj_mono (show j + 1 ≤ j' by omega)
    linarith [h.2, h'.1]
  · have h1 := sj_lt_succ j' hj'
    have h2 := sj_mono (show j' + 1 ≤ j by omega)
    linarith [h'.2, h.1]

lemma gForce_on_Ij (w : Phase) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ Ij j) :
    gForce w t = fun x =>
      (1 / (kk j * δs j ^ 2)) • bDot cf₀ (w j) ((t - sj j) / δs j) (kk j • x) := by
  funext x
  unfold gForce
  rw [tsum_eq_single j fun j' hj' => by
    rw [if_neg fun h => hj' (Ij_unique h.1 hj h.2 ht)]]
  rw [if_pos ⟨hj, ht⟩]

lemma lintegral_Icc_affine (s : ℝ) {δ : ℝ} (hδ : 0 < δ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Icc s (s + δ), g t = ∫⁻ u in Icc 0 1, ENNReal.ofReal δ * g (s + δ * u) := by
  have himg : (fun u => s + δ * u) '' Icc 0 1 = Icc s (s + δ) := by
    have : (fun u => s + δ * u) = (fun v => s + v) ∘ (fun u => δ * u) := rfl
    rw [this, Set.image_comp, Set.image_mul_left_Icc hδ.le zero_le_one, Set.image_const_add_Icc]
    simp
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
    (f' := fun _ => δ) (fun u _ => by simpa using ((hasDerivAt_id u).const_mul δ).const_add s |>.hasDerivWithinAt)
    (fun u _ v _ h => by simpa [hδ.ne'] using h)]
  simp [abs_of_pos hδ]

end AnomDiss
