module

public import RequestProject.PolarRep
public import RequestProject.Comparison
public import RequestProject.Residue
public import RequestProject.Rescale

/-!
# The two-dimensional interpolation inequality (Lemma 6.1)

`‖v‖_∞ ≤ C‖v‖₂^{1/3}‖curl v‖₄^{2/3} + C‖v‖₂` for smooth periodic divergence-free fields on `𝕋²`,
proved by localizing with a cutoff and applying the Cauchy–Pompeiu formula.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

noncomputable section

namespace AnomDiss

/-! ### A fixed bump function -/

/-- A smooth profile equal to `1` on `(-∞, 1/3]` and to `0` on `[3/4, ∞)`. -/
def bumpProfile (t : ℝ) : ℝ := Real.smoothTransition ((3 / 4 - t) * (12 / 5))

/-- The sum of squares of the coordinates. -/
def sumsq (w : Pt 2) : ℝ := ∑ k, w k ^ 2

/-- A fixed smooth bump on `ℝ²`: `1` for `|w|² ≤ 1/3`, `0` for `|w|² ≥ 3/4`. -/
def bump1 (w : Pt 2) : ℝ := bumpProfile (sumsq w)

lemma contDiff_sumsq : ContDiff ℝ ∞ sumsq := by
  unfold sumsq
  exact ContDiff.sum fun k _ => ((contDiff_apply ℝ ℝ k).pow 2)

lemma continuous_sumsq : Continuous sumsq := contDiff_sumsq.continuous

lemma contDiff_bump1 : ContDiff ℝ ∞ bump1 := by
  unfold bump1 bumpProfile
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_sumsq).mul contDiff_const)

lemma bump1_eq_one {w : Pt 2} (h : sumsq w ≤ 1 / 3) : bump1 w = 1 := by
  unfold bump1 bumpProfile
  exact Real.smoothTransition.one_of_one_le (by nlinarith)

lemma bump1_eq_zero {w : Pt 2} (h : 3 / 4 ≤ sumsq w) : bump1 w = 0 := by
  unfold bump1 bumpProfile
  exact Real.smoothTransition.zero_of_nonpos (by nlinarith)

lemma bump1_nonneg (w : Pt 2) : 0 ≤ bump1 w := Real.smoothTransition.nonneg _

lemma bump1_le_one (w : Pt 2) : bump1 w ≤ 1 := Real.smoothTransition.le_one _

lemma pd_bump1_inner {w : Pt 2} (h : sumsq w < 1 / 3) (i : Fin 2) : pd i bump1 w = 0 := by
  have hev : bump1 =ᶠ[𝓝 w] fun _ => (1 : ℝ) := by
    have : {y : Pt 2 | sumsq y < 1 / 3} ∈ 𝓝 w :=
      (isOpen_lt continuous_sumsq continuous_const).mem_nhds h
    filter_upwards [this] with y hy using bump1_eq_one hy.le
  unfold pd
  rw [hev.fderiv_eq]
  simp

lemma pd_bump1_outer {w : Pt 2} (h : 3 / 4 < sumsq w) (i : Fin 2) : pd i bump1 w = 0 := by
  have hev : bump1 =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
    have : {y : Pt 2 | 3 / 4 < sumsq y} ∈ 𝓝 w :=
      (isOpen_lt continuous_const continuous_sumsq).mem_nhds h
    filter_upwards [this] with y hy using bump1_eq_zero hy.le
  unfold pd
  rw [hev.fderiv_eq]
  simp

lemma pd_bump1_bound : ∃ K, 0 ≤ K ∧ ∀ i w, |pd i bump1 w| ≤ K := by
  have hcs : HasCompactSupport bump1 := by
    refine HasCompactSupport.intro (K := {w | sumsq w ≤ 3 / 4}) ?_ fun w hw => ?_
    · refine Metric.isCompact_of_isClosed_isBounded
        (isClosed_le continuous_sumsq continuous_const) ?_
      refine (Metric.isBounded_closedBall (x := (0 : Pt 2)) (r := 1)).subset fun w hw => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro k
      have hk : w k ^ 2 ≤ sumsq w := by
        unfold sumsq
        exact Finset.single_le_sum (f := fun k => w k ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ k)
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_one.mpr (by simp only [mem_setOf_eq] at hw; linarith)
    · exact bump1_eq_zero (le_of_lt (not_le.1 hw))
  have hfc : Continuous (fderiv ℝ bump1) := contDiff_bump1.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (hcs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hfc
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun i w => ?_⟩
  unfold pd
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  have : ‖(Pi.single i 1 : Pt 2)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  calc ‖fderiv ℝ bump1 w‖ * ‖(Pi.single i 1 : Pt 2)‖ ≤ C * 1 :=
        mul_le_mul (hC w) this (norm_nonneg _) ((norm_nonneg _).trans (hC w))
    _ = C := mul_one C

/-! ### The rescaled cutoff -/

lemma sumsq_eq (w : Pt 2) : sumsq w = euclNorm w ^ 2 := by
  unfold euclNorm sumsq
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]

lemma sumsq_smul (c : ℝ) (w : Pt 2) : sumsq (c • w) = c ^ 2 * sumsq w := by
  unfold sumsq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- The cutoff `η(y) = bump1((y - z)/ρ)`. -/
def cutoff (z : Pt 2) (ρ : ℝ) (y : Pt 2) : ℝ := bump1 (ρ⁻¹ • (y - z))

lemma contDiff_cutoff (z : Pt 2) (ρ : ℝ) : ContDiff ℝ ∞ (cutoff z ρ) := by
  unfold cutoff
  exact contDiff_bump1.comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)

lemma sumsq_cutoff_arg {ρ : ℝ} (hρ : 0 < ρ) (z y : Pt 2) :
    sumsq (ρ⁻¹ • (y - z)) = euclNorm (y - z) ^ 2 / ρ ^ 2 := by
  rw [sumsq_smul, sumsq_eq]; field_simp

lemma cutoff_self (z : Pt 2) (ρ : ℝ) : cutoff z ρ z = 1 := by
  unfold cutoff
  exact bump1_eq_one (by simp [sumsq])

lemma cutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {z y : Pt 2} (h : ρ ≤ euclNorm (y - z)) :
    cutoff z ρ y = 0 := by
  unfold cutoff
  refine bump1_eq_zero ?_
  rw [sumsq_cutoff_arg hρ, le_div_iff₀ (by positivity)]
  nlinarith

lemma cutoff_nonneg (z : Pt 2) (ρ : ℝ) (y : Pt 2) : 0 ≤ cutoff z ρ y := bump1_nonneg _

lemma cutoff_le_one (z : Pt 2) (ρ : ℝ) (y : Pt 2) : cutoff z ρ y ≤ 1 := bump1_le_one _

lemma pd_cutoff (z : Pt 2) (ρ : ℝ) (i : Fin 2) (y : Pt 2) :
    pd i (cutoff z ρ) y = ρ⁻¹ * pd i bump1 (ρ⁻¹ • (y - z)) := by
  have e : cutoff z ρ = fun y => (fun w => bump1 (ρ⁻¹ • w)) (y + -z) := by
    funext y; simp [cutoff, sub_eq_add_neg]
  rw [e, pd_translate (fun w => bump1 (ρ⁻¹ • w)) i (-z)]
  simp only
  rw [pd_smul_comp bump1 ρ⁻¹ i (y + -z) ((contDiff_bump1.differentiable (by simp)) _),
    smul_eq_mul, sub_eq_add_neg]

lemma pd_cutoff_inner {ρ : ℝ} (hρ : 0 < ρ) {z y : Pt 2} (h : euclNorm (y - z) ≤ ρ / 2)
    (i : Fin 2) : pd i (cutoff z ρ) y = 0 := by
  rw [pd_cutoff, pd_bump1_inner, mul_zero]
  rw [sumsq_cutoff_arg hρ, div_lt_iff₀ (by positivity)]
  have h0 := euclNorm_nonneg' (y - z)
  nlinarith

lemma pd_cutoff_outer {ρ : ℝ} (hρ : 0 < ρ) {z y : Pt 2} (h : ρ ≤ euclNorm (y - z))
    (i : Fin 2) : pd i (cutoff z ρ) y = 0 := by
  rw [pd_cutoff, pd_bump1_outer, mul_zero]
  rw [sumsq_cutoff_arg hρ, lt_div_iff₀ (by positivity)]
  nlinarith

lemma pd_cutoff_bound : ∃ K, 0 ≤ K ∧ ∀ (z : Pt 2) (ρ : ℝ), 0 < ρ → ∀ i y,
    |pd i (cutoff z ρ) y| ≤ K / ρ := by
  obtain ⟨K, hK0, hK⟩ := pd_bump1_bound
  refine ⟨K, hK0, fun z ρ hρ i y => ?_⟩
  rw [pd_cutoff, abs_mul, abs_of_pos (inv_pos.2 hρ), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hK i _) (inv_nonneg.2 hρ.le)

lemma hasCompactSupport_cutoff {ρ : ℝ} (hρ : 0 < ρ) (z : Pt 2) :
    HasCompactSupport (cutoff z ρ) := by
  refine HasCompactSupport.intro (K := Metric.closedBall z ρ) (isCompact_closedBall z ρ)
    fun y hy => cutoff_eq_zero hρ ?_
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
  obtain ⟨k, hk⟩ : ∃ k, ρ < |(y - z) k| := by
    by_contra hcon
    push_neg at hcon
    exact absurd ((pi_norm_le_iff_of_nonneg hρ.le).2 fun k => by
      rw [Real.norm_eq_abs]; exact hcon k) (not_le.2 hy)
  exact (le_of_lt hk).trans (abs_le_euclNorm _ k)

/-! ### The localized Cauchy–Pompeiu estimate -/

lemma pd_smul_fun (c : Pt 2 → ℝ) (g : Pt 2 → Pt 2) (i : Fin 2) (y : Pt 2)
    (hc : DifferentiableAt ℝ c y) (hg : DifferentiableAt ℝ g y) :
    pd i (fun y => c y • g y) y = pd i c y • g y + c y • pd i g y := by
  unfold pd
  change fderiv ℝ (c • g) y _ = _
  rw [(hc.hasFDerivAt.smul hg.hasFDerivAt).fderiv]
  simp [add_comm]

/-- The real-linear map `w ↦ w₀ - i w₁`. -/
def cplxL : Pt 2 →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (1 : ℂ) +
    (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)).smulRight Complex.I

lemma cplxL_apply (w : Pt 2) : cplxL w = (w 0 : ℂ) + ((-w 1 : ℝ) : ℂ) * Complex.I := by
  simp [cplxL, Complex.real_smul]

lemma norm_cplxL (w : Pt 2) : ‖cplxL w‖ = euclNorm w := by
  rw [cplxL_apply, Complex.norm_add_mul_I]
  unfold euclNorm
  simp [Fin.sum_univ_two]

lemma norm_re_add_I_le (a b : ℝ) : ‖(a : ℂ) + Complex.I * b‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- **Localized Cauchy–Pompeiu estimate** for a divergence-free field. -/
lemma local_cauchy (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v) (hdiv : ∀ x, divergence v x = 0)
    (z : Pt 2) {ρ : ℝ} (hρ : 0 < ρ) :
    2 * π * euclNorm (v z) ≤
      (∫ p in polarCoord.target, cutoff z ρ (z + polPt p.1 p.2) *
        |pd 0 v (z + polPt p.1 p.2) 1 - pd 1 v (z + polPt p.1 p.2) 0|) +
      ∫ p in polarCoord.target,
        (|pd 0 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 0 +
            pd 1 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 1| +
          |pd 1 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 0 -
            pd 0 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 1|) := by
  set η := cutoff z ρ with hη
  have hηc : ContDiff ℝ 1 η := (contDiff_cutoff z ρ).of_le (by simp)
  set u : Pt 2 → Pt 2 := fun y => η y • v y with hu
  have huc : ContDiff ℝ 1 u := hηc.smul hv
  set f : Pt 2 → ℂ := fun y => cplxL (u y) with hf
  have hfc : ContDiff ℝ 1 f := cplxL.contDiff.comp huc
  have hfs : HasCompactSupport f :=
    ((hasCompactSupport_cutoff hρ z).smul_right (f' := v)).comp_left (g := cplxL) (map_zero _)
  have hmain := norm_le_polar f hfc hfs z
  have hfz : ‖f z‖ = euclNorm (v z) := by
    simp only [hf, hu, hη, cutoff_self, one_smul, norm_cplxL]
  rw [hfz] at hmain
  have hdu : Differentiable ℝ u := huc.differentiable one_ne_zero
  have hdη : Differentiable ℝ η := hηc.differentiable one_ne_zero
  have hdv : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hpdf : ∀ i, pd i f = fun y => cplxL (pd i u y) := fun i => pd_clm_fun cplxL u i hdu
  -- the pointwise bound
  have hpt : ∀ y, ‖pd 0 f y + Complex.I * pd 1 f y‖ ≤
      η y * |pd 0 v y 1 - pd 1 v y 0| +
        (|pd 0 η y * v y 0 + pd 1 η y * v y 1| + |pd 1 η y * v y 0 - pd 0 η y * v y 1|) := by
    intro y
    have hd := hdiv y
    simp only [divergence, Fin.sum_univ_two] at hd
    simp only [hpdf, hu, pd_smul_fun η v _ y (hdη y) (hdv y), cplxL_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have e : (((pd 0 η y * v y 0 + η y * pd 0 v y 0 : ℝ) : ℂ) +
        ((-(pd 0 η y * v y 1 + η y * pd 0 v y 1) : ℝ) : ℂ) * Complex.I) +
        Complex.I * (((pd 1 η y * v y 0 + η y * pd 1 v y 0 : ℝ) : ℂ) +
        ((-(pd 1 η y * v y 1 + η y * pd 1 v y 1) : ℝ) : ℂ) * Complex.I) =
        ((pd 0 η y * v y 0 + pd 1 η y * v y 1 + η y * (pd 0 v y 0 + pd 1 v y 1) : ℝ) : ℂ) +
        Complex.I * ((pd 1 η y * v y 0 - pd 0 η y * v y 1 -
          η y * (pd 0 v y 1 - pd 1 v y 0) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [e, hd, mul_zero, add_zero]
    refine (norm_re_add_I_le _ _).trans ?_
    have h1 := abs_sub (pd 1 η y * v y 0 - pd 0 η y * v y 1) (η y * (pd 0 v y 1 - pd 1 v y 0))
    rw [abs_mul, abs_of_nonneg (cutoff_nonneg z ρ y)] at h1
    linarith
  -- continuity and support of the majorants
  have hw : Continuous fun p : ℝ × ℝ => z + polPt p.1 p.2 :=
    continuous_const.add continuous_polPt
  have hpη : ∀ i, Continuous (pd i η) := fun i => continuous_pd_of_C1 η hηc i
  have hpv : ∀ i, Continuous (pd i v) := fun i => continuous_pd_of_C1 v hv i
  have hvc : Continuous v := hv.continuous
  have hηcc : Continuous η := hηc.continuous
  have hΦ1c : Continuous fun p : ℝ × ℝ => η (z + polPt p.1 p.2) *
      |pd 0 v (z + polPt p.1 p.2) 1 - pd 1 v (z + polPt p.1 p.2) 0| := by
    refine (hηcc.comp hw).mul (continuous_abs.comp ?_)
    exact (((continuous_apply 1).comp (hpv 0)).comp hw).sub
      (((continuous_apply 0).comp (hpv 1)).comp hw)
  have hΦ2c : Continuous fun p : ℝ × ℝ =>
      |pd 0 η (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 0 +
          pd 1 η (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 1| +
        |pd 1 η (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 0 -
          pd 0 η (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 1| := by
    have c0 := (hpη 0).comp hw
    have c1 := (hpη 1).comp hw
    have v0 := ((continuous_apply 0).comp hvc).comp hw
    have v1 := ((continuous_apply 1).comp hvc).comp hw
    exact (continuous_abs.comp ((c0.mul v0).add (c1.mul v1))).add
      (continuous_abs.comp ((c1.mul v0).sub (c0.mul v1)))
  have hnorm : ∀ r θ, 0 ≤ r → euclNorm (z + polPt r θ - z) = r := fun r θ hr => by
    rw [add_sub_cancel_left, euclNorm_polPt hr]
  have hΦ1z : ∀ r θ, ρ ≤ r → η (z + polPt r θ) *
      |pd 0 v (z + polPt r θ) 1 - pd 1 v (z + polPt r θ) 0| = 0 := fun r θ h => by
    rw [hη, cutoff_eq_zero hρ (by rw [hnorm r θ (hρ.le.trans h)]; exact h), zero_mul]
  have hΦ2z : ∀ r θ, ρ ≤ r →
      |pd 0 η (z + polPt r θ) * v (z + polPt r θ) 0 + pd 1 η (z + polPt r θ) * v (z + polPt r θ) 1| +
        |pd 1 η (z + polPt r θ) * v (z + polPt r θ) 0 -
          pd 0 η (z + polPt r θ) * v (z + polPt r θ) 1| = 0 := fun r θ h => by
    have hn : ρ ≤ euclNorm (z + polPt r θ - z) := by rw [hnorm r θ (hρ.le.trans h)]; exact h
    rw [hη, pd_cutoff_outer hρ hn 0, pd_cutoff_outer hρ hn 1]
    simp
  have hI1 := integrableOn_target_of_radius _ hΦ1c ρ hΦ1z
  have hI2 := integrableOn_target_of_radius _ hΦ2c ρ hΦ2z
  refine hmain.trans ?_
  rw [← integral_add hI1 hI2]
  refine integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _) (hI1.add hI2)
    (Eventually.of_forall fun p => ?_)
  exact hpt _

/-! ### Local integrals of periodic functions -/

lemma integral_cell_add_right_real (G : Pt 2 → ℝ) (hc : Continuous G) (hp : IsPeriodic G)
    (c : Pt 2) : ∫ x in cell 2, G (x + c) = ∫ x in cell 2, G x := by
  have h := integral_cell_add_right (fun x => (G x : ℂ)) (Complex.continuous_ofReal.comp hc)
    (fun x n => by simp only [hp x n]) c
  simp only [integral_complex_ofReal] at h
  exact_mod_cast h

/-- A nonnegative function dominated by a periodic `G` and supported in a Euclidean ball of
radius `ρ ≤ 1/2` has integral at most `∫_{𝕋²} G`. -/
lemma integral_local_le_cell (G : Pt 2 → ℝ) (hGc : Continuous G) (hGp : IsPeriodic G)
    (z : Pt 2) {ρ : ℝ} (hρ : ρ ≤ 1 / 2) (H : Pt 2 → ℝ) (hH0 : ∀ y, 0 ≤ H y)
    (hHle : ∀ y, H y ≤ G y) (hHz : ∀ y, ρ ≤ euclNorm (y - z) → H y = 0) :
    ∫ y, H y ≤ ∫ y in cell 2, G y := by
  set a : Pt 2 := z - fun _ => 1 / 2 with ha
  set Q : Set (Pt 2) := Icc a (a + 1) with hQ
  have hQi : Integrable (Q.indicator G) :=
    (hGc.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hle : ∀ y, H y ≤ Q.indicator G y := by
    intro y
    by_cases hy : y ∈ Q
    · rw [Set.indicator_of_mem hy]; exact hHle y
    · rw [Set.indicator_of_notMem hy, hHz y]
      simp only [hQ, mem_Icc, not_and_or, Pi.le_def, not_forall, not_le] at hy
      rcases hy with ⟨k, hk⟩ | ⟨k, hk⟩
      · refine le_trans ?_ (abs_le_euclNorm (y - z) k)
        simp only [ha, Pi.sub_apply] at hk
        rw [Pi.sub_apply, abs_of_neg (by linarith)]; linarith
      · refine le_trans ?_ (abs_le_euclNorm (y - z) k)
        simp only [ha, Pi.add_apply, Pi.sub_apply, Pi.one_apply] at hk
        rw [Pi.sub_apply, abs_of_pos (by linarith)]; linarith
  refine (integral_mono_of_nonneg (Eventually.of_forall hH0) hQi
    (Eventually.of_forall hle)).trans_eq ?_
  rw [← integral_add_right_eq_self (μ := volume) (Q.indicator G) a]
  have e : (fun y => Q.indicator G (y + a)) = (cell 2).indicator (fun y => G (y + a)) := by
    funext y
    by_cases hy : y ∈ cell 2
    · have : y + a ∈ Q := by
        simp only [cell, mem_Icc] at hy
        exact ⟨by simpa using add_le_add_right hy.1 a, by
          simpa [add_comm] using add_le_add_right hy.2 a⟩
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hy]
    · have : y + a ∉ Q := by
        intro h
        apply hy
        simp only [hQ, mem_Icc] at h
        exact ⟨by simpa using sub_le_sub_right h.1 a, by
          have := sub_le_sub_right h.2 a; simpa [add_comm] using this⟩
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hy]
  rw [e, integral_indicator (show MeasurableSet (cell 2) from measurableSet_Icc),
    integral_cell_add_right_real G hGc hGp a]

/-! ### The two terms of the local estimate -/

/-- The vorticity term: `∫∫ η|om| ≤ ‖om‖₄ (3π)^{3/4} ρ^{1/2}`. -/
lemma vorticity_term (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 1 v) (hp : IsPeriodic v) (z : Pt 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) :
    ∫ p in polarCoord.target, cutoff z ρ (z + polPt p.1 p.2) *
        |pd 0 v (z + polPt p.1 p.2) 1 - pd 1 v (z + polPt p.1 p.2) 0| ≤
      (∫ y in cell 2, (pd 0 v y 1 - pd 1 v y 0) ^ 4) ^ ((1 : ℝ) / 4) *
        ((3 * π) ^ ((3 : ℝ) / 4) * ρ ^ ((1 : ℝ) / 2)) := by
  set om : Pt 2 → ℝ := fun y => pd 0 v y 1 - pd 1 v y 0 with hvo
  set η := cutoff z ρ with hη
  have hvoc : Continuous om :=
    ((continuous_apply 1).comp (continuous_pd_of_C1 v hv 0)).sub
      ((continuous_apply 0).comp (continuous_pd_of_C1 v hv 1))
  have hvop : IsPeriodic om := fun x n => by
    simp only [hvo, isPeriodic_pd v hp 0 x n, isPeriodic_pd v hp 1 x n]
  have hηc : Continuous η := (contDiff_cutoff z ρ).continuous
  have hw : Continuous fun p : ℝ × ℝ => z + polPt p.1 p.2 :=
    continuous_const.add continuous_polPt
  set Φ : ℝ × ℝ → ℝ := fun p => η (z + polPt p.1 p.2) * |om (z + polPt p.1 p.2)| with hΦ
  have hΦc : Continuous Φ := (hηc.comp hw).mul (continuous_abs.comp (hvoc.comp hw))
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x => mul_nonneg (cutoff_nonneg _ _ _) (abs_nonneg _)
  have hpq : Real.HolderConjugate 4 (4 / 3) := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hexp : -((4 / 3 : ℝ) / 4) = -(1 / 3) := by norm_num
  have hsupp : ∀ r θ, 0 < r → (r ≤ 0 ∨ ρ ≤ r) → Φ (r, θ) = 0 := by
    intro r θ hr h
    rcases h with h | h
    · exact absurd h (not_le.2 hr)
    · simp only [hΦ, hη]
      rw [cutoff_eq_zero hρ (by rw [add_sub_cancel_left, euclNorm_polPt hr.le]; exact h), zero_mul]
  have hwI : IntegrableOn (fun r : ℝ => r ^ (-((4 / 3 : ℝ) / 4))) (Ioo 0 ρ) := by
    rw [hexp]
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ)
      (by norm_num : (-1 : ℝ) < -(1 / 3)))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.le] at this
    exact this.mono_set Ioo_subset_Ioc_self
  have h := polar_holder hpq Φ hΦc hΦ0 le_rfl hρ hsupp hwI
  have hc0 : 0 ≤ (2 * π * ∫ r in Ioo 0 ρ, r ^ (-((4 / 3 : ℝ) / 4))) ^ (1 / (4 / 3 : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioo
      fun r hr => Real.rpow_nonneg hr.1.le _)) _
  have hb0 : 0 ≤ (∫ y in cell 2, om y ^ 4) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (setIntegral_nonneg measurableSet_Icc fun y _ => by positivity) _
  refine h.trans (mul_le_mul ?_ (le_of_eq ?_) hc0 hb0)
  · -- the first factor
    refine Real.rpow_le_rpow (setIntegral_nonneg polarCoord.open_target.measurableSet
      fun x hx => ?_) ?_ (by norm_num)
    · rw [polarCoord_target] at hx
      exact mul_nonneg hx.1.le (Real.rpow_nonneg (hΦ0 x) _)
    have e1 : ∫ x in polarCoord.target, x.1 * Φ x ^ (4 : ℝ) =
        ∫ y, (η (z + y) * |om (z + y)|) ^ (4 : ℝ) := by
      rw [← integral_polar (fun y => (η (z + y) * |om (z + y)|) ^ (4 : ℝ))]
      rfl
    rw [e1, integral_add_left_eq_self (fun y => (η y * |om y|) ^ (4 : ℝ)) z]
    refine integral_local_le_cell (fun y => om y ^ 4) (hvoc.pow 4) (fun x n => by
      simp only [hvop x n]) z hρ2 _ (fun y => Real.rpow_nonneg (mul_nonneg (cutoff_nonneg _ _ _) (abs_nonneg _)) _) ?_ ?_
    · intro y
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (η y * |om y|) ^ 4 ≤ |om y| ^ 4 :=
            pow_le_pow_left₀ (mul_nonneg (cutoff_nonneg _ _ _) (abs_nonneg _))
              (mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one _ _ _)) 4
        _ = om y ^ 4 := by
            rw [show |om y| ^ 4 = (|om y| ^ 2) ^ 2 by ring, sq_abs]; ring
    · intro y hy
      simp only [hη, cutoff_eq_zero hρ hy, zero_mul]
      exact Real.zero_rpow (by norm_num)
  · -- the second factor
    rw [hexp, integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le hρ.le,
      integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num), sub_zero]
    rw [show 2 * π * (ρ ^ (-(1 / 3 : ℝ) + 1) / (-(1 / 3) + 1)) = 3 * π * ρ ^ ((2 : ℝ) / 3) by
      norm_num; ring]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hρ.le]
    norm_num

/-- The velocity term: `∫∫ |∇η||v| ≲ ρ⁻¹ ‖v‖₂`. -/
lemma velocity_term : ∃ C, 0 ≤ C ∧ ∀ (v : Pt 2 → Pt 2), ContDiff ℝ 1 v → IsPeriodic v →
    ∀ (z : Pt 2) (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 2 →
    ∫ p in polarCoord.target,
        (|pd 0 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 0 +
            pd 1 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 1| +
          |pd 1 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 0 -
            pd 0 (cutoff z ρ) (z + polPt p.1 p.2) * v (z + polPt p.1 p.2) 1|) ≤
      C / ρ * l2V v := by
  obtain ⟨K, hK0, hK⟩ := pd_cutoff_bound
  refine ⟨Real.sqrt 8 * K * Real.sqrt (2 * π), by positivity, fun v hv hp z ρ hρ hρ2 => ?_⟩
  set η := cutoff z ρ with hη
  set Ψ : Pt 2 → ℝ := fun y => |pd 0 η y * v y 0 + pd 1 η y * v y 1| +
    |pd 1 η y * v y 0 - pd 0 η y * v y 1| with hΨ
  have hηc : ContDiff ℝ 1 η := (contDiff_cutoff z ρ).of_le (by simp)
  have hΨc : Continuous Ψ := by
    have c0 := continuous_pd_of_C1 η hηc 0
    have c1 := continuous_pd_of_C1 η hηc 1
    have v0 := (continuous_apply 0).comp hv.continuous
    have v1 := (continuous_apply 1).comp hv.continuous
    exact (continuous_abs.comp ((c0.mul v0).add (c1.mul v1))).add
      (continuous_abs.comp ((c1.mul v0).sub (c0.mul v1)))
  have hΨ0 : ∀ y, 0 ≤ Ψ y := fun y => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hw : Continuous fun p : ℝ × ℝ => z + polPt p.1 p.2 :=
    continuous_const.add continuous_polPt
  set Φ : ℝ × ℝ → ℝ := fun p => Ψ (z + polPt p.1 p.2) with hΦ
  have hnorm : ∀ r θ, 0 ≤ r → euclNorm (z + polPt r θ - z) = r := fun r θ hr => by
    rw [add_sub_cancel_left, euclNorm_polPt hr]
  have hsupp : ∀ r θ, 0 < r → (r ≤ ρ / 2 ∨ ρ ≤ r) → Φ (r, θ) = 0 := by
    intro r θ hr h
    simp only [hΦ, hΨ, hη]
    rcases h with h | h
    · have hn : euclNorm (z + polPt r θ - z) ≤ ρ / 2 := by rw [hnorm r θ hr.le]; exact h
      simp [pd_cutoff_inner hρ hn]
    · have hn : ρ ≤ euclNorm (z + polPt r θ - z) := by rw [hnorm r θ hr.le]; exact h
      simp [pd_cutoff_outer hρ hn]
  have hwI : IntegrableOn (fun r : ℝ => r ^ (-((2 : ℝ) / 2))) (Ioo (ρ / 2) ρ) := by
    refine (ContinuousOn.integrableOn_Icc (a := ρ / 2) (b := ρ) ?_).mono_set Ioo_subset_Icc_self
    exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (by
      have := hx.1; simp only [id] at *; linarith))
  have h := polar_holder Real.HolderConjugate.two_two Φ (hΨc.comp hw) (fun x => hΨ0 _)
    (by positivity) (by linarith) hsupp hwI
  -- the pointwise bound on `Ψ²`
  have hΨle : ∀ y, Ψ y ^ 2 ≤ 8 * K ^ 2 / ρ ^ 2 * (v y 0 ^ 2 + v y 1 ^ 2) := by
    intro y
    have b0 := hK z ρ hρ 0 y
    have b1 := hK z ρ hρ 1 y
    have hKρ : 0 ≤ K / ρ := by positivity
    have ha : |pd 0 η y * v y 0 + pd 1 η y * v y 1| ≤ K / ρ * (|v y 0| + |v y 1|) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right b0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right b1 (abs_nonneg _))
    have hb : |pd 1 η y * v y 0 - pd 0 η y * v y 1| ≤ K / ρ * (|v y 0| + |v y 1|) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right b1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right b0 (abs_nonneg _))
    have h1 : Ψ y ≤ 2 * (K / ρ) * (|v y 0| + |v y 1|) := by simp only [hΨ]; linarith
    have h2 : (|v y 0| + |v y 1|) ^ 2 ≤ 2 * (v y 0 ^ 2 + v y 1 ^ 2) := by
      rw [← sq_abs (v y 0), ← sq_abs (v y 1)]
      nlinarith [sq_nonneg (|v y 0| - |v y 1|)]
    calc Ψ y ^ 2 ≤ (2 * (K / ρ) * (|v y 0| + |v y 1|)) ^ 2 :=
          pow_le_pow_left₀ (hΨ0 y) h1 2
      _ = 4 * (K / ρ) ^ 2 * (|v y 0| + |v y 1|) ^ 2 := by ring
      _ ≤ 4 * (K / ρ) ^ 2 * (2 * (v y 0 ^ 2 + v y 1 ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 * K ^ 2 / ρ ^ 2 * (v y 0 ^ 2 + v y 1 ^ 2) := by field_simp; ring
  -- the first factor
  have hF1 : ∫ x in polarCoord.target, x.1 * Φ x ^ (2 : ℝ) ≤ 8 * K ^ 2 / ρ ^ 2 * l2sqV v := by
    have e1 : ∫ x in polarCoord.target, x.1 * Φ x ^ (2 : ℝ) = ∫ y, Ψ (z + y) ^ (2 : ℝ) := by
      rw [← integral_polar (fun y => Ψ (z + y) ^ (2 : ℝ))]
      rfl
    rw [e1, integral_add_left_eq_self (fun y => Ψ y ^ (2 : ℝ)) z]
    have hG : IsPeriodic fun y => 8 * K ^ 2 / ρ ^ 2 * (v y 0 ^ 2 + v y 1 ^ 2) := fun x n => by
      simp only [hp x n]
    refine (integral_local_le_cell _ (continuous_const.mul
      ((((continuous_apply 0).comp hv.continuous).pow 2).add
        (((continuous_apply 1).comp hv.continuous).pow 2))) hG z hρ2 _
      (fun y => Real.rpow_nonneg (hΨ0 y) _) (fun y => ?_) (fun y hy => ?_)).trans_eq ?_
    · rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hΨle y
    · simp [hΨ, hη, pd_cutoff_outer hρ hy]
    · show ∫ y in cell 2, 8 * K ^ 2 / ρ ^ 2 * (v y 0 ^ 2 + v y 1 ^ 2) = _
      rw [integral_const_mul]
      unfold l2sqV
      simp [Fin.sum_univ_two]
  -- the second factor
  have hF2 : 2 * π * ∫ r in Ioo (ρ / 2) ρ, r ^ (-((2 : ℝ) / 2)) ≤ 2 * π := by
    have : ∫ r in Ioo (ρ / 2) ρ, r ^ (-((2 : ℝ) / 2)) ≤ 1 := by
      have hle : ∫ r in Ioo (ρ / 2) ρ, r ^ (-((2 : ℝ) / 2)) ≤ ∫ r in Ioo (ρ / 2) ρ, 2 / ρ := by
        refine setIntegral_mono_on hwI (integrableOn_const (by simp)) measurableSet_Ioo
          fun r hr => ?_
        have hr0 : 0 < r := by linarith [hr.1]
        rw [show -((2 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
        rw [inv_eq_one_div, div_le_div_iff₀ hr0 hρ]
        linarith [hr.1]
      refine hle.trans_eq ?_
      rw [integral_const, measureReal_restrict_apply_univ,
        Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul]
      field_simp; ring
    nlinarith [Real.pi_pos]
  refine h.trans ?_
  have hn1 : 0 ≤ ∫ x in polarCoord.target, x.1 * Φ x ^ (2 : ℝ) :=
    setIntegral_nonneg polarCoord.open_target.measurableSet fun x hx => by
      rw [polarCoord_target] at hx
      exact mul_nonneg hx.1.le (Real.rpow_nonneg (hΨ0 _) _)
  have hn2 : 0 ≤ 2 * π * ∫ r in Ioo (ρ / 2) ρ, r ^ (-((2 : ℝ) / 2)) :=
    mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioo
      fun r hr => Real.rpow_nonneg (by linarith [hr.1]) _)
  rw [show (1 : ℝ) / 2 = 1 / 2 from rfl, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  calc Real.sqrt (∫ x in polarCoord.target, x.1 * Φ x ^ (2 : ℝ)) *
        Real.sqrt (2 * π * ∫ r in Ioo (ρ / 2) ρ, r ^ (-((2 : ℝ) / 2)))
      ≤ Real.sqrt (8 * K ^ 2 / ρ ^ 2 * l2sqV v) * Real.sqrt (2 * π) :=
        mul_le_mul (Real.sqrt_le_sqrt hF1) (Real.sqrt_le_sqrt hF2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = Real.sqrt 8 * K * Real.sqrt (2 * π) / ρ * l2V v := by
        unfold l2V
        rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity),
          Real.sqrt_mul (by norm_num), Real.sqrt_sq hK0, Real.sqrt_sq hρ.le]
        ring

/-! ### Assembly -/

/-- The local estimate at scale `ρ`: `|v(z)| ≤ C₁ ‖ω‖₄ √ρ + C₂ ρ⁻¹ ‖v‖₂` for `0 < ρ ≤ 1/2`. -/
lemma pointwise_scale_bound : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    ∀ v : Pt 2 → Pt 2, ContDiff ℝ 1 v → IsPeriodic v → (∀ x, divergence v x = 0) →
    ∀ (z : Pt 2) (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 2 →
    euclNorm (v z) ≤
      C₁ * (∫ y in cell 2, (pd 0 v y 1 - pd 1 v y 0) ^ 4) ^ ((1 : ℝ) / 4) * Real.sqrt ρ +
        C₂ / ρ * l2V v := by
  obtain ⟨C, hC0, hC⟩ := velocity_term
  refine ⟨(3 * π) ^ ((3 : ℝ) / 4) / (2 * π), C / (2 * π), by positivity, by positivity,
    fun v hv hp hdiv z ρ hρ hρ2 => ?_⟩
  have h1 := local_cauchy v hv hdiv z hρ
  have h2 := vorticity_term v hv hp z hρ hρ2
  have h3 := hC v hv hp z ρ hρ hρ2
  rw [Real.sqrt_eq_rpow]
  have hpi : 0 < 2 * π := by positivity
  rw [← mul_le_mul_iff_of_pos_left hpi]
  calc 2 * π * euclNorm (v z) ≤ _ := h1
    _ ≤ _ := add_le_add h2 h3
    _ = _ := by field_simp

/-- An elementary optimization in the scale `ρ`. -/
lemma interp_optimize {C₁ C₂ A W e : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (H : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 → e ≤ C₁ * W * Real.sqrt ρ + C₂ / ρ * A) :
    e ≤ (4 * C₁ + 3 * C₂) * A ^ ((1 : ℝ) / 3) * W ^ ((2 : ℝ) / 3) +
      (4 * C₁ + 3 * C₂) * A := by
  set a := A ^ ((1 : ℝ) / 3) with ha
  set w := W ^ ((1 : ℝ) / 3) with hw
  have ha0 : 0 ≤ a := Real.rpow_nonneg hA _
  have hw0 : 0 ≤ w := Real.rpow_nonneg hW _
  have hAa : A = a ^ 3 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hA]; norm_num
  have hWw : W = w ^ 3 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW]; norm_num
  have hW23 : W ^ ((2 : ℝ) / 3) = w ^ 2 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW]; norm_num
  rw [hW23]
  set C := 4 * C₁ + 3 * C₂ with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hfirst : 0 ≤ C * a * w ^ 2 := by positivity
  rcases eq_or_lt_of_le hw0 with hw' | hw'
  · -- `W = 0`
    have := H (1 / 2) (by norm_num) le_rfl
    rw [hWw, ← hw'] at this
    have hA2 : C₂ / (1 / 2) * A ≤ C * A := by
      rw [div_div_eq_mul_div, div_one]
      exact mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) hA
    simp at this
    nlinarith
  rcases eq_or_lt_of_le ha0 with ha' | ha'
  · -- `A = 0`, `W > 0`: let `ρ → 0`
    have hA0 : A = 0 := by rw [hAa, ← ha']; norm_num
    by_contra hcon
    push_neg at hcon
    have he : 0 < e := by
      have : C * a * w ^ 2 + C * A = 0 := by rw [← ha', hA0]; ring
      linarith
    set M := C₁ * W + 1 with hM
    have hM0 : 0 < M := by positivity
    set ρ := min (1 / 2) ((e / M) ^ 2) with hρ
    have hρ0 : 0 < ρ := lt_min (by norm_num) (by positivity)
    have hρs : Real.sqrt ρ ≤ e / M := by
      calc Real.sqrt ρ ≤ Real.sqrt ((e / M) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
        _ = e / M := Real.sqrt_sq (by positivity)
    have := H ρ hρ0 (min_le_left _ _)
    rw [hA0, mul_zero, add_zero] at this
    have h2 : C₁ * W * Real.sqrt ρ ≤ C₁ * W * (e / M) :=
      mul_le_mul_of_nonneg_left hρs (by positivity)
    have h3 : C₁ * W * (e / M) < e := by
      rw [mul_div_assoc', div_lt_iff₀ hM0]; nlinarith
    linarith
  · -- `A, W > 0`
    by_cases hsmall : (a / w) ^ 2 ≤ 1 / 2
    · have hρ0 : 0 < (a / w) ^ 2 := by positivity
      have := H ((a / w) ^ 2) hρ0 hsmall
      rw [Real.sqrt_sq (by positivity), hAa, hWw] at this
      have e1 : C₁ * w ^ 3 * (a / w) + C₂ / (a / w) ^ 2 * a ^ 3 = (C₁ + C₂) * (a * w ^ 2) := by
        field_simp
      rw [e1] at this
      have : (C₁ + C₂) * (a * w ^ 2) ≤ C * a * w ^ 2 := by
        rw [mul_assoc C]; exact mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) (by positivity)
      nlinarith [hC0, hA]
    · push_neg at hsmall
      have hw2 : w ^ 2 < 2 * a ^ 2 := by
        rw [div_pow, lt_div_iff₀ (by positivity)] at hsmall; linarith
      have hw3 : w ^ 3 ≤ 3 * a ^ 3 := by nlinarith [sq_nonneg (w - 3 / 2 * a)]
      have := H (1 / 2) (by norm_num) le_rfl
      have hs : Real.sqrt (1 / 2) ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
      rw [hWw] at this
      have h1 : C₁ * w ^ 3 * Real.sqrt (1 / 2) ≤ 3 * C₁ * A := by
        rw [hAa]
        calc C₁ * w ^ 3 * Real.sqrt (1 / 2) ≤ C₁ * w ^ 3 * 1 :=
              mul_le_mul_of_nonneg_left hs (by positivity)
          _ ≤ 3 * C₁ * a ^ 3 := by nlinarith
      have h2 : C₂ / (1 / 2) * A = 2 * C₂ * A := by ring
      rw [h2] at this
      have : 3 * C₁ * A + 2 * C₂ * A ≤ C * A := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right (by rw [hCdef]; linarith) hA
      linarith

/-- **Lemma 6.1** (two-dimensional interpolation), in the form proved here: for smooth periodic
divergence-free fields, `|v(x)| ≤ C‖v‖₂^{1/3}‖curl v‖₄^{2/3} + C‖v‖₂`. -/
theorem interpolation_bound : ∃ C : ℝ, ∀ v : Pt 2 → Pt 2, ContDiff ℝ 1 v → IsPeriodic v →
    (∀ x, divergence v x = 0) → ∀ x,
    euclNorm (v x) ≤ C * l2V v ^ ((1 : ℝ) / 3) *
        ((∫ y in cell 2, (pd 0 v y 1 - pd 1 v y 0) ^ 4) ^ ((1 : ℝ) / 4)) ^ ((2 : ℝ) / 3) +
      C * l2V v := by
  obtain ⟨C₁, C₂, hC₁, hC₂, H⟩ := pointwise_scale_bound
  refine ⟨4 * C₁ + 3 * C₂, fun v hv hp hdiv x => ?_⟩
  refine interp_optimize hC₁ hC₂ (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (setIntegral_nonneg measurableSet_Icc fun y _ => by positivity) _)
    fun ρ hρ hρ2 => H v hv hp hdiv x ρ hρ hρ2

/-- **Lemma 6.1** (two-dimensional interpolation).  For mean-zero smooth divergence-free fields
on `𝕋²`, `‖v‖_∞ ≤ C‖v‖₂^{1/3}‖curl v‖₄^{2/3} + C‖v‖₂`.  (The mean-zero hypothesis of the paper
is kept in the statement but is not needed: see `interpolation_bound`.) -/
theorem two_dimensional_interpolation : ∃ C : ℝ, ∀ v : Pt 2 → Pt 2, ContDiff ℝ ∞ v →
    IsPeriodic v → (∫ x in cell 2, v x) = 0 → (∀ x, divergence v x = 0) → ∀ x,
    euclNorm (v x) ≤ C * l2V v ^ ((1 : ℝ) / 3) *
        ((∫ y in cell 2, curl2 v y ^ 4) ^ ((1 : ℝ) / 4)) ^ ((2 : ℝ) / 3) + C * l2V v := by
  obtain ⟨C, hC⟩ := interpolation_bound
  exact ⟨C, fun v hv hp _ hdiv x => hC v (hv.of_le (by simp)) hp hdiv x⟩

end AnomDiss
