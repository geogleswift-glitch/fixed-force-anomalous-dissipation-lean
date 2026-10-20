module

public import RequestProject.Basic

/-!
# Polar coordinates on `ℝ²` and a Cauchy–Pompeiu type representation

Auxiliary analysis for the two-dimensional interpolation inequality (Lemma 6.1).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace AnomDiss

/-- The point with polar coordinates `(r, θ)`. -/
def polPt (r θ : ℝ) : Pt 2 := ![r * Real.cos θ, r * Real.sin θ]

lemma finTwoArrow_symm_polarCoord_symm (p : ℝ × ℝ) :
    MeasurableEquiv.finTwoArrow.symm (polarCoord.symm p) = polPt p.1 p.2 := by
  rw [polarCoord_symm_apply]
  funext i; fin_cases i <;> rfl

/-- Polar change of variables on `Pt 2`. -/
lemma integral_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Pt 2 → E) :
    ∫ p in polarCoord.target, p.1 • g (polPt p.1 p.2) = ∫ y, g y := by
  have h := integral_comp_polarCoord_symm (fun q => g (MeasurableEquiv.finTwoArrow.symm q))
  simp only [finTwoArrow_symm_polarCoord_symm] at h
  rw [h]
  exact (volume_preserving_finTwoArrow ℝ).symm.integral_comp' g

lemma lintegral_polar (g : Pt 2 → ENNReal) :
    ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * g (polPt p.1 p.2) = ∫⁻ y, g y := by
  have h := lintegral_comp_polarCoord_symm (fun q => g (MeasurableEquiv.finTwoArrow.symm q))
  simp only [finTwoArrow_symm_polarCoord_symm, smul_eq_mul] at h
  rw [h]
  exact (volume_preserving_finTwoArrow ℝ).symm.lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) g

lemma euclNorm_polPt {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : euclNorm (polPt r θ) = r := by
  unfold euclNorm polPt
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq hr

/-- The unit vector `(cos θ, sin θ)`. -/
def uvec (θ : ℝ) : Pt 2 := ![Real.cos θ, Real.sin θ]

/-- The unit vector `(-sin θ, cos θ)`. -/
def uvec' (θ : ℝ) : Pt 2 := ![-Real.sin θ, Real.cos θ]

lemma polPt_eq (r θ : ℝ) : polPt r θ = r • uvec θ := by
  funext i; fin_cases i <;> simp [polPt, uvec]

lemma hasDerivAt_polPt_r (r θ : ℝ) : HasDerivAt (fun r => polPt r θ) (uvec θ) r := by
  simp only [polPt_eq]
  simpa using (hasDerivAt_id r).smul_const (uvec θ)

lemma hasDerivAt_polPt_θ (r θ : ℝ) : HasDerivAt (fun θ => polPt r θ) (r • uvec' θ) θ := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simp only [polPt, uvec', Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
    simpa [mul_neg] using (Real.hasDerivAt_cos θ).const_mul r
  · simp only [polPt, uvec', Fin.mk_one, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    simpa using (Real.hasDerivAt_sin θ).const_mul r

lemma fderiv_apply_vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Pt 2 → E)
    (w : Pt 2) (a b : ℝ) : fderiv ℝ f w ![a, b] = a • pd 0 f w + b • pd 1 f w := by
  have : (![a, b] : Pt 2) = a • (Pi.single 0 1 : Pt 2) + b • (Pi.single 1 1 : Pt 2) := by
    funext i; fin_cases i <;> simp
  rw [this, map_add, map_smul, map_smul]
  rfl

lemma norm_polPt_ge {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : r / 2 ≤ ‖polPt r θ‖ := by
  have h0 : |r * Real.cos θ| ≤ ‖polPt r θ‖ := by
    have := norm_le_pi_norm (polPt r θ) 0
    simpa [polPt] using this
  have h1 : |r * Real.sin θ| ≤ ‖polPt r θ‖ := by
    have := norm_le_pi_norm (polPt r θ) 1
    simpa [polPt] using this
  rw [abs_mul, abs_of_nonneg hr] at h0 h1
  have hc : Real.cos θ ^ 2 ≤ |Real.cos θ| := by
    rw [← sq_abs]; nlinarith [abs_nonneg (Real.cos θ), Real.abs_cos_le_one θ]
  have hs : Real.sin θ ^ 2 ≤ |Real.sin θ| := by
    rw [← sq_abs]; nlinarith [abs_nonneg (Real.sin θ), Real.abs_sin_le_one θ]
  have : 1 ≤ |Real.cos θ| + |Real.sin θ| := by nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith

lemma polPt_pi (r : ℝ) : polPt r π = polPt r (-π) := by
  simp [polPt]

/-- A compactly supported function vanishes far out along every ray. -/
lemma exists_radius_zero {E : Type*} [NormedAddCommGroup E] (g : Pt 2 → E)
    (hs : HasCompactSupport g) (z : Pt 2) :
    ∃ R, 0 < R ∧ ∀ r θ, R ≤ r → g (z + polPt r θ) = 0 := by
  obtain ⟨R', hR'⟩ := hs.isCompact.isBounded.subset_closedBall z
  refine ⟨2 * max R' 0 + 1, by positivity, fun r θ hr => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 := hR' hmem
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] at h1
  have h2 := norm_polPt_ge (show 0 ≤ r by linarith [le_max_right R' 0]) θ
  linarith [le_max_left R' 0]

lemma continuous_polPt : Continuous fun p : ℝ × ℝ => polPt p.1 p.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 * Real.cos p.2)
  · exact (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 * Real.sin p.2)

lemma polPt_zero (θ : ℝ) : polPt 0 θ = 0 := by
  funext i; fin_cases i <;> simp [polPt]

lemma polarTarget_eq :
    volume.restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
  rw [polarCoord_target, Measure.volume_eq_prod, Measure.prod_restrict]

/-- A continuous function of `(r, θ)` vanishing for large `r` is integrable on the polar
target. -/
lemma integrableOn_target_of_radius {E : Type*} [NormedAddCommGroup E] (F : ℝ × ℝ → E)
    (hF : Continuous F) (R : ℝ) (hR : ∀ r θ, R ≤ r → F (r, θ) = 0) :
    IntegrableOn F polarCoord.target := by
  have h1 : IntegrableOn F (Icc 0 R ×ˢ Icc (-π) π) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine h1.of_forall_diff_eq_zero polarCoord.open_target.measurableSet fun p hp => ?_
  obtain ⟨hpt, hpn⟩ := hp
  rw [polarCoord_target] at hpt
  obtain ⟨h0, h2⟩ := hpt
  by_contra hne
  apply hpn
  refine ⟨⟨le_of_lt h0, ?_⟩, ⟨le_of_lt h2.1, le_of_lt h2.2⟩⟩
  by_contra hlt
  exact hne (hR p.1 p.2 (le_of_lt (not_le.1 hlt)))

lemma integrableOn_Ioi_of_radius {E : Type*} [NormedAddCommGroup E] (F : ℝ → E)
    (hF : Continuous F) (R : ℝ) (hR : ∀ r, R ≤ r → F r = 0) :
    IntegrableOn F (Ioi 0) := by
  have h1 : IntegrableOn F (Icc 0 R) := hF.continuousOn.integrableOn_compact isCompact_Icc
  refine h1.of_forall_diff_eq_zero measurableSet_Ioi fun r hr => ?_
  obtain ⟨h0, hn⟩ := hr
  by_contra hne
  exact hn ⟨le_of_lt h0, le_of_lt (not_le.1 fun h => hne (hR r h))⟩

/-- **Cauchy–Pompeiu formula in polar form.**  For a compactly supported `C¹` function
`f : ℝ² → ℂ`, `∫∫ e^{-iθ} (∂₁f + i∂₂f)(z + r e^{iθ}) dr dθ = -2π f(z)`. -/
lemma cauchy_polar (f : Pt 2 → ℂ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (z : Pt 2) :
    ∫ p in polarCoord.target, Complex.exp (-(p.2 : ℂ) * Complex.I) *
        (pd 0 f (z + polPt p.1 p.2) + Complex.I * pd 1 f (z + polPt p.1 p.2)) =
      -(2 * π) * f z := by
  have hdf : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set A : ℝ × ℝ → ℂ := fun p => fderiv ℝ f (z + polPt p.1 p.2) (uvec p.2) with hA
  set B : ℝ × ℝ → ℂ := fun p => fderiv ℝ f (z + polPt p.1 p.2) (uvec' p.2) with hB
  have hw : Continuous fun p : ℝ × ℝ => z + polPt p.1 p.2 := continuous_const.add continuous_polPt
  have huv : Continuous fun p : ℝ × ℝ => uvec p.2 := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos p.2)
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin p.2)
  have huv' : Continuous fun p : ℝ × ℝ => uvec' p.2 := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => -Real.sin p.2)
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos p.2)
  have hAc : Continuous A := (hcf.comp hw).clm_apply huv
  have hBc : Continuous B := (hcf.comp hw).clm_apply huv'
  obtain ⟨R, hR0, hR⟩ := exists_radius_zero (fderiv ℝ f) (hs.fderiv (𝕜 := ℝ)) z
  obtain ⟨R', hR'0, hR'⟩ := exists_radius_zero f hs z
  have hAz : ∀ r θ, R ≤ r → A (r, θ) = 0 := fun r θ h => by simp [hA, hR r θ h]
  have hBz : ∀ r θ, R ≤ r → B (r, θ) = 0 := fun r θ h => by simp [hB, hR r θ h]
  have hAi := integrableOn_target_of_radius A hAc R hAz
  have hBi := integrableOn_target_of_radius B hBc R hBz
  -- pointwise identity
  have hpt : ∀ p : ℝ × ℝ, Complex.exp (-(p.2 : ℂ) * Complex.I) *
      (pd 0 f (z + polPt p.1 p.2) + Complex.I * pd 1 f (z + polPt p.1 p.2)) =
      A p + Complex.I * B p := by
    intro p
    simp only [hA, hB, uvec, uvec', fderiv_apply_vec2, Complex.real_smul]
    rw [show -(p.2 : ℂ) * Complex.I = ((-p.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [hpt]
  rw [integral_add hAi (hBi.const_mul Complex.I), integral_const_mul]
  -- the radial part
  have hArad : ∫ p in polarCoord.target, A p = -(2 * π) * f z := by
    rw [IntegrableOn, polarTarget_eq] at hAi; rw [polarTarget_eq]
    rw [integral_prod_symm _ hAi]
    have hin : ∀ θ, ∫ r in Ioi (0 : ℝ), A (r, θ) = -f z := by
      intro θ
      have hG : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt (fun r => f (z + polPt r θ)) (A (r, θ)) r :=
        fun r _ => (hdf _).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_polPt_r r θ).const_add z)
      have hGc : Continuous fun r => f (z + polPt r θ) :=
        hdf.continuous.comp (continuous_const.add
          (continuous_polPt.comp (continuous_id.prodMk continuous_const)))
      rw [integral_Ioi_of_hasDerivAt_of_tendsto hGc.continuousWithinAt hG
        (integrableOn_Ioi_of_radius _ (hAc.comp (continuous_id.prodMk continuous_const)) R
          (fun r h => hAz r θ h))
        (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R', fun r h => (hR' r θ h).symm⟩))]
      simp [polPt_zero]
    simp only [hin, integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [Real.pi_pos]), Complex.real_smul]
    push_cast; ring
  -- the angular part
  have hBang : ∫ p in polarCoord.target, B p = 0 := by
    rw [IntegrableOn, polarTarget_eq] at hBi; rw [polarTarget_eq]
    rw [integral_prod _ hBi]
    refine (setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_).trans (integral_zero _ _)
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hG : ∀ θ, HasDerivAt (fun θ => (r⁻¹ : ℝ) • f (z + polPt r θ)) (B (r, θ)) θ := by
      intro θ
      have := ((hdf _).hasFDerivAt.comp_hasDerivAt θ
        ((hasDerivAt_polPt_θ r θ).const_add z)).fun_const_smul (r⁻¹ : ℝ)
      simpa only [hB, Function.comp_def, map_smul, smul_smul, inv_mul_cancel₀ hr0,
        one_smul] using this
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      (show -π ≤ π by linarith [Real.pi_pos]),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hG θ)
        ((hBc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _),
      polPt_pi, sub_self]
  rw [hArad, hBang, mul_zero, add_zero]

/-- The Cauchy–Pompeiu bound: `2π |f(z)| ≤ ∫∫ |(∂₁f + i∂₂f)(z + r e^{iθ})| dr dθ`. -/
lemma norm_le_polar (f : Pt 2 → ℂ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (z : Pt 2) :
    2 * π * ‖f z‖ ≤ ∫ p in polarCoord.target,
      ‖pd 0 f (z + polPt p.1 p.2) + Complex.I * pd 1 f (z + polPt p.1 p.2)‖ := by
  have h := cauchy_polar f hf hs z
  have h1 : 2 * π * ‖f z‖ = ‖-(2 * (π : ℂ)) * f z‖ := by
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [h1, ← h]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1; funext p
  rw [norm_mul, show -(p.2 : ℂ) * Complex.I = ((-p.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

lemma volume_polar_box_ne_top (r₀ ρ : ℝ) :
    volume (Ioo r₀ ρ ×ˢ Ioo (-π) π) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc r₀ ρ ×ˢ Icc (-π) π)).measure_lt_top)
  exact Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

/-- Hölder's inequality in polar coordinates with the radial weight `r`, for a continuous
function supported in the annulus `r₀ < r < ρ`. -/
lemma polar_holder {p q : ℝ} (hpq : p.HolderConjugate q) (Φ : ℝ × ℝ → ℝ) (hΦc : Continuous Φ)
    (hΦ0 : ∀ x, 0 ≤ Φ x) {r₀ ρ : ℝ} (hr₀ : 0 ≤ r₀) (hρ : r₀ < ρ)
    (hsupp : ∀ r θ, 0 < r → (r ≤ r₀ ∨ ρ ≤ r) → Φ (r, θ) = 0)
    (hw : IntegrableOn (fun r : ℝ => r ^ (-(q / p))) (Ioo r₀ ρ)) :
    ∫ x in polarCoord.target, Φ x ≤
      (∫ x in polarCoord.target, x.1 * Φ x ^ p) ^ (1 / p) *
        (2 * π * ∫ r in Ioo r₀ ρ, r ^ (-(q / p))) ^ (1 / q) := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set S : Set (ℝ × ℝ) := Ioo r₀ ρ ×ˢ Ioo (-π) π with hS
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hST : S ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono (fun r hr => lt_of_le_of_lt hr₀ hr.1) le_rfl
  haveI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.2 (volume_polar_box_ne_top r₀ ρ)
  have hpos : ∀ x ∈ S, 0 < x.1 := fun x hx => lt_of_le_of_lt hr₀ hx.1.1
  -- step 1: restrict to the box
  have e1 : ∫ x in polarCoord.target, Φ x = ∫ x in S, Φ x := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      polarCoord.open_target.measurableSet hST fun x hx => ?_
    obtain ⟨hxT, hxS⟩ := hx
    rw [polarCoord_target] at hxT
    refine hsupp x.1 x.2 hxT.1 ?_
    by_contra hcon
    push_neg at hcon
    exact hxS ⟨⟨hcon.1, hcon.2⟩, hxT.2⟩
  -- step 2: factor
  set F : ℝ × ℝ → ℝ := fun x => x.1 ^ (1 / p) * Φ x with hF
  set G : ℝ × ℝ → ℝ := fun x => x.1 ^ (-(1 / p)) with hG
  have e2 : ∫ x in S, Φ x = ∫ x in S, F x * G x := by
    refine setIntegral_congr_fun hSm fun x hx => ?_
    simp only [hF, hG]
    rw [mul_comm (x.1 ^ (1 / p)), mul_assoc, ← Real.rpow_add (hpos x hx), add_neg_cancel,
      Real.rpow_zero, mul_one]
  have hFc : Continuous F := (( Real.continuous_rpow_const (by positivity)).comp
    continuous_fst).mul hΦc
  have hGm : Measurable G := by simp only [hG]; fun_prop
  have hF0 : 0 ≤ᵐ[volume.restrict S] F := ae_restrict_of_forall_mem hSm fun x hx =>
    mul_nonneg (Real.rpow_nonneg (hpos x hx).le _) (hΦ0 x)
  have hG0 : 0 ≤ᵐ[volume.restrict S] G := ae_restrict_of_forall_mem hSm fun x hx =>
    Real.rpow_nonneg (hpos x hx).le _
  have hFL : MemLp F (ENNReal.ofReal p) (volume.restrict S) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (s := Icc r₀ ρ ×ˢ Icc (-π) π) hFc.continuousOn
    refine MemLp.of_bound hFc.aestronglyMeasurable C (ae_restrict_of_forall_mem hSm fun x hx => ?_)
    exact hC x (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hx)
  have hrestr : volume.restrict S =
      (volume.restrict (Ioo r₀ ρ)).prod (volume.restrict (Ioo (-π) π)) := by
    rw [hS, Measure.volume_eq_prod, Measure.prod_restrict]
  have hwI : Integrable (fun x : ℝ × ℝ => x.1 ^ (-(q / p)) * (1 : ℝ)) (volume.restrict S) := by
    rw [hrestr]
    haveI : IsFiniteMeasure (volume.restrict (Ioo (-π) π)) :=
      isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
    exact Integrable.mul_prod (f := fun r : ℝ => r ^ (-(q / p))) (g := fun _ : ℝ => (1 : ℝ))
      hw (integrable_const 1)
  have hGq : ∀ x ∈ S, ‖G x‖ ^ q = x.1 ^ (-(q / p)) * 1 := by
    intro x hx
    simp only [hG, mul_one]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hpos x hx).le _), ← Real.rpow_mul (hpos x hx).le]
    congr 1; ring
  have hGL : MemLp G (ENNReal.ofReal q) (volume.restrict S) := by
    rw [← integrable_norm_rpow_iff hGm.aestronglyMeasurable (by simpa using hq0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
    exact hwI.congr (ae_restrict_of_forall_mem hSm fun x hx => (hGq x hx).symm)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hF0 hG0 hFL hGL
  have hGq' : ∀ x ∈ S, G x ^ q = x.1 ^ (-(q / p)) * 1 := fun x hx => by
    rw [← hGq x hx, Real.norm_of_nonneg (Real.rpow_nonneg (hpos x hx).le _)]
  have hn1 : 0 ≤ (∫ x in S, G x ^ q) ^ (1 / q) :=
    Real.rpow_nonneg (integral_nonneg_of_ae (hG0.mono fun x hx => Real.rpow_nonneg hx q)) _
  have hn2 : 0 ≤ (∫ x in polarCoord.target, x.1 * Φ x ^ p) ^ (1 / p) := by
    refine Real.rpow_nonneg (setIntegral_nonneg polarCoord.open_target.measurableSet
      fun x hx => ?_) _
    rw [polarCoord_target] at hx
    exact mul_nonneg hx.1.le (Real.rpow_nonneg (hΦ0 x) _)
  rw [e1, e2]
  refine hH.trans (mul_le_mul ?_ (le_of_eq ?_) hn1 hn2)
  · -- first factor
    refine Real.rpow_le_rpow (integral_nonneg_of_ae (hF0.mono fun x hx => by
      simpa using Real.rpow_nonneg hx p)) ?_ (by positivity)
    have e3 : ∫ x in S, F x ^ p = ∫ x in S, x.1 * Φ x ^ p := by
      refine setIntegral_congr_fun hSm fun x hx => ?_
      simp only [hF]
      rw [Real.mul_rpow (Real.rpow_nonneg (hpos x hx).le _) (hΦ0 x), ← Real.rpow_mul
        (hpos x hx).le, one_div_mul_cancel hp0.ne', Real.rpow_one]
    rw [e3]
    have hcont : Continuous fun x : ℝ × ℝ => x.1 * Φ x ^ p :=
      continuous_fst.mul ((Real.continuous_rpow_const hp0.le).comp hΦc)
    refine setIntegral_mono_set (integrableOn_target_of_radius _ hcont ρ ?_) ?_
      (Eventually.of_forall hST)
    · intro r θ hr
      by_cases h0 : 0 < r
      · simp [hsupp r θ h0 (Or.inr hr), Real.zero_rpow hp0.ne']
      · exfalso; linarith
    · refine ae_restrict_of_forall_mem polarCoord.open_target.measurableSet fun x hx => ?_
      rw [polarCoord_target] at hx
      exact mul_nonneg hx.1.le (Real.rpow_nonneg (hΦ0 x) _)
  · -- second factor
    congr 1
    rw [setIntegral_congr_fun hSm (fun x hx => hGq' x hx), hrestr]
    rw [integral_prod_mul (fun r : ℝ => r ^ (-(q / p))) (fun _ : ℝ => (1 : ℝ))]
    simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
      Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [Real.pi_pos])]
    ring

end AnomDiss
