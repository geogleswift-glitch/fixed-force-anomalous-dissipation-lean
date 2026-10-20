module

public import RequestProject.SemiclassicalCore
public import RequestProject.DampedResponse

/-!
# The weighted Fourier estimate (Lemma 3.5)

The proof follows the paper, except that the low-output region `|ξ + n| ≤ aρ` is handled by
the semiclassical observable estimate (applied to a bump function supported in `|z| ≤ 2a`,
which vanishes on all vectors `DΨ(y)ᵀe`) instead of the non-stationary phase lemma: this gives
a mass `O(1/ρ)`, and since `σ < 1` the weight ratio `(ρ/R)^σ` loses at most `ρ^σ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

lemma contDiff_sumSq : ContDiff ℝ ∞ (fun u : Pt 2 => ∑ i, u i ^ 2) := by
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

lemma sumSq_nonneg (u : Pt 2) : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma euclNorm_sq' (u : Pt 2) : euclNorm u ^ 2 = ∑ i, u i ^ 2 :=
  Real.sq_sqrt (sumSq_nonneg u)

/-- A function vanishing outside `|u| ≥ c` (Euclidean) has compact support. -/
lemma hasCompactSupport_of_euclNorm {f : Pt 2 → ℝ} (c : ℝ)
    (hf : ∀ u, c ≤ euclNorm u → f u = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Pt 2) c) fun u hu => hf u ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hu
  exact (hu.trans_le (norm_le_euclNorm u)).le

/-- A smooth bump which is `1` on `|u| ≤ a` and `0` on `|u| ≥ 2a`. -/
lemma low_bump (a : ℝ) (ha : 0 < a) :
    ∃ g : Pt 2 → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ u, 0 ≤ g u) ∧
      (∀ u, euclNorm u ≤ a → g u = 1) ∧ (∀ u, 2 * a ≤ euclNorm u → g u = 0) := by
  set g : Pt 2 → ℝ := fun u => Real.smoothTransition ((4 * a ^ 2 - ∑ i, u i ^ 2) / (3 * a ^ 2))
  have hg0 : ∀ u, 2 * a ≤ euclNorm u → g u = 0 := by
    intro u hu
    refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ (by positivity))
    rw [← euclNorm_sq']
    nlinarith
  refine ⟨g, ?_, hasCompactSupport_of_euclNorm (2 * a) hg0,
    fun u => Real.smoothTransition.nonneg _, fun u hu => ?_, hg0⟩
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.sub contDiff_sumSq).div_const _)
  · refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ (by positivity), ← euclNorm_sq']
    have := euclNorm_nonneg u
    nlinarith

/-- A smooth compactly supported `f ≥ 0` with `f(u) ≤ |u|^{-σ}`, and equality for
`a ≤ |u| ≤ B`. -/
lemma mid_bump (σ a B : ℝ) (ha : 0 < a) (haB : a ≤ B) :
    ∃ f : Pt 2 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ u, 0 ≤ f u) ∧
      (∀ u, u ≠ 0 → f u ≤ euclNorm u ^ (-σ)) ∧
      (∀ u, a ≤ euclNorm u → euclNorm u ≤ B → f u = euclNorm u ^ (-σ)) := by
  have hB : 0 < B := ha.trans_le haB
  set χ : ℝ → ℝ := fun t => Real.smoothTransition ((t - a ^ 2 / 2) / (a ^ 2 / 2)) *
    Real.smoothTransition ((2 * B ^ 2 - t) / B ^ 2) with hχdef
  have hχ0 : ∀ t, t ≤ a ^ 2 / 2 → χ t = 0 := by
    intro t ht
    simp only [hχdef]
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity)), zero_mul]
  have hχ0' : ∀ t, 2 * B ^ 2 ≤ t → χ t = 0 := by
    intro t ht
    simp only [hχdef]
    rw [Real.smoothTransition.zero_of_nonpos (x := (2 * B ^ 2 - t) / B ^ 2)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)), mul_zero]
  have hχ1 : ∀ t, a ^ 2 ≤ t → t ≤ B ^ 2 → χ t = 1 := by
    intro t h1 h2
    simp only [hχdef]
    rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
    · rw [le_div_iff₀ (by positivity)]; linarith
    · rw [le_div_iff₀ (by positivity)]; linarith
  have hχnn : ∀ t, 0 ≤ χ t := fun t =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hχle : ∀ t, χ t ≤ 1 := fun t =>
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  have hχs : ContDiff ℝ ∞ χ :=
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_id.sub contDiff_const).div_const _)).mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.sub contDiff_id).div_const _))
  set h : ℝ → ℝ := fun t => χ t * t ^ (-σ / 2) with hhdef
  have hhs : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : 0 < t
    · exact hχs.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne ht.ne')
    · push_neg at ht
      have hev : h =ᶠ[𝓝 t] fun _ => 0 := by
        have ha4 : 0 < a ^ 2 / 4 := by positivity
        filter_upwards [Iio_mem_nhds (show t < a ^ 2 / 4 by linarith)] with s hs
        have hs' := (Set.mem_Iio.1 hs).le
        simp only [hhdef, hχ0 s (by linarith), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hpow : ∀ u : Pt 2, euclNorm u ^ (-σ) = (∑ i, u i ^ 2) ^ (-σ / 2) := by
    intro u
    unfold euclNorm
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (sumSq_nonneg u)]
    ring_nf
  refine ⟨fun u => h (∑ i, u i ^ 2), hhs.comp contDiff_sumSq, ?_, fun u => ?_, fun u _ => ?_,
    fun u h1 h2 => ?_⟩
  · refine hasCompactSupport_of_euclNorm (2 * B) fun u hu => ?_
    simp only [hhdef]
    rw [hχ0' _ (by rw [← euclNorm_sq']; nlinarith), zero_mul]
  · exact mul_nonneg (hχnn _) (Real.rpow_nonneg (sumSq_nonneg u) _)
  · simp only [hhdef]
    rw [hpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (sumSq_nonneg u) _) (hχle _)
  · simp only [hhdef]
    have hn := euclNorm_nonneg u
    have e1 : a ^ 2 ≤ ∑ i, u i ^ 2 := by rw [← euclNorm_sq']; nlinarith
    have e2 : ∑ i, u i ^ 2 ≤ B ^ 2 := by rw [← euclNorm_sq']; nlinarith
    rw [hpow, hχ1 _ e1 e2, one_mul]

lemma euclNorm_transpose_mulVec_le (M : Matrix (Fin 2) (Fin 2) ℝ) (K : ℝ)
    (hM : ∀ i j, |M i j| ≤ K) (w : Pt 2) : euclNorm (Mᵀ *ᵥ w) ≤ 2 * K * euclNorm w := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hM 0 0)
  have hcoord : ∀ i, (Mᵀ *ᵥ w) i ^ 2 ≤ 2 * K ^ 2 * (w 0 ^ 2 + w 1 ^ 2) := by
    intro i
    have h1 : (Mᵀ *ᵥ w) i = M 0 i * w 0 + M 1 i * w 1 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h1]
    have a1 := hM 0 i; have a2 := hM 1 i
    have b1 : |M 0 i * w 0| ≤ K * |w 0| := by rw [abs_mul]; gcongr
    have b2 : |M 1 i * w 1| ≤ K * |w 1| := by rw [abs_mul]; gcongr
    have c : |M 0 i * w 0 + M 1 i * w 1| ≤ K * (|w 0| + |w 1|) :=
      (abs_add_le _ _).trans (by linarith)
    have d : (M 0 i * w 0 + M 1 i * w 1) ^ 2 ≤ (K * (|w 0| + |w 1|)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) c 2
    have e : (|w 0| + |w 1|) ^ 2 ≤ 2 * (w 0 ^ 2 + w 1 ^ 2) := by
      nlinarith [sq_abs (w 0), sq_abs (w 1), sq_nonneg (|w 0| - |w 1|)]
    calc _ ≤ (K * (|w 0| + |w 1|)) ^ 2 := d
      _ = K ^ 2 * (|w 0| + |w 1|) ^ 2 := by ring
      _ ≤ K ^ 2 * (2 * (w 0 ^ 2 + w 1 ^ 2)) := by gcongr
      _ = _ := by ring
  unfold euclNorm
  rw [show 2 * K * Real.sqrt (∑ i, w i ^ 2) = Real.sqrt ((2 * K) ^ 2 * ∑ i, w i ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two] at *
  have := hcoord 0; have := hcoord 1
  nlinarith

/-- A uniform bound on the inverse derivative gives a lower bound on `|DΨ(y)ᵀe|`. -/
lemma jac_transpose_lower (Ψ Ψinv : Pt 2 → Pt 2) (hΨ : Differentiable ℝ Ψ)
    (hΨinv : Differentiable ℝ Ψinv) (hli : Function.LeftInverse Ψinv Ψ) (K1 : ℝ)
    (hK1 : ∀ x, ‖fderiv ℝ Ψinv x‖ ≤ K1) (y e : Pt 2) (he : euclNorm e = 1) :
    1 ≤ 2 * K1 * euclNorm ((jac Ψ y)ᵀ *ᵥ e) := by
  have hcomp : jac (Ψinv ∘ Ψ) y = jac Ψinv (Ψ y) * jac Ψ y := jac_comp' (hΨinv _) (hΨ y)
  have hid : Ψinv ∘ Ψ = id := funext hli
  rw [hid, jac_id'] at hcomp
  have hJM : jac Ψ y * jac Ψinv (Ψ y) = 1 := mul_eq_one_comm.mp hcomp.symm
  have he' : e = (jac Ψinv (Ψ y))ᵀ *ᵥ ((jac Ψ y)ᵀ *ᵥ e) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hJM, Matrix.transpose_one,
      Matrix.one_mulVec]
  have hM : ∀ i j, |jac Ψinv (Ψ y) i j| ≤ K1 := by
    intro i j
    simp only [jac, Matrix.of_apply]
    have h1 : ‖(Pi.single j (1:ℝ) : Pt 2)‖ ≤ 1 := by
      refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun k => ?_
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    calc |fderiv ℝ Ψinv (Ψ y) (Pi.single j 1) i|
        = ‖fderiv ℝ Ψinv (Ψ y) (Pi.single j 1) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ Ψinv (Ψ y) (Pi.single j 1)‖ := norm_le_pi_norm _ i
      _ ≤ ‖fderiv ℝ Ψinv (Ψ y)‖ * ‖(Pi.single j (1:ℝ) : Pt 2)‖ := (fderiv ℝ Ψinv (Ψ y)).le_opNorm _
      _ ≤ K1 * 1 := mul_le_mul (hK1 _) h1 (norm_nonneg _) ((norm_nonneg _).trans (hK1 (Ψ y)))
      _ = K1 := mul_one _
  calc (1:ℝ) = euclNorm e := he.symm
    _ = euclNorm ((jac Ψinv (Ψ y))ᵀ *ᵥ ((jac Ψ y)ᵀ *ᵥ e)) := by rw [← he']
    _ ≤ 2 * K1 * euclNorm ((jac Ψ y)ᵀ *ᵥ e) := euclNorm_transpose_mulVec_le _ K1 hM _

/-- Joint measurability of the Jacobian of a measurable family of differentiable maps. -/
lemma measurable_jac_param {Ω' : Type*} [MeasurableSpace Ω'] (Ψ : Ω' → Pt 2 → Pt 2)
    (hmeas : Measurable (Function.uncurry Ψ)) (hd : ∀ o, Differentiable ℝ (Ψ o)) :
    ∀ i j, Measurable (fun p : Ω' × Pt 2 => jac (Ψ p.1) p.2 i j) := by
  intro i j
  set v : Pt 2 := Pi.single j 1
  set F : ℕ → Ω' × Pt 2 → ℝ := fun m p =>
    ((m:ℝ) + 1) * (Ψ p.1 (p.2 + ((m:ℝ) + 1)⁻¹ • v) i - Ψ p.1 p.2 i) with hF
  have hFm : ∀ m, Measurable (F m) := by
    intro m
    have h1 : Measurable fun p : Ω' × Pt 2 => Ψ p.1 (p.2 + ((m:ℝ) + 1)⁻¹ • v) :=
      hmeas.comp (measurable_fst.prodMk (measurable_snd.add_const _))
    have h2 : Measurable fun p : Ω' × Pt 2 => Ψ p.1 p.2 := hmeas
    exact measurable_const.mul (((measurable_pi_apply i).comp h1).sub
      ((measurable_pi_apply i).comp h2))
  refine measurable_of_tendsto_metrizable hFm (tendsto_pi_nhds.2 fun p => ?_)
  obtain ⟨o, y⟩ := p
  have hd : HasDerivAt (fun r : ℝ => Ψ o (y + r • v)) (fderiv ℝ (Ψ o) y v) 0 := by
    have hl : HasDerivAt (fun r : ℝ => y + r • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
    have := (hd o (y + (0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hl
    simpa [Function.comp_def] using this
  have hs := hd.tendsto_slope_zero
  have ht : Tendsto (fun m : ℕ => ((m:ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact Filter.Eventually.of_forall fun m => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]; positivity
  have := ((continuous_apply i).tendsto _).comp (hs.comp ht)
  refine this.congr fun m => ?_
  simp only [Function.comp, hF, zero_add, zero_smul, add_zero, inv_inv, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]

/-- The pointwise comparison of output weight with the three test quantities. -/
lemma weight_term_bound (σ R ρ k q B a : ℝ) (hσ : 0 < σ) (hR : 0 < R) (hRρ : R ≤ ρ)
    (hk : 0 < k) (hq : 0 < q) (hB : 0 < B) (ha : 0 < a) (u v : Pt 2)
    (hv : euclNorm v = k * ρ * euclNorm u) (gu fu : ℝ) (hg0 : 0 ≤ gu) (hf0 : 0 ≤ fu)
    (hglow : euclNorm u ≤ a → gu = 1)
    (hfmid : a ≤ euclNorm u → euclNorm u ≤ B → euclNorm u ^ (-σ) ≤ fu) :
    weightW σ R (q * k) v ≤
      (R / ρ) ^ σ * ((ρ / R) ^ σ * gu + q ^ σ * fu + q ^ σ * B ^ (-σ)) := by
  have hρpos : 0 < ρ := by linarith
  have hA0 : 0 ≤ (R / ρ) ^ σ := by positivity
  have hQ0 : 0 ≤ q ^ σ := by positivity
  have hQf : 0 ≤ q ^ σ * fu := mul_nonneg hQ0 hf0
  have hQB : 0 ≤ q ^ σ * B ^ (-σ) := mul_nonneg hQ0 (by positivity)
  have hWle1 : weightW σ R (q * k) v ≤ 1 := by
    unfold weightW; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hprod : (R / ρ) ^ σ * (ρ / R) ^ σ = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      show R / ρ * (ρ / R) = 1 by field_simp, Real.one_rpow]
  by_cases hu : euclNorm u ≤ a
  · rw [hglow hu]
    calc weightW σ R (q * k) v ≤ 1 := hWle1
      _ = (R / ρ) ^ σ * ((ρ / R) ^ σ * 1) := by rw [mul_one, hprod]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hA0
  · push_neg at hu
    have hu0 : 0 < euclNorm u := ha.trans hu
    have hv0 : 0 < euclNorm v := by rw [hv]; positivity
    have hvne : v ≠ 0 := by
      intro h; rw [h] at hv0; simp [euclNorm] at hv0
    have hW : weightW σ R (q * k) v ≤ (R / ρ) ^ σ * (q ^ σ * euclNorm u ^ (-σ)) := by
      rw [weightW, if_neg hvne]
      refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [hv, show R * (q * k) / (k * ρ * euclNorm u) = (R / ρ) * q * (euclNorm u)⁻¹ by
        field_simp]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg hu0.le,
        Real.inv_rpow hu0.le]
      ring
    refine hW.trans (mul_le_mul_of_nonneg_left ?_ hA0)
    have hg' : 0 ≤ (ρ / R) ^ σ * gu := mul_nonneg (by positivity) hg0
    by_cases huB : euclNorm u ≤ B
    · have := mul_le_mul_of_nonneg_left (hfmid hu.le huB) hQ0
      linarith
    · push_neg at huB
      have := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hB huB.le (by linarith : -σ ≤ 0)) hQ0
      linarith

lemma continuous_jacT_mulVec {Ψ : Pt 2 → Pt 2} (hΨ : ContDiff ℝ 1 Ψ) (e : Pt 2) :
    Continuous fun y => (jac Ψ y)ᵀ *ᵥ e := by
  have hfd : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv one_ne_zero
  have hent : ∀ i j, Continuous fun y => jac Ψ y i j := fun i j =>
    (continuous_apply i).comp (hfd.clm_apply continuous_const)
  refine continuous_pi fun j => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact continuous_finset_sum _ fun i _ => (hent i j).mul continuous_const

lemma continuous_euclNorm : Continuous (euclNorm : Pt 2 → ℝ) := by
  unfold euclNorm; fun_prop

/-- `lemma_fourier_core` under the weaker hypotheses actually used by its proof: `Ψ` a `C²` lift
with bounded first and second derivatives and a `C¹` left inverse with bounded derivative (no
area preservation or right inverse is needed). -/
theorem lemma_fourier_core_C2 (q : ℕ) (hq : 3 ≤ q) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (K : ℕ → ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω')
      [IsProbabilityMeasure P] (Ψ Ψinv : Ω' → Pt 2 → Pt 2),
      Measurable (Function.uncurry Ψ) →
      (∀ o, ContDiff ℝ 2 (Ψ o) ∧ ContDiff ℝ 1 (Ψinv o) ∧ IsLift (Ψ o) ∧
        Function.LeftInverse (Ψinv o) (Ψ o)) →
      (∀ o y, ‖iteratedFDeriv ℝ 1 (Ψ o) y‖ ≤ K 1 ∧ ‖iteratedFDeriv ℝ 2 (Ψ o) y‖ ≤ K 2 ∧
        ‖iteratedFDeriv ℝ 1 (Ψinv o) y‖ ≤ K 1) →
      (∀ e : Pt 2, euclNorm e = 1 →
        ∫ o, (∫ y in cell 2, euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) ^ (-σ)) ∂P ≤
          1 / (32 * (q : ℝ) ^ σ)) →
      ∀ R, R₀ ≤ R → ∀ k : ℕ, 1 ≤ k → ∀ ℓ : Fin 2 → ℤ, R * k ≤ euclNorm (intVec ℓ) →
        ∫ o, ∑' n, weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) *
            ‖coeffC (Ψ o) ((k : ℝ)⁻¹ • intVec ℓ) n‖ ^ 2 ∂P
          ≤ weightW σ R k (intVec ℓ) / 2 := by
  -- constants
  set K1 : ℝ := max (K 1) 1 with hK1def
  have hK1pos : 0 < K1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set a : ℝ := 1 / (8 * K1) with hadef
  have ha : 0 < a := by positivity
  have hqpos : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set Q : ℝ := (q : ℝ) ^ σ with hQdef
  have hQpos : 0 < Q := by positivity
  set B : ℝ := (8:ℝ) ^ (1 / σ) * q with hBdef
  have hBpos : 0 < B := by positivity
  have hqB : Q * B ^ (-σ) = 1 / 8 := by
    rw [hBdef, Real.mul_rpow (by positivity) hqpos.le, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 8)]
    have : 1 / σ * -σ = -1 := by field_simp
    rw [this, Real.rpow_neg hqpos.le, Real.rpow_neg_one, hQdef]
    field_simp
  have haB : a ≤ B := by
    have h1 : a ≤ 1 := by
      rw [hadef, div_le_one (by positivity)]; nlinarith [le_max_right (K 1) 1]
    have h2 : (1:ℝ) ≤ (8:ℝ) ^ (1 / σ) := Real.one_le_rpow (by norm_num) (by positivity)
    have h3 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    nlinarith
  obtain ⟨g, hgs, hgc, hg0, hg1, hg2⟩ := low_bump a ha
  obtain ⟨f, hfs, hfc, hf0, hfle, hfeq⟩ := mid_bump σ a B ha haB
  obtain ⟨Cg, hCg⟩ := semiclassical_core g hgs hgc (K 2)
  obtain ⟨Cf, hCf⟩ := semiclassical_core f hfs hfc (K 2)
  obtain ⟨Mg, hMg⟩ : ∃ M, ∀ u, g u ≤ M := by
    obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hgs.continuous
    exact ⟨M, fun u => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM u))⟩
  obtain ⟨Mf, hMf⟩ : ∃ M, ∀ u, f u ≤ M := by
    obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hfs.continuous
    exact ⟨M, fun u => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM u))⟩
  set Cg' := max Cg 0 with hCg'
  set Cf' := max Cf 0 with hCf'
  refine ⟨max 1 (8 * (Cg' + Q * Cf')), le_max_left _ _, ?_⟩
  intro Ω' _ P _ Ψ Ψinv hmeas hprop hbd hmom R hR k hk ℓ hℓ
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hR8 : 8 * (Cg' + Q * Cf') ≤ R := (le_max_right _ _).trans hR
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  set ξ : Pt 2 := (k:ℝ)⁻¹ • intVec ℓ with hξdef
  set ρ := euclNorm ξ with hρdef
  have hρ : ρ = euclNorm (intVec ℓ) / k := by
    rw [hρdef, hξdef, euclNorm_smul, abs_of_pos (inv_pos.2 hkpos)]; field_simp
  have hRρ : R ≤ ρ := by rw [hρ, le_div_iff₀ hkpos]; exact hℓ
  have hρpos : 0 < ρ := by linarith
  set e : Pt 2 := ρ⁻¹ • ξ with hedef
  have he : euclNorm e = 1 := by
    rw [hedef, euclNorm_smul, abs_of_pos (inv_pos.2 hρpos), ← hρdef]; field_simp
  have hρe : ρ • e = ξ := by rw [hedef, smul_smul, mul_inv_cancel₀ hρpos.ne', one_smul]
  have hWl : weightW σ R k (intVec ℓ) = (R / ρ) ^ σ := by
    have hl0 : intVec ℓ ≠ 0 := by
      intro h
      rw [h] at hℓ
      have : euclNorm (0 : Pt 2) = 0 := by simp [euclNorm]
      rw [this] at hℓ
      nlinarith
    rw [weightW, if_neg hl0]
    have : R * k / euclNorm (intVec ℓ) = R / ρ := by
      rw [hρ]; field_simp
    rw [this, min_eq_right]
    exact Real.rpow_le_one (by positivity) (div_le_one_of_le₀ hRρ hρpos.le) hσ0.le
  -- lower bound on `|DΨᵀe|`
  have hlow : ∀ o y, 4 * a ≤ euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) := by
    intro o y
    have h1 := jac_transpose_lower (Ψ o) (Ψinv o) ((hprop o).1.differentiable (by simp))
      ((hprop o).2.1.differentiable (by simp)) (hprop o).2.2.2 K1 (fun x => by
        have := (hbd o x).2.2
        rw [norm_iteratedFDeriv_one] at this
        exact this.trans (le_max_left _ _)) y e he
    rw [hadef, show 4 * (1 / (8 * K1)) = 1 / (2 * K1) by field_simp; ring,
      div_le_iff₀ (by positivity)]
    linarith
  -- the moment function
  set Z : Ω' → ℝ := fun o => ∫ y in cell 2, euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) ^ (-σ) with hZdef
  have hZint : Integrable Z P := by
    have hent := measurable_jac_param Ψ hmeas fun o => (hprop o).1.differentiable (by simp)
    have hGm : Measurable fun p : Ω' × Pt 2 => euclNorm ((jac (Ψ p.1) p.2)ᵀ *ᵥ e) ^ (-σ) := by
      have hv : Measurable fun p : Ω' × Pt 2 => (jac (Ψ p.1) p.2)ᵀ *ᵥ e := by
        refine Measurable.of_eval fun j => ?_
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        exact Finset.measurable_sum _ fun i _ => (hent i j).mul measurable_const
      exact (continuous_euclNorm.measurable.comp hv).pow_const _
    have hZm : StronglyMeasurable Z :=
      hGm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Pt 2)).restrict (cell 2))
    haveI : IsFiniteMeasure ((volume : Measure (Pt 2)).restrict (cell 2)) :=
      ⟨by rw [Measure.restrict_apply_univ, volume_cell_two]; simp⟩
    refine Integrable.of_bound hZm.aestronglyMeasurable ((4 * a) ^ (-σ))
      (Filter.Eventually.of_forall fun o => ?_)
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Pt 2)).restrict (cell 2))
      (C := (4 * a) ^ (-σ)) (f := fun y => euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) ^ (-σ))
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (euclNorm_nonneg _) _)]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (hlow o y) (by linarith))
    have hμ : ((volume : Measure (Pt 2)).restrict (cell 2)).real univ = 1 := by
      simp [Measure.real, volume_cell_two]
    rw [hμ, mul_one] at this
    exact this
  -- pointwise bound
  have hpt : ∀ o, (∑' n, weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) *
      ‖coeffC (Ψ o) ξ n‖ ^ 2) ≤ (R / ρ) ^ σ * (Cg' / R + Q * (Z o + Cf' / R) + 1 / 8) := by
    intro o
    obtain ⟨hs, hsi, hlift, hli⟩ := hprop o
    have hΨ2 : ContDiff ℝ 2 (Ψ o) := hs
    have hK2 : ∀ y, ‖iteratedFDeriv ℝ 2 (Ψ o) y‖ ≤ K 2 := fun y => (hbd o y).2.1
    set c : (Fin 2 → ℤ) → ℝ := fun n => ‖coeffC (Ψ o) ξ n‖ ^ 2 with hcdef
    have hc1 : HasSum c 1 := coeff_parseval (Ψ o) hs.continuous hlift ξ
    have hc0 : ∀ n, 0 ≤ c n := fun n => sq_nonneg _
    have hcfc : ∀ n, c n = ‖fc (scPhase ρ e (Ψ o)) n‖ ^ 2 := by
      intro n; show ‖coeffC (Ψ o) ξ n‖ ^ 2 = _; rw [← hρe, coeffC_eq_fc_scPhase]
    set u : (Fin 2 → ℤ) → Pt 2 := fun n => ρ⁻¹ • (ρ • e + intVec n) with hudef
    have hv : ∀ n, euclNorm (intVec ℓ + (k:ℝ) • intVec n) = k * ρ * euclNorm (u n) := by
      intro n
      have : intVec ℓ + (k:ℝ) • intVec n = ((k:ℝ) * ρ) • u n := by
        rw [hudef]; simp only
        rw [smul_smul, mul_assoc, mul_inv_cancel₀ hρpos.ne', mul_one, smul_add, hρe, hξdef,
          smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
      rw [this, euclNorm_smul, abs_of_pos (by positivity)]
    have hterm : ∀ n, weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) * c n ≤
        (R / ρ) ^ σ * ((ρ / R) ^ σ * g (u n) + Q * f (u n) + Q * B ^ (-σ)) * c n := fun n =>
      mul_le_mul_of_nonneg_right (weight_term_bound σ R ρ k q B a hσ0 (by linarith) hRρ hkpos
        hqpos hBpos ha (u n) _ (hv n) (g (u n)) (f (u n)) (hg0 _) (hf0 _) (hg1 _)
        (fun h1 h2 => (hfeq _ h1 h2).ge)) (hc0 n)
    have hsg : Summable fun n => g (u n) * c n :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (hg0 _) (hc0 n))
        (fun n => mul_le_mul_of_nonneg_right (hMg _) (hc0 n)) (hc1.summable.mul_left Mg)
    have hsf : Summable fun n => f (u n) * c n :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (hf0 _) (hc0 n))
        (fun n => mul_le_mul_of_nonneg_right (hMf _) (hc0 n)) (hc1.summable.mul_left Mf)
    have hRHS : HasSum
        (fun n => (R / ρ) ^ σ * ((ρ / R) ^ σ * g (u n) + Q * f (u n) + Q * B ^ (-σ)) * c n)
        ((R / ρ) ^ σ * ((ρ / R) ^ σ * (∑' n, g (u n) * c n) + Q * (∑' n, f (u n) * c n) +
          Q * B ^ (-σ) * 1)) := by
      have := (((hsg.hasSum.mul_left ((ρ / R) ^ σ)).add (hsf.hasSum.mul_left Q)).add
        (hc1.mul_left (Q * B ^ (-σ)))).mul_left ((R / ρ) ^ σ)
      convert this using 1
      funext n; ring
    have hLs : Summable fun n =>
        weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) * c n := by
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg ?_ (hc0 n)) hterm hRHS.summable
      unfold weightW; split_ifs
      · exact zero_le_one
      · exact le_min zero_le_one
          (Real.rpow_nonneg (div_nonneg (by positivity) (euclNorm_nonneg _)) _)
    refine (hasSum_le hterm hLs.hasSum hRHS).trans ?_
    -- the three sums
    have hρ1 : 1 ≤ ρ := hR1.trans hRρ
    have hcont : Continuous fun y => (jac (Ψ o) y)ᵀ *ᵥ e := continuous_jacT_mulVec (hs.of_le (by norm_num)) e
    have hSg : ∑' n, g (u n) * c n ≤ Cg' / ρ := by
      have h := hCg (Ψ o) hΨ2 hlift hK2 e he ρ hρ1
      have hz : ∫ y in cell 2, g ((jac (Ψ o) y)ᵀ *ᵥ e) = 0 := by
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
        exact hg2 _ (by linarith [hlow o y])
      rw [hz, sub_zero] at h
      simp only [← hcfc] at h
      have h' : |∑' n, g (u n) * c n| ≤ Cg / ρ := h
      calc ∑' n, g (u n) * c n ≤ Cg / ρ := (le_abs_self _).trans h'
        _ ≤ Cg' / ρ := div_le_div_of_nonneg_right (le_max_left _ _) hρpos.le
    have hSf : ∑' n, f (u n) * c n ≤ Z o + Cf' / ρ := by
      have h := hCf (Ψ o) hΨ2 hlift hK2 e he ρ hρ1
      simp only [← hcfc] at h
      have hle : ∫ y in cell 2, f ((jac (Ψ o) y)ᵀ *ᵥ e) ≤ Z o := by
        rw [hZdef]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => hf0 _) ?_
          (Filter.Eventually.of_forall fun y => ?_)
        · have : Continuous fun y => euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) ^ (-σ) :=
            (continuous_euclNorm.comp hcont).rpow_const fun y =>
              Or.inl (ne_of_gt (lt_of_lt_of_le (by positivity) (hlow o y)))
          exact this.continuousOn.integrableOn_compact isCompact_Icc
        · refine hfle _ fun h0 => ?_
          have := hlow o y
          rw [h0] at this
          have : euclNorm (0 : Pt 2) = 0 := by simp [euclNorm]
          linarith
      have h' : |∑' n, f (u n) * c n - ∫ y in cell 2, f ((jac (Ψ o) y)ᵀ *ᵥ e)| ≤ Cf / ρ := h
      calc ∑' n, f (u n) * c n ≤ (∫ y in cell 2, f ((jac (Ψ o) y)ᵀ *ᵥ e)) + Cf / ρ := by
            have h'' := (le_abs_self _).trans h'
            linarith
        _ ≤ Z o + Cf' / ρ := add_le_add hle (div_le_div_of_nonneg_right (le_max_left _ _) hρpos.le)
    have hpow : (ρ / R) ^ σ ≤ ρ / R := by
      calc (ρ / R) ^ σ ≤ (ρ / R) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ((one_le_div (by linarith)).2 hRρ) hσ1.le
        _ = ρ / R := Real.rpow_one _
    have hW0 : 0 ≤ (R / ρ) ^ σ := by positivity
    have hCg0 : 0 ≤ Cg' := le_max_right _ _
    have hCf0 : 0 ≤ Cf' := le_max_right _ _
    have hSg0 : 0 ≤ ∑' n, g (u n) * c n := tsum_nonneg fun n => mul_nonneg (hg0 _) (hc0 n)
    have e1 : (ρ / R) ^ σ * (∑' n, g (u n) * c n) ≤ Cg' / R := by
      calc (ρ / R) ^ σ * (∑' n, g (u n) * c n) ≤ (ρ / R) * (Cg' / ρ) :=
            mul_le_mul hpow hSg hSg0 (by positivity)
        _ = Cg' / R := by field_simp
    have e2 : Cf' / ρ ≤ Cf' / R := div_le_div_of_nonneg_left hCf0 (by linarith) hRρ
    have e3 : Q * (∑' n, f (u n) * c n) ≤ Q * (Z o + Cf' / R) :=
      mul_le_mul_of_nonneg_left (hSf.trans (by linarith)) hQpos.le
    refine mul_le_mul_of_nonneg_left ?_ hW0
    rw [mul_one, hqB]
    linarith
  have hnn : ∀ o, 0 ≤ ∑' n, weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) *
      ‖coeffC (Ψ o) ξ n‖ ^ 2 := by
    intro o
    refine tsum_nonneg fun n => mul_nonneg ?_ (sq_nonneg _)
    unfold weightW; split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one
        (Real.rpow_nonneg (div_nonneg (by positivity) (euclNorm_nonneg _)) _)
  have hYint : Integrable (fun o => (R / ρ) ^ σ * (Cg' / R + Q * (Z o + Cf' / R) + 1 / 8)) P := by
    have : (fun o => (R / ρ) ^ σ * (Cg' / R + Q * (Z o + Cf' / R) + 1 / 8)) =
        fun o => ((R / ρ) ^ σ * Q) * Z o + (R / ρ) ^ σ * (Cg' / R + Q * Cf' / R + 1 / 8) := by
      funext o; ring
    rw [this]
    exact (hZint.const_mul _).add (integrable_const _)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hYint
    (Filter.Eventually.of_forall hpt)).trans ?_
  have hEZ := hmom e he
  have hIY : ∫ o, (R / ρ) ^ σ * (Cg' / R + Q * (Z o + Cf' / R) + 1 / 8) ∂P =
      ((R / ρ) ^ σ * Q) * (∫ o, Z o ∂P) + (R / ρ) ^ σ * (Cg' / R + Q * Cf' / R + 1 / 8) := by
    have : (fun o => (R / ρ) ^ σ * (Cg' / R + Q * (Z o + Cf' / R) + 1 / 8)) =
        fun o => ((R / ρ) ^ σ * Q) * Z o + (R / ρ) ^ σ * (Cg' / R + Q * Cf' / R + 1 / 8) := by
      funext o; ring
    rw [this, integral_add (hZint.const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp
  rw [hIY, hWl]
  have hW0 : 0 ≤ (R / ρ) ^ σ := by positivity
  have h1 : Q * ∫ o, Z o ∂P ≤ 1 / 32 := by
    calc Q * ∫ o, Z o ∂P ≤ Q * (1 / (32 * Q)) := by gcongr
      _ = 1 / 32 := by field_simp
  have h2 : Cg' / R + Q * Cf' / R ≤ 1 / 8 := by
    rw [← add_div, div_le_iff₀ (by linarith)]; linarith
  nlinarith

theorem lemma_fourier_core (q : ℕ) (hq : 3 ≤ q) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (K : ℕ → ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω')
      [IsProbabilityMeasure P] (Ψ Ψinv : Ω' → Pt 2 → Pt 2),
      Measurable (Function.uncurry Ψ) →
      (∀ o, ContDiff ℝ ∞ (Ψ o) ∧ ContDiff ℝ ∞ (Ψinv o) ∧ IsLift (Ψ o) ∧
        Function.LeftInverse (Ψinv o) (Ψ o) ∧ Function.RightInverse (Ψinv o) (Ψ o) ∧
        ∀ y, (jac (Ψ o) y).det = 1) →
      (∀ o y, ∀ a, 1 ≤ a → ‖iteratedFDeriv ℝ a (Ψ o) y‖ ≤ K a ∧
        ‖iteratedFDeriv ℝ a (Ψinv o) y‖ ≤ K a) →
      (∀ e : Pt 2, euclNorm e = 1 →
        ∫ o, (∫ y in cell 2, euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) ^ (-σ)) ∂P ≤
          1 / (32 * (q : ℝ) ^ σ)) →
      ∀ R, R₀ ≤ R → ∀ k : ℕ, 1 ≤ k → ∀ ℓ : Fin 2 → ℤ, R * k ≤ euclNorm (intVec ℓ) →
        ∫ o, ∑' n, weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) *
            ‖coeffC (Ψ o) ((k : ℝ)⁻¹ • intVec ℓ) n‖ ^ 2 ∂P
          ≤ weightW σ R k (intVec ℓ) / 2 := by
  obtain ⟨R₀, hR₀, h⟩ := lemma_fourier_core_C2 q hq σ hσ0 hσ1 K
  refine ⟨R₀, hR₀, fun Ω' _ P _ Ψ Ψinv hmeas hprop hbd hmom => ?_⟩
  refine h Ω' P Ψ Ψinv hmeas (fun o => ?_) (fun o y => ⟨(hbd o y 1 le_rfl).1, (hbd o y 2 (by norm_num)).1,
    (hbd o y 1 le_rfl).2⟩) hmom
  obtain ⟨h1, h2, h3, h4, -⟩ := hprop o
  exact ⟨h1.of_le (WithTop.coe_le_coe.2 le_top), h2.of_le (WithTop.coe_le_coe.2 le_top), h3, h4⟩

end AnomDiss
