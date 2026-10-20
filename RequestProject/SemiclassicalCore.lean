module

public import RequestProject.SemiclassicalAux

/-!
# The semiclassical observable estimate (approximation part of Lemma 3.3)

With `G(y) = e^{2πi ρ e·(Ψ(y) - y)}` and `f(η) = ∫ F(z) e^{2πi z·η} dz`,
`∑ₙ f((ρe+n)/ρ)|Ĝ(n)|² = ∫ F(z) ∫_{𝕋²} e^{2πi ρ e·(Ψ(y+z/ρ) - Ψ(y))} dy dz`, while
`∫_{𝕋²} f(DΨ(y)ᵀe) dy = ∫ F(z) ∫_{𝕋²} e^{2πi e·DΨ(y)z} dy dz`; a second-order Taylor expansion of
`Ψ` bounds the difference by `4πK ∫|z|²|F(z)| dz / ρ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- `c_n^Ψ(ξ) = ∫_{𝕋²} e^{2πi(ξ·w(y) - n·y)} dy` where `Ψ(y) = y + w(y)` (Definition 3.2). -/
def coeffC (Ψ : Pt 2 → Pt 2) (ξ : Pt 2) (n : Fin 2 → ℤ) : ℂ :=
  ∫ y in cell 2, Complex.exp (2 * π * Complex.I * ((dot ξ (Ψ y - y) - dot (intVec n) y : ℝ) : ℂ))

/-- The weight `W_k(v) = min{1, (Rk/|v|)^σ}`, `W_k(0) = 1` (Lemma 3.5). -/
def weightW (σ R k : ℝ) (v : Pt 2) : ℝ :=
  if v = 0 then 1 else min 1 ((R * k / euclNorm v) ^ σ)

lemma weightW_nonneg {σ R k : ℝ} (hRk : 0 ≤ R * k) (v : Pt 2) : 0 ≤ weightW σ R k v := by
  unfold weightW
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (Real.rpow_nonneg (div_nonneg hRk (Real.sqrt_nonneg _)) _)

lemma weightW_le_one (σ R k : ℝ) (v : Pt 2) : weightW σ R k v ≤ 1 := by
  unfold weightW
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- **Lemma 3.3** (semiclassical observable), Parseval part: `∑ₙ |c_n^Ψ(ξ)|² = 1`. -/
theorem coeff_parseval (Ψ : Pt 2 → Pt 2) (hΨ : Continuous Ψ) (hlift : IsLift Ψ) (ξ : Pt 2) :
    HasSum (fun n => ‖coeffC Ψ ξ n‖ ^ 2) 1 := by
  set g : Pt 2 → ℂ := fun y => Complex.exp (2 * π * Complex.I * ((dot ξ (Ψ y - y) : ℝ) : ℂ))
    with hg
  have hgc : Continuous g := by
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    unfold dot
    exact continuous_finset_sum _ fun i _ => continuous_const.mul
      ((continuous_apply i).comp (hΨ.sub continuous_id))
  have hgp : IsPeriodic g := by
    intro y n
    simp only [hg, hlift y n]
    congr 4
    abel_nf
  have hcoef : ∀ n, coeffC Ψ ξ n = fc g n := by
    intro n
    unfold coeffC fc
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp only [hg, expChar, ← Complex.exp_add]
    congr 1
    have : dot (-intVec n) y = -dot (intVec n) y := by simp [dot, Finset.sum_neg_distrib]
    rw [this]; push_cast; ring
  have h1 : ∫ x in cell 2, ‖g x‖ ^ 2 = 1 := by
    have : ∀ x, ‖g x‖ ^ 2 = 1 := by
      intro x
      simp only [hg, Complex.norm_exp]
      have : (2 * π * Complex.I * ((dot ξ (Ψ x - x) : ℝ) : ℂ)).re = 0 := by simp
      rw [this]; simp
    simp only [this]
    simp [cell, Measure.real, Real.volume_Icc_pi]
  have := parseval_cell_complex g hgc hgp
  rw [h1] at this
  simpa only [hcoef] using this

/-- The phase `G(y) = e^{2πi ρ e·(Ψ(y) - y)}` whose Fourier coefficients are `c_n^Ψ(ρe)`. -/
def scPhase (ρ : ℝ) (e : Pt 2) (Ψ : Pt 2 → Pt 2) (y : Pt 2) : ℂ :=
  Complex.exp (2 * π * Complex.I * ((dot (ρ • e) (Ψ y - y) : ℝ) : ℂ))

lemma coeffC_eq_fc_scPhase (Ψ : Pt 2 → Pt 2) (ρ : ℝ) (e : Pt 2) (n : Fin 2 → ℤ) :
    coeffC Ψ (ρ • e) n = fc (scPhase ρ e Ψ) n := by
  unfold coeffC fc
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  simp only [scPhase, expChar, ← Complex.exp_add]
  congr 1
  have : dot (-intVec n) y = -dot (intVec n) y := by simp [dot, Finset.sum_neg_distrib]
  rw [this]; push_cast; ring

lemma continuous_scPhase (ρ : ℝ) (e : Pt 2) {Ψ : Pt 2 → Pt 2} (hΨ : Continuous Ψ) :
    Continuous (scPhase ρ e Ψ) := by
  unfold scPhase dot
  fun_prop

lemma isPeriodic_scPhase (ρ : ℝ) (e : Pt 2) {Ψ : Pt 2 → Pt 2} (hlift : IsLift Ψ) :
    IsPeriodic (scPhase ρ e Ψ) := by
  intro y n
  simp only [scPhase, hlift y n]
  congr 4
  abel_nf

lemma phase_combo (ρ : ℝ) (hρ : ρ ≠ 0) (e : Pt 2) (Ψ : Pt 2 → Pt 2) (z y : Pt 2) :
    expChar z e * (starRingEnd ℂ (scPhase ρ e Ψ y) * scPhase ρ e Ψ (y + ρ⁻¹ • z)) =
      Complex.exp (2 * π * Complex.I * ((ρ * dot e (Ψ (y + ρ⁻¹ • z) - Ψ y) : ℝ) : ℂ)) := by
  simp only [scPhase, expChar]
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  simp only [dot, Fin.sum_univ_two, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  push_cast
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  field_simp
  ring

lemma volume_cell_two : volume (cell 2) = 1 := by
  simp [cell, Real.volume_Icc_pi]

theorem semiclassical_core (f : Pt 2 → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (K : ℝ) : ∃ C : ℝ, ∀ Ψ : Pt 2 → Pt 2, ContDiff ℝ 2 Ψ → IsLift Ψ →
      (∀ y, ‖iteratedFDeriv ℝ 2 Ψ y‖ ≤ K) → ∀ e : Pt 2, euclNorm e = 1 → ∀ ρ : ℝ, 1 ≤ ρ →
      |(∑' n, f (ρ⁻¹ • (ρ • e + intVec n)) * ‖fc (scPhase ρ e Ψ) n‖ ^ 2) -
        ∫ y in cell 2, f ((jac Ψ y)ᵀ *ᵥ e)| ≤ C / ρ := by
  obtain ⟨F, hFc, hFi, hFm, hrep⟩ := fourier_rep_smooth f hf hfc
  refine ⟨4 * π * K * ∫ z, ‖z‖ ^ 2 * ‖F z‖, ?_⟩
  intro Ψ hΨ hlift hK e he ρ hρ
  have hρ0 : 0 < ρ := by linarith
  haveI : IsFiniteMeasure ((volume : Measure (Pt 2)).restrict (cell 2)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_cell_two]; simp⟩
  have hΨc : Continuous Ψ := hΨ.continuous
  have hDc : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv (by norm_num)
  set G := scPhase ρ e Ψ with hGdef
  have hGc : Continuous G := continuous_scPhase ρ e hΨc
  have hGp : IsPeriodic G := isPeriodic_scPhase ρ e hlift
  set c : (Fin 2 → ℤ) → ℝ := fun n => ‖fc G n‖ ^ 2 with hcdef
  have hcs : Summable c := (parseval_cell_complex G hGc hGp).summable
  set Φ : Pt 2 → Pt 2 → ℂ := fun z y =>
    Complex.exp (2 * π * Complex.I * ((ρ * dot e (Ψ (y + ρ⁻¹ • z) - Ψ y) : ℝ) : ℂ)) with hΦdef
  set Φ0 : Pt 2 → Pt 2 → ℂ := fun z y =>
    Complex.exp (2 * π * Complex.I * ((dot e (fderiv ℝ Ψ y z) : ℝ) : ℂ)) with hΦ0def
  have hΦc : Continuous (Function.uncurry Φ) := by
    show Continuous fun p : Pt 2 × Pt 2 => Φ p.1 p.2
    simp only [hΦdef, dot]
    fun_prop
  have hΦ0c : Continuous (Function.uncurry Φ0) := by
    show Continuous fun p : Pt 2 × Pt 2 => Φ0 p.1 p.2
    have h1 : Continuous fun p : Pt 2 × Pt 2 => fderiv ℝ Ψ p.2 p.1 :=
      (hDc.comp continuous_snd).clm_apply continuous_fst
    simp only [hΦ0def, dot]
    fun_prop
  have hΦn : ∀ z y, ‖Φ z y‖ = 1 := by
    intro z y; rw [hΦdef, Complex.norm_exp]; simp
  have hΦ0n : ∀ z y, ‖Φ0 z y‖ = 1 := by
    intro z y; rw [hΦ0def, Complex.norm_exp]; simp
  -- Step A: the series as an integral
  have hA : (((∑' n, f (ρ⁻¹ • (ρ • e + intVec n)) * c n : ℝ)) : ℂ) =
      ∫ z, F z * ∫ y in cell 2, Φ z y := by
    have hH : ∀ n, (((f (ρ⁻¹ • (ρ • e + intVec n)) * c n : ℝ)) : ℂ) =
        ∫ z, F z * expChar z e * (expChar (intVec n) (ρ⁻¹ • z) * (c n : ℂ)) := by
      intro n
      rw [Complex.ofReal_mul, hrep, ← integral_mul_const]
      congr 1; funext z
      rw [expChar_rescale z e n ρ hρ0.ne']; ring
    have hEc : Continuous fun z : Pt 2 => expChar z e := by unfold expChar dot; fun_prop
    have hnorm : ∀ n z, ‖F z * expChar z e * (expChar (intVec n) (ρ⁻¹ • z) * (c n : ℂ))‖ =
        ‖F z‖ * c n := by
      intro n z
      rw [norm_mul, norm_mul, norm_mul, norm_expChar, norm_expChar, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      ring
    have hint : ∀ n, Integrable
        (fun z => F z * expChar z e * (expChar (intVec n) (ρ⁻¹ • z) * (c n : ℂ))) := by
      intro n
      refine (hFi.norm.mul_const (c n)).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · have : Continuous fun z : Pt 2 => expChar (intVec n) (ρ⁻¹ • z) :=
          (continuous_expChar _).comp (continuous_const_smul _)
        exact ((hFc.mul hEc).mul (this.mul continuous_const)).aestronglyMeasurable
      · rw [hnorm]
    have hsum : Summable fun n =>
        ∫ z, ‖F z * expChar z e * (expChar (intVec n) (ρ⁻¹ • z) * (c n : ℂ))‖ := by
      simp_rw [hnorm, integral_mul_const]
      exact hcs.mul_left _
    rw [Complex.ofReal_tsum]
    simp_rw [hH]
    rw [integral_tsum_of_summable_integral_norm hint hsum]
    congr 1; funext z
    rw [tsum_mul_left, (hasSum_char_sq G hGc hGp (ρ⁻¹ • z)).tsum_eq, mul_assoc,
      ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact phase_combo ρ hρ0.ne' e Ψ z y
  -- Step B: the main term as an integral
  have hB : (((∫ y in cell 2, f ((jac Ψ y)ᵀ *ᵥ e) : ℝ)) : ℂ) =
      ∫ z, F z * ∫ y in cell 2, Φ0 z y := by
    have hint2 : Integrable (Function.uncurry fun (y z : Pt 2) => F z * Φ0 z y)
        (((volume : Measure (Pt 2)).restrict (cell 2)).prod volume) := by
      have hbound : Integrable (fun p : Pt 2 × Pt 2 => (1 : ℝ) * ‖F p.2‖)
          (((volume : Measure (Pt 2)).restrict (cell 2)).prod volume) :=
        (integrable_const (1:ℝ)).mul_prod hFi.norm
      refine hbound.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · exact ((hFc.comp continuous_snd).mul (hΦ0c.comp continuous_swap)).aestronglyMeasurable
      · simp [Function.uncurry, hΦ0n]
    rw [← integral_complex_ofReal]
    have hpt : ∀ y, ((f ((jac Ψ y)ᵀ *ᵥ e) : ℝ) : ℂ) = ∫ z, F z * Φ0 z y := by
      intro y; rw [hrep]; congr 1; funext z; rw [hΦ0def]; simp only [expChar, dot_transpose_jac]
    simp_rw [hpt]
    rw [integral_integral_swap hint2]
    congr 1; funext z; rw [integral_const_mul]
  -- Step C: the error bound
  have hC : ‖(∫ z, F z * ∫ y in cell 2, Φ z y) - ∫ z, F z * ∫ y in cell 2, Φ0 z y‖ ≤
      (4 * π * K * ∫ z, ‖z‖ ^ 2 * ‖F z‖) / ρ := by
    set μc := (volume : Measure (Pt 2)).restrict (cell 2) with hμc
    have hμ1 : μc.real univ = 1 := by
      simp [hμc, Measure.real, volume_cell_two]
    have hIy : ∀ (H : Pt 2 → Pt 2 → ℂ), Continuous (Function.uncurry H) → ∀ z,
        Integrable (H z) μc := by
      intro H hH z
      have : Continuous (H z) := hH.comp (Continuous.prodMk_right z)
      exact this.continuousOn.integrableOn_compact isCompact_Icc
    have hbd1 : ∀ (H : Pt 2 → Pt 2 → ℂ), (∀ z y, ‖H z y‖ = 1) → ∀ z,
        ‖∫ y in cell 2, H z y‖ ≤ 1 := by
      intro H hH z
      have := norm_integral_le_of_norm_le_const (μ := μc) (C := 1)
        (Filter.Eventually.of_forall fun y => (hH z y).le)
      rwa [hμ1, mul_one] at this
    have hIz : ∀ (H : Pt 2 → Pt 2 → ℂ), Continuous (Function.uncurry H) → (∀ z y, ‖H z y‖ = 1) →
        Integrable (fun z => F z * ∫ y in cell 2, H z y) := by
      intro H hH hn
      refine (hFi.norm).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · exact hFc.aestronglyMeasurable.mul
          (hH.stronglyMeasurable.integral_prod_right' (ν := μc)).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hbd1 H hn z)
    have hpt : ∀ z y, ‖Φ z y - Φ0 z y‖ ≤ 4 * π * K * ‖z‖ ^ 2 / ρ := by
      intro z y
      simp only [hΦdef, hΦ0def]
      refine (norm_exp2pi_sub_le _ _).trans ?_
      set h : Pt 2 := ρ⁻¹ • z with hhdef
      have hD : fderiv ℝ Ψ y z = ρ • fderiv ℝ Ψ y h := by
        rw [hhdef, ← map_smul, smul_smul, mul_inv_cancel₀ hρ0.ne', one_smul]
      have hid : ρ * dot e (Ψ (y + h) - Ψ y) - dot e (fderiv ℝ Ψ y z) =
          ρ * dot e (Ψ (y + h) - Ψ y - fderiv ℝ Ψ y h) := by
        rw [hD]
        simp only [dot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hid, abs_mul, abs_of_pos hρ0]
      have h1 := abs_dot_le_of_unit e (Ψ (y + h) - Ψ y - fderiv ℝ Ψ y h) he
      have h2 := taylor2_bound Ψ hΨ K hK y h
      have hh : ‖h‖ = ρ⁻¹ * ‖z‖ := by
        rw [hhdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hρ0.le)]
      rw [hh] at h2
      calc 2 * π * (ρ * |dot e (Ψ (y + h) - Ψ y - fderiv ℝ Ψ y h)|)
          ≤ 2 * π * (ρ * (2 * (K * (ρ⁻¹ * ‖z‖) ^ 2))) := by
            gcongr; exact h1.trans (by linarith)
        _ = 4 * π * K * ‖z‖ ^ 2 / ρ := by field_simp; ring
    rw [← integral_sub (hIz Φ hΦc hΦn) (hIz Φ0 hΦ0c hΦ0n)]
    refine (norm_integral_le_of_norm_le (g := fun z => (4 * π * K / ρ) * (‖z‖ ^ 2 * ‖F z‖))
      (hFm.const_mul _) (Filter.Eventually.of_forall fun z => ?_)).trans_eq ?_
    · rw [← mul_sub, ← integral_sub (hIy Φ hΦc z) (hIy Φ0 hΦ0c z), norm_mul]
      have := norm_integral_le_of_norm_le_const (μ := μc)
        (Filter.Eventually.of_forall fun y => hpt z y)
      rw [hμ1, mul_one] at this
      calc ‖F z‖ * ‖∫ y in cell 2, Φ z y - Φ0 z y‖ ≤ ‖F z‖ * (4 * π * K * ‖z‖ ^ 2 / ρ) := by
            gcongr
        _ = 4 * π * K / ρ * (‖z‖ ^ 2 * ‖F z‖) := by ring
    · rw [integral_const_mul]; ring
  rw [← hA, ← hB, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hC
  exact hC

end AnomDiss
