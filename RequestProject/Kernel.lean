module

public import RequestProject.Residue
public import RequestProject.PhaseContinuity

/-!
# Section 7: properties of the averaged kernels (Lemma 7.5)
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- The physical pulse operator is given by the (unique) classical solution across `I_j`. -/
lemma pulseOp_spec (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (b : BlockParam L₀) (h : Pt 2 → ℂ) (hh : ContDiff ℝ ∞ h) (hp : IsPeriodic h) :
    ∃ θ : ℝ → Pt 2 → ℂ, IsParabolicC12 (δs j) (1 / 2) θ ∧
      IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t)) h θ ∧
      pulseOp N j b h = θ (δs j) := by
  have hν := viscosity_properties.2.2.1 N (hj.trans hjN)
  have hT := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hT.le, le_rfl⟩
  set v : ℝ → Pt 2 → Pt 2 := fun t => VpulseB (nuN N) j b (sj j + t) with hv
  have hD := vpulse_stage_props (nuN N) (fun _ => b) j
  have hvreg : IsParabolicC01 (δs j) (1 / 2) v :=
    parabolicC01_of_contDiff hT.le (by norm_num) (by norm_num) _ hD.2.1 hD.1
  obtain ⟨θ, hreg, hθ⟩ := complex_scalar_exists hSc hT hν v (fun t _ => hD.1 t) hvreg
    (fun t _ => hD.2.2 t) _ hh hp
  refine ⟨θ, hreg, hθ, ?_⟩
  have hex : ∃ out, ∃ θ' : ℝ → Pt 2 → ℂ, IsClassicalScalar (δs j) (nuN N)
      (fun t => VpulseB (nuN N) j b (sj j + t)) h θ' ∧ θ' (δs j) = out :=
    ⟨_, θ, hθ, rfl⟩
  obtain ⟨θ', hθ', he⟩ := Classical.epsilon_spec hex
  unfold pulseOp
  rw [← he]
  exact complex_scalar_unique hT hν.le v _ θ' θ hθ' hθ _ hTmem

/-- `∫‖h‖² = ‖Re h‖₂² + ‖Im h‖₂²` for continuous `h`. -/
lemma integral_normSq_eq_re_im (h : Pt 2 → ℂ) (hc : Continuous h) :
    ∫ x in cell 2, ‖h x‖ ^ 2 = l2sq (fun x => (h x).re) + l2sq (fun x => (h x).im) := by
  unfold l2sq
  rw [← integral_add]
  · refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    simp only
    rw [← Complex.sq_norm_sub_sq_re, Complex.sq_norm, Complex.normSq_apply]; ring
  · exact ((Complex.continuous_re.comp hc).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  · exact ((Complex.continuous_im.comp hc).pow 2).continuousOn.integrableOn_compact isCompact_Icc

/-- The pulse operator is an `L²` contraction on smooth periodic data. -/
lemma pulseOp_l2_le (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (b : BlockParam L₀) (h : Pt 2 → ℂ) (hh : ContDiff ℝ ∞ h) (hp : IsPeriodic h) :
    Continuous (pulseOp N j b h) ∧ IsPeriodic (pulseOp N j b h) ∧
      ∫ x in cell 2, ‖pulseOp N j b h x‖ ^ 2 ≤ ∫ x in cell 2, ‖h x‖ ^ 2 := by
  obtain ⟨θ, -, hθ, hout⟩ := pulseOp_spec hSc hj hjN b h hh hp
  have hν := viscosity_properties.2.2.1 N (hj.trans hjN)
  have hT := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hT.le, le_rfl⟩
  have hD := vpulse_stage_props (nuN N) (fun _ => b) j
  have hvreg : IsParabolicC01 (δs j) (1 / 2)
      (fun t => VpulseB (nuN N) j b (sj j + t)) :=
    parabolicC01_of_contDiff hT.le (by norm_num) (by norm_num) _ hD.2.1 hD.1
  obtain ⟨β, -, -, hθreg⟩ := hθ.regular
  have houtc : Continuous (θ (δs j)) := (hθreg.smooth_x _ hTmem).continuous
  rw [hout]
  refine ⟨houtc, hθ.periodic _ hTmem, ?_⟩
  have key : ∀ L : ℂ →L[ℝ] ℝ, l2sq (fun x => L (θ (δs j) x)) ≤ l2sq (fun x => L (h x)) := by
    intro L
    have hθL := hθ.clm hT L
    have he := (scalar_energy_max (δs j) (nuN N) (1 / 2) hν _ (fun t _ => hD.1 t) hvreg
      (fun t _ => hD.2.2 t) _ _ hθL).2 _ hTmem
    have hd := dissipation_nonneg' (nuN N) hν.le (fun t x => L (θ t x)) (δs j) hT.le
    linarith
  rw [integral_normSq_eq_re_im _ houtc, integral_normSq_eq_re_im _ hh.continuous]
  have h1 := key Complex.reCLM
  have h2 := key Complex.imCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at h1 h2
  linarith

lemma integral_cell_normSq_expChar (ℓ : Fin 2 → ℤ) :
    ∫ x in cell 2, ‖expChar (intVec ℓ) x‖ ^ 2 = 1 := by
  have : ∀ x, ‖expChar (intVec ℓ) x‖ ^ 2 = 1 := by
    intro x
    simp only [expChar, Complex.norm_exp]
    have : (2 * π * Complex.I * ((dot (intVec ℓ) x : ℝ) : ℂ)).re = 0 := by simp
    rw [this]; simp
  simp only [this]
  simp [cell, Measure.real, Real.volume_Icc_pi]

/-- For each block parameter, `∑ₘ |⟨T e_ℓ, e_m⟩|² ≤ 1`. -/
lemma pulseEntry_hasSum_le (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (b : BlockParam L₀) (ℓ : Fin 2 → ℤ) :
    Summable (fun m => ‖pulseEntry N j b ℓ m‖ ^ 2) ∧
      ∑' m, ‖pulseEntry N j b ℓ m‖ ^ 2 ≤ 1 := by
  obtain ⟨hc, hp, hle⟩ := pulseOp_l2_le hSc hj hjN b _ (contDiff_expChar _) (isPeriodic_expChar ℓ)
  have hs := parseval_cell_complex _ hc hp
  rw [integral_cell_normSq_expChar] at hle
  exact ⟨hs.summable, hs.tsum_eq.trans_le hle⟩

/-- **Lemma 7.5 (1)**: the averaged kernels are substochastic. -/
theorem kernel_substochastic (hSc : ExternalScalar) (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (ℓ : Fin 2 → ℤ) :
    Summable (fun m => kernelK N j ℓ m) ∧ ∑' m, kernelK N j ℓ m ≤ 1 := by
  set f : (Fin 2 → ℤ) → BlockParam L₀ → ℝ := fun m b => ‖pulseEntry N j b ℓ m‖ ^ 2 with hf
  have hfnn : ∀ m b, 0 ≤ f m b := fun _ _ => sq_nonneg _
  have hKnn : ∀ m, 0 ≤ kernelK N j ℓ m := fun m => integral_nonneg (hfnn m)
  have hpart : ∀ s : Finset (Fin 2 → ℤ), ∑ m ∈ s, kernelK N j ℓ m ≤ 1 := by
    intro s
    classical
    set s' := s.filter fun m => Integrable (f m) (blockMeasure L₀)
    have e : ∑ m ∈ s, kernelK N j ℓ m = ∑ m ∈ s', kernelK N j ℓ m := by
      rw [Finset.sum_filter_of_ne]
      intro m _ hm
      by_contra hI
      exact hm (integral_undef hI)
    rw [e]
    have e2 : ∑ m ∈ s', kernelK N j ℓ m = ∫ b, ∑ m ∈ s', f m b ∂(blockMeasure L₀) := by
      rw [integral_finset_sum]
      · rfl
      · intro m hm; exact (Finset.mem_filter.1 hm).2
    rw [e2]
    have hb : ∀ b, ∑ m ∈ s', f m b ≤ 1 := by
      intro b
      obtain ⟨hs, hle⟩ := pulseEntry_hasSum_le hSc hj hjN b ℓ
      exact (hs.sum_le_tsum s' (fun m _ => hfnn m b)).trans hle
    calc ∫ b, ∑ m ∈ s', f m b ∂(blockMeasure L₀) ≤ ∫ _b, (1 : ℝ) ∂(blockMeasure L₀) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun b =>
            Finset.sum_nonneg fun m _ => hfnn m b) (integrable_const _)
            (Eventually.of_forall hb)
      _ = 1 := by simp
  have hs : Summable (fun m => kernelK N j ℓ m) := summable_of_sum_le hKnn hpart
  exact ⟨hs, hs.tsum_le_of_sum_le hpart⟩

end AnomDiss
