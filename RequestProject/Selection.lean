module

public import RequestProject.KernelEvolution

/-!
# Section 7 (continued): averaged terminal energy, phase selection, embedding

The averaged terminal estimate (Proposition 7.8), the phase selection (Lemma 7.9), and the
embedding of the two-dimensional problem into three dimensions (Lemma 7.10).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss


lemma l2sq_eq_toReal_tsum (h : Pt 2 → ℝ) (hc : Continuous h) (hp : IsPeriodic h) :
    l2sq h = (∑' ℓ, ENNReal.ofReal (‖fc (fun x => (h x : ℂ)) ℓ‖ ^ 2)).toReal := by
  have hs := parseval_cell h hc hp
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq,
    ENNReal.toReal_ofReal (hs.nonneg (fun _ => sq_nonneg _))]

lemma euclNorm_neg {d : ℕ} (v : Pt d) : euclNorm (-v) = euclNorm v := by
  simp [euclNorm]

lemma weightW_neg (σ R k : ℝ) (v : Pt 2) : weightW σ R k (-v) = weightW σ R k v := by
  simp [weightW, euclNorm_neg, neg_eq_zero]

lemma kk_pos (j : ℕ) : 0 < kk j := by unfold kk; have := qq_ge; positivity

lemma heatFactor_le_one (N j : ℕ) (hN : 1 ≤ N) (m : Fin 2 → ℤ) : heatFactor N j m ≤ 1 := by
  unfold heatFactor
  rw [Real.exp_le_one_iff, neg_nonpos]
  have := (viscosity_properties.2.2.1 N hN).le
  have := ηs_nonneg j
  positivity

lemma heatFactor_last (N : ℕ) (hN : 1 ≤ N) (R : ℝ) (hR : 0 ≤ R) (m : Fin 2 → ℤ)
    (hm : R * kk (N + 1) ≤ euclNorm (intVec m)) :
    heatFactor N N m ≤ Real.exp (-(2 * R ^ 2 * (qq : ℝ) ^ 2)) := by
  unfold heatFactor
  apply Real.exp_le_exp.2
  have hk := kk_pos N
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hη : 0 < ηs N := by unfold ηs τstar; positivity
  have key : 8 * π ^ 2 * nuN N * ηs N = 2 / kk N ^ 2 := by
    unfold nuN; field_simp; ring
  have hkN : kk (N + 1) = qq * kk N := by unfold kk; ring
  rw [hkN] at hm
  have h0 : 0 ≤ R * (qq * kk N) := by have := qq_ge; positivity
  have hsq : (R * (qq * kk N)) ^ 2 ≤ euclNorm (intVec m) ^ 2 := pow_le_pow_left₀ h0 hm 2
  have : 8 * π ^ 2 * nuN N * ηs N * euclNorm (intVec m) ^ 2 =
      2 * euclNorm (intVec m) ^ 2 / kk N ^ 2 := by rw [key]; ring
  rw [this, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  nlinarith

lemma heat_rho_le (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Real.exp (-(2 * Rε ε ^ 2 * (qq : ℝ) ^ 2)) ≤ ε / 16 := by
  have hq : (1 : ℝ) ≤ qq := by have := qq_ge; exact_mod_cast (by omega : 1 ≤ qq)
  have hlog : 0 ≤ Real.log (16 / ε) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hε0]; linarith
  have hR : Real.log (16 / ε) ≤ Rε ε ^ 2 := by
    have h1 : Real.sqrt (Real.log (16 / ε)) ≤ Rε ε := le_max_right _ _
    have h2 := Real.sq_sqrt hlog
    nlinarith [Real.sqrt_nonneg (Real.log (16 / ε))]
  calc Real.exp (-(2 * Rε ε ^ 2 * (qq : ℝ) ^ 2)) ≤ Real.exp (-Real.log (16 / ε)) := by
        apply Real.exp_le_exp.2
        have hq2 : 0 ≤ (qq : ℝ) ^ 2 - 1 := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg (Rε ε)) hq2]
    _ = ε / 16 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

/-- **Proposition 7.8** (averaged terminal energy).  For all large `N`,
`𝔼_ω‖θ̄_ω^{ν_N}(T_N)‖₂² ≤ ε/8`. -/
theorem averaged_terminal (hSc : ExternalScalar) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : ℕ, ∀ N, N' ≤ N →
      ∫ w, l2sq (compScalar N w (theta0 ε) (TN N)) ∂phaseMeasure ≤ ε / 8 := by
  obtain ⟨-, hW0, hθs, hθp, hθl2, -, -, hθfc⟩ := initial_frequency ε hε0
  obtain ⟨hK, hrecK, Nd, hdrift⟩ := kernel_properties hSc
  refine ⟨max Nd 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  set θ₀ := theta0 ε with hθ₀def
  set R := Rε ε with hRdef
  have hR0 : 0 ≤ R := le_trans (Real.sqrt_nonneg _) (le_max_right _ _)
  -- Fourier energies
  set G : ℕ → (Fin 2 → ℤ) → Phase → ℝ := fun j m w =>
    ‖fc (fun x => (compScalar N w θ₀ (sj j) x : ℂ)) m‖ ^ 2 with hGdef
  have hsjI : ∀ j, j ≤ N + 1 → sj j ∈ Icc 0 (TN N) := fun j hj =>
    ⟨(sj_bounds j).1, sj_mono hj⟩
  have hGmeas : ∀ j, 1 ≤ j → j ≤ N + 1 → ∀ m, Measurable (G j m) := fun j hj hjN m =>
    (compScalar_fourier_measurable hSc ε N hN1 j hj hjN m).norm.pow_const 2
  have hGnn : ∀ j m w, 0 ≤ G j m w := fun _ _ _ => sq_nonneg _
  have hGle : ∀ j, 1 ≤ j → j ≤ N + 1 → ∀ m w, G j m w ≤ 1 := by
    intro j hj hjN m w
    obtain ⟨hc, hp⟩ := compScalar_regular hSc N hN1 w θ₀ hθs hθp j hj hjN
    have := fc_sq_le _ hc hp m
    have := compScalar_l2_le hSc N hN1 w θ₀ hθs hθp _ (hsjI j hjN)
    rw [hθl2] at this
    linarith
  have hGint : ∀ j, 1 ≤ j → j ≤ N + 1 → ∀ m, Integrable (G j m) phaseMeasure :=
    fun j hj hjN m => Integrable.of_bound (hGmeas j hj hjN m).aestronglyMeasurable 1
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGnn j m w)]; exact hGle j hj hjN m w)
  set P : ℕ → (Fin 2 → ℤ) → ℝ≥0∞ := fun j m => ∫⁻ w, ENNReal.ofReal (G (j + 1) m w) ∂phaseMeasure
    with hPdef
  have hPX : ∀ j, j ≤ N → ∀ m, P j m = ENNReal.ofReal (∫ w, G (j + 1) m w ∂phaseMeasure) :=
    fun j hj m => (ofReal_integral_eq_lintegral_ofReal (hGint (j + 1) (by omega) (by omega) m)
      (Eventually.of_forall (hGnn _ m))).symm
  have hPsum : ∀ j, j ≤ N → ∑' m, P j m =
      ∫⁻ w, ENNReal.ofReal (l2sq (compScalar N w θ₀ (sj (j + 1)))) ∂phaseMeasure := by
    intro j hj
    rw [← lintegral_tsum (fun m => (hGmeas (j + 1) (by omega) (by omega) m).ennreal_ofReal.aemeasurable)]
    congr 1; funext w
    obtain ⟨hc, hp⟩ := compScalar_regular hSc N hN1 w θ₀ hθs hθp (j + 1) (by omega) (by omega)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => hGnn _ m w) (parseval_cell _ hc hp).summable,
      (parseval_cell _ hc hp).tsum_eq]
  have hPsum_le : ∀ j, j ≤ N → ∑' m, P j m ≤ 1 := by
    intro j hj
    rw [hPsum j hj]
    refine (lintegral_mono fun w => ?_).trans (by simp : ∫⁻ _, (1 : ℝ≥0∞) ∂phaseMeasure ≤ 1)
    refine ENNReal.ofReal_le_one.2 ?_
    have := compScalar_l2_le hSc N hN1 w θ₀ hθs hθp _ (hsjI (j + 1) (by omega))
    rwa [hθl2] at this
  have hKnn : ∀ j ℓ m, 0 ≤ kernelK N j ℓ m := fun _ _ _ => integral_nonneg fun _ => sq_nonneg _
  have hKle1 : ∀ j, 1 ≤ j → j ≤ N → ∀ ℓ m, kernelK N j ℓ m ≤ 1 := fun j hj hjN ℓ m =>
    ((hK N j hj hjN ℓ).1.le_tsum m (fun _ _ => hKnn _ _ _)).trans (hK N j hj hjN ℓ).2
  have hK' : ∀ j, 1 ≤ j → j ≤ N → ∀ ℓ, ∑' m, ENNReal.ofReal (kernelK N j ℓ m) ≤ 1 := by
    intro j hj hjN ℓ
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => hKnn j ℓ m) (hK N j hj hjN ℓ).1]
    exact ENNReal.ofReal_le_one.2 (hK N j hj hjN ℓ).2
  have hWnn : ∀ k m, 0 ≤ weightW σ₀ R (kk k) (intVec m) := fun k m =>
    weightW_nonneg (mul_nonneg hR0 (kk_pos _).le) _
  have hdrift' : ∀ j, 1 ≤ j → j ≤ N → ∀ ℓ, R * kk j ≤ euclNorm (intVec ℓ) →
      ∑' m, ENNReal.ofReal (weightW σ₀ R (kk (j + 1)) (intVec m)) *
          ENNReal.ofReal (kernelK N j ℓ m) ≤
        ENNReal.ofReal (weightW σ₀ R (kk j) (intVec ℓ)) / 2 := by
    intro j hj hjN ℓ hℓ
    have hs : Summable fun m => weightW σ₀ R (kk (j + 1)) (intVec m) * kernelK N j ℓ m :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (hWnn _ m) (hKnn _ _ _))
        (fun m => mul_le_of_le_one_left (hKnn _ _ _) (weightW_le_one _ _ _ _)) (hK N j hj hjN ℓ).1
    calc ∑' m, ENNReal.ofReal (weightW σ₀ R (kk (j + 1)) (intVec m)) *
          ENNReal.ofReal (kernelK N j ℓ m)
        = ∑' m, ENNReal.ofReal (weightW σ₀ R (kk (j + 1)) (intVec m) * kernelK N j ℓ m) := by
          congr 1; funext m; rw [ENNReal.ofReal_mul (hWnn _ m)]
      _ = ENNReal.ofReal (∑' m, weightW σ₀ R (kk (j + 1)) (intVec m) * kernelK N j ℓ m) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (hWnn _ m) (hKnn _ _ _)) hs).symm
      _ ≤ ENNReal.ofReal (weightW σ₀ R (kk j) (intVec ℓ) / 2) :=
          ENNReal.ofReal_le_ofReal (hdrift R (le_max_left _ _) N (le_trans (le_max_left _ _) hN)
            j hj hjN ℓ hℓ)
      _ = _ := by rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hd' : ∀ j, 1 ≤ j → j ≤ N → ∀ m, ENNReal.ofReal (heatFactor N j m) ≤ 1 :=
    fun j _ _ m => ENNReal.ofReal_le_one.2 (heatFactor_le_one N j hN1 m)
  have hP0eq : ∀ ℓ, P 0 ℓ = ENNReal.ofReal (‖fc (fun x => (θ₀ x : ℂ)) ℓ‖ ^ 2) := by
    intro ℓ
    have h0 : ∀ w, compScalar N w θ₀ (sj (0 + 1)) = θ₀ := fun w => by
      rw [zero_add, sj_one]; exact (compScalar_spec hSc N hN1 w θ₀ hθs hθp).1
    simp only [hPdef, hGdef, h0]
    rw [lintegral_const, measure_univ, mul_one]
  have hWℓ : ∀ ℓ, (ℓ = ell0 ε ∨ ℓ = -ell0 ε) →
      weightW σ₀ R (kk 1) (intVec ℓ) = weightW σ₀ R (kk 1) (intVec (ell0 ε)) := by
    rintro ℓ (rfl | rfl)
    · rfl
    · rw [intVec_neg, weightW_neg]
  have hp0low : ∀ ℓ, euclNorm (intVec ℓ) < R * kk 1 → P 0 ℓ = 0 := by
    intro ℓ hℓ
    rw [hP0eq, hθfc]
    split_ifs with h
    · exfalso
      have h1 := weightW_eq_one σ₀_pos _ hℓ
      rw [hWℓ ℓ h] at h1
      linarith
    · simp
  have hrec : ∀ j, 1 ≤ j → j ≤ N → ∀ m, P j m = ENNReal.ofReal (heatFactor N j m) *
      ∑' ℓ, ENNReal.ofReal (kernelK N j ℓ m) * P (j - 1) ℓ := by
    intro j hj hjN m
    have h : ∫ w, G (j + 1) m w ∂phaseMeasure =
        heatFactor N j m * ∑' ℓ, kernelK N j ℓ m * ∫ w, G j ℓ w ∂phaseMeasure :=
      hrecK θ₀ hθs hθp N j hj hjN m
    have hj1 : j - 1 + 1 = j := by omega
    have hPX' : ∀ ℓ, P (j - 1) ℓ = ENNReal.ofReal (∫ w, G j ℓ w ∂phaseMeasure) := fun ℓ => by
      rw [hPX (j - 1) (by omega) ℓ, hj1]
    have hXnn : ∀ ℓ, 0 ≤ ∫ w, G j ℓ w ∂phaseMeasure := fun ℓ => integral_nonneg (hGnn j ℓ)
    have hXs : Summable fun ℓ => ∫ w, G j ℓ w ∂phaseMeasure := by
      have := ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
        (hPsum_le (j - 1) (by omega)))
      refine this.congr fun ℓ => ?_
      rw [hPX' ℓ, ENNReal.toReal_ofReal (hXnn ℓ)]
    have hs : Summable fun ℓ => kernelK N j ℓ m * ∫ w, G j ℓ w ∂phaseMeasure :=
      Summable.of_nonneg_of_le (fun ℓ => mul_nonneg (hKnn _ _ _) (hXnn ℓ))
        (fun ℓ => mul_le_of_le_one_left (hXnn ℓ) (hKle1 j hj hjN ℓ m)) hXs
    rw [hPX j hjN m, h, ENNReal.ofReal_mul (show 0 ≤ heatFactor N j m from (Real.exp_pos _).le),
      ENNReal.ofReal_tsum_of_nonneg (fun ℓ => mul_nonneg (hKnn _ _ _) (hXnn ℓ)) hs]
    congr 1; congr 1; funext ℓ
    rw [ENNReal.ofReal_mul (hKnn _ _ _), hPX' ℓ]
  have hlast : ∀ m, R * kk (N + 1) ≤ euclNorm (intVec m) →
      ENNReal.ofReal (heatFactor N N m) ≤
        ENNReal.ofReal (Real.exp (-(2 * R ^ 2 * (qq : ℝ) ^ 2))) :=
    fun m hm => ENNReal.ofReal_le_ofReal (heatFactor_last N hN1 R hR0 m hm)
  have key := weighted_energy_recursion σ₀ R σ₀_pos N hN1
    (fun j ℓ m => ENNReal.ofReal (kernelK N j ℓ m)) (fun j m => ENNReal.ofReal (heatFactor N j m))
    P _ hK' hdrift' hd' (hPsum_le 0 (Nat.zero_le _)) hp0low hrec hlast
  have hWsum : ∑' ℓ, ENNReal.ofReal (weightW σ₀ R (kk 1) (intVec ℓ)) * P 0 ℓ ≤
      ENNReal.ofReal (ε / 8) := by
    calc ∑' ℓ, ENNReal.ofReal (weightW σ₀ R (kk 1) (intVec ℓ)) * P 0 ℓ
        ≤ ∑' ℓ, ENNReal.ofReal (weightW σ₀ R (kk 1) (intVec (ell0 ε))) * P 0 ℓ := by
          refine ENNReal.tsum_le_tsum fun ℓ => ?_
          rw [hP0eq, hθfc]
          split_ifs with h
          · rw [hWℓ ℓ h]
          · simp
      _ = ENNReal.ofReal (weightW σ₀ R (kk 1) (intVec (ell0 ε))) * ∑' ℓ, P 0 ℓ :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (weightW σ₀ R (kk 1) (intVec (ell0 ε))) * 1 := by
          gcongr; exact hPsum_le 0 (Nat.zero_le _)
      _ ≤ ENNReal.ofReal (ε / 8) := by rw [mul_one]; exact ENNReal.ofReal_le_ofReal hW0
  have hfin : ∑' m, P N m ≤ ENNReal.ofReal (ε / 8) := by
    have h16 : ENNReal.ofReal (ε / 8) / 2 = ENNReal.ofReal (ε / 16) := by
      rw [show ε / 16 = ε / 8 / 2 by ring, ENNReal.ofReal_div_of_pos two_pos,
        ENNReal.ofReal_ofNat]
    calc ∑' m, P N m ≤ _ := key
      _ ≤ ENNReal.ofReal (ε / 8) / 2 + ENNReal.ofReal (ε / 16) := by
          gcongr
          exact heat_rho_le ε hε0 hε1
      _ = ENNReal.ofReal (ε / 8) := by
          rw [h16, ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  -- the terminal energy
  have hmeasT : Measurable fun w => l2sq (compScalar N w θ₀ (TN N)) := by
    have : (fun w => l2sq (compScalar N w θ₀ (TN N))) =
        fun w => (∑' m, ENNReal.ofReal (G (N + 1) m w)).toReal := by
      funext w
      obtain ⟨hc, hp⟩ := compScalar_regular hSc N hN1 w θ₀ hθs hθp (N + 1) (by omega) le_rfl
      exact l2sq_eq_toReal_tsum _ hc hp
    rw [this]
    exact (Measurable.ennreal_tsum fun m =>
      (hGmeas (N + 1) (by omega) le_rfl m).ennreal_ofReal).ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w => l2sq_nonneg' _)
    hmeasT.aestronglyMeasurable]
  have := hPsum N le_rfl
  rw [show TN N = sj (N + 1) from rfl, ← this]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hfin

/-- Measurability of `ω ↦ F_N(ω) = ‖θ̄_ω^{ν_N}(T_N)‖₂²` (first part of the proof of
Lemma 7.9). -/
theorem compScalar_terminal_measurable (hSc : ExternalScalar) (ε : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    Measurable fun w => l2sq (compScalar N w (theta0 ε) (TN N)) := by
  have e : (fun w => l2sq (compScalar N w (theta0 ε) (TN N))) = fun w =>
      (∑' m, ENNReal.ofReal
        (‖fc (fun x => (compScalar N w (theta0 ε) (sj (N + 1)) x : ℂ)) m‖ ^ 2)).toReal := by
    funext w
    obtain ⟨hc, hp⟩ := compScalar_regular hSc N hN w _ (theta0_contDiff ε) (theta0_periodic ε)
      (N + 1) (by omega) le_rfl
    exact l2sq_eq_toReal_tsum _ hc hp
  rw [e]
  exact (Measurable.ennreal_tsum fun m =>
    ((compScalar_fourier_measurable hSc ε N hN (N + 1) (by omega) le_rfl m).norm.pow_const
      2).ennreal_ofReal).ennreal_toReal

/-- **Lemma 7.9** (phase selection).  There are a phase sequence `ω_*` and a strictly
increasing sequence `N_m → ∞`, exceeding any prescribed threshold, such that
`‖θ_{ω_*}^{ν_{N_m}}(T_{N_m})‖₂² ≤ ε` for every `m` (for the true solutions `v`, `θ`). -/
theorem phase_selection (hSc : ExternalScalar) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (Nbar : ℕ) :
    ∃ (wstar : Phase) (Nseq : ℕ → ℕ), StrictMono Nseq ∧ (∀ m, Nbar ≤ Nseq m) ∧
      ∀ m (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
        IsClassicalNS 1 (nuN (Nseq m)) 0 (gForce wstar) v p → ∀ θ : ℝ → Pt 2 → ℝ,
        IsClassicalScalar 1 (nuN (Nseq m)) v (theta0 ε) θ →
        l2sq (θ (TN (Nseq m))) ≤ ε := by
  obtain ⟨-, -, hθs, hθp, hθl2, hθmax, -, -⟩ := initial_frequency ε hε0
  obtain ⟨N', hN'⟩ := averaged_terminal hSc ε hε0 hε1
  obtain ⟨C, N'', htr⟩ := transfer hSc
  -- threshold for the transfer error
  have hlim : Tendsto (fun N : ℕ => 2 * C * Real.sqrt 2 * (N : ℝ) ^ (-(M₀ : ℝ))) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop (y := (M₀ : ℝ)) (by exact_mod_cast M₀_pos)).comp
      tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul (2 * C * Real.sqrt 2)
    rw [mul_zero] at h2
    exact h2
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (half_pos hε0)))
  set N0 := max (max (max N' N'') (max N3 Nbar)) 1 with hN0
  set F : ℕ → Phase → ℝ := fun n w => l2sq (compScalar (n + N0) w (theta0 ε) (TN (n + N0)))
  have hN0' : ∀ n, 1 ≤ n + N0 := fun n => by omega
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    compScalar_terminal_measurable hSc ε (n + N0) (hN0' n)
  have hFnn : ∀ n w, 0 ≤ F n w := fun n w => l2sq_nonneg' _
  have hFle : ∀ n w, F n w ≤ 1 := fun n w => by
    have := compScalar_terminal_le hSc (n + N0) (hN0' n) w (theta0 ε) hθs hθp
    rw [hθl2] at this; exact this
  have hFint : ∀ n, Integrable (F n) phaseMeasure := fun n =>
    Integrable.of_bound (hFmeas n).aestronglyMeasurable 1
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n w)]; exact hFle n w)
  have hlint : ∀ n, ∫⁻ w, ENNReal.ofReal (F n w) ∂phaseMeasure ≤ ENNReal.ofReal (ε / 8) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint n) (Eventually.of_forall (hFnn n))]
    exact ENNReal.ofReal_le_ofReal (hN' (n + N0) (by omega))
  -- Fatou
  have hfatou := lintegral_liminf_le (μ := phaseMeasure) (u := (atTop : Filter ℕ))
    (f := fun n w => ENNReal.ofReal (F n w)) (fun n => (hFmeas n).ennreal_ofReal)
  have hli : liminf (fun n => ∫⁻ w, ENNReal.ofReal (F n w) ∂phaseMeasure) atTop
      ≤ ENNReal.ofReal (ε / 8) :=
    liminf_le_of_frequently_le' (Frequently.of_forall hlint)
  obtain ⟨wstar, hw⟩ := exists_le_lintegral (μ := phaseMeasure)
    (f := fun w => liminf (fun n => ENNReal.ofReal (F n w)) atTop)
    (Measurable.liminf (fun n => (hFmeas n).ennreal_ofReal)).aemeasurable
  have hlt : liminf (fun n => ENNReal.ofReal (F n wstar)) atTop < ENNReal.ofReal (ε / 2) := by
    refine lt_of_le_of_lt (hw.trans (hfatou.trans hli)) ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal (F n wstar) < ENNReal.ofReal (ε / 2) :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨wstar, fun m => φ m + N0, fun a b hab => by simp only; have := hφ hab; omega,
    fun m => by show Nbar ≤ φ m + N0; omega, ?_⟩
  intro m v p hv θ hθ
  set N := φ m + N0
  have hFm : F (φ m) wstar < ε / 2 := by
    have := hφP m
    rwa [ENNReal.ofReal_lt_ofReal_iff (by linarith)] at this
  have htr' := (htr (theta0 ε) hθs hθp hθl2 (Real.sqrt 2) hθmax N (by omega) wstar v p hv θ hθ
    (compScalar N wstar (theta0 ε)) (compScalar_spec hSc N (hN0' _) wstar _ hθs hθp)).2
  have hsmall := hN3 N (by omega)
  have hF' : l2sq (compScalar N wstar (theta0 ε) (TN N)) < ε / 2 := hFm
  have := (abs_le.1 htr').2
  linarith

/-! ### Lemma 7.10: embedding into three dimensions -/

/-! The projection `proj3` and the embedding `embedU` are defined in
`RequestProject.EmbeddingCalc`. -/

lemma continuous_pd {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : Pt d → E} (hh : ContDiff ℝ 1 h) (i : Fin d) : Continuous (pd i h) := by
  unfold pd
  exact (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- **Lemma 7.10** (two- to three-dimensional embedding).  If `(v,p)` solves the forced 2D
Navier–Stokes system and `θ` the advection–diffusion equation with drift `v`, then
`u = (v₁,v₂,θ)`, `P = p` solve the forced 3D Navier–Stokes system with force `(g₁,g₂,0)`, and
`‖∇u(t)‖²_{L²(𝕋³)} = ‖∇v(t)‖²_{L²(𝕋²)} + ‖∇θ(t)‖²_{L²(𝕋²)}`. -/
theorem two_to_three_embedding (T ν β : ℝ) (hT : 0 < T) (hβ0 : 0 < β) (hβ1 : β < 1)
    (v₀ : Pt 2 → Pt 2) (g : ℝ → Pt 2 → Pt 2) (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ)
    (hv : IsClassicalNS T ν v₀ g v p) (hvreg : IsParabolicC12 T β v)
    (hpreg : IsParabolicC01 T β p) (θ₀ : Pt 2 → ℝ) (θ : ℝ → Pt 2 → ℝ)
    (hθ : IsClassicalScalar T ν v θ₀ θ) (hθreg : IsParabolicC12 T β θ) :
    IsClassicalNS T ν (embedU v₀ θ₀) (fun t => embedU (g t) 0) (fun t => embedU (v t) (θ t))
      (fun t x => p t (proj3 x)) ∧
    ∀ t ∈ Icc 0 T, ∫ x in cell 3, gradSqV (embedU (v t) (θ t)) x =
      (∫ x in cell 2, gradSqV (v t) x) + ∫ x in cell 2, gradSq (θ t) x := by
  have d1 : ∀ t ∈ Icc 0 T, Differentiable ℝ (v t) := fun t ht =>
    (hvreg.smooth_x t ht).differentiable (by norm_num)
  have d1' : ∀ t ∈ Icc 0 T, Differentiable ℝ (θ t) := fun t ht =>
    (hθreg.smooth_x t ht).differentiable (by norm_num)
  have dp : ∀ t ∈ Icc 0 T, Differentiable ℝ (p t) := fun t ht =>
    (hpreg.smooth_x t ht).differentiable (by norm_num)
  refine ⟨⟨fun t ht => isPeriodic_embedU (hv.periodic_u t ht) (hθ.periodic t ht),
    fun t ht => isPeriodic_comp_proj3 (hv.periodic_p t ht),
    ⟨β, hβ0, hβ1, parabolicC12_embedU hT hβ0 hvreg hθreg, parabolicC01_comp_proj3 hβ0 hpreg⟩,
    ?_, ?_, ?_⟩, ?_⟩
  · show embedU (v 0) (θ 0) = embedU v₀ θ₀
    rw [hv.init, hθ.init]
  · intro t ht x
    rw [divergence_embedU (d1 t ht) (d1' t ht)]
    exact hv.div_free t ht _
  · intro t ht x
    rw [dt_embedU hT ht (fun y => hvreg.diff_t y t ht) (fun y => hθreg.diff_t y t ht),
      conv_embedU (d1 t ht) (d1' t ht), grad_comp_proj3 _ (dp t ht),
      lap_embedU (hvreg.smooth_x t ht) (hθreg.smooth_x t ht)]
    have e1 := hv.eqn t ht (proj3 x)
    have e2 := hθ.eqn t ht (proj3 x)
    ext k
    fin_cases k
    · have := congrFun e1 0
      simp only [Pi.add_apply, Pi.smul_apply] at this
      simp [embedU, this]
    · have := congrFun e1 1
      simp only [Pi.add_apply, Pi.smul_apply] at this
      simp [embedU, this]
    · simp [embedU, e2]
  · intro t ht
    have hcont1 : Continuous (gradSqV (v t)) := by
      unfold gradSqV
      have : ∀ i, Continuous (pd i (v t)) := fun i =>
        continuous_pd ((hvreg.smooth_x t ht).of_le (by norm_num)) i
      fun_prop
    have hcont2 : Continuous (gradSq (θ t)) := by
      unfold gradSq
      have : ∀ i, Continuous (pd i (θ t)) := fun i =>
        continuous_pd ((hθreg.smooth_x t ht).of_le (by norm_num)) i
      fun_prop
    have : (fun x => gradSqV (embedU (v t) (θ t)) x) =
        fun x => (fun y => gradSqV (v t) y + gradSq (θ t) y) (proj3 x) := by
      funext x; exact gradSqV_embedU (d1 t ht) (d1' t ht) x
    rw [this]
    exact (integral_cell3 (fun y => gradSqV (v t) y + gradSq (θ t) y)).trans
      (integral_add hcont1.integrableOn_Icc hcont2.integrableOn_Icc)

end AnomDiss
