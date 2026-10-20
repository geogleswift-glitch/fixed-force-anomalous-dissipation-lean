module

public import RequestProject.KernelDrift
public import RequestProject.PulseAverage
public import RequestProject.CompScalarFacts
public import RequestProject.HeatFourier

/-!
# Section 7: evolution of the expected Fourier energies (Lemma 7.5 (2))

The quiet interval `J_j` multiplies each Fourier coefficient by a heat factor; across the pulse
interval `I_j` the phase average (Lemma 7.3) removes the cross terms, and independence of the
blocks gives the convolution with the averaged kernel.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-! ### The pulse interval: phase averaging (Lemma 7.3) -/

/-- Averaging over a block parameter: for any continuous periodic real `h` and solutions `φ_b`
across `I_j` started from `h`, `𝔼_b |φ_b(δ_j)^(m)|² = ∑_ℓ K_{j,N}(ℓ,m) |ĥ(ℓ)|²`. -/
lemma pulse_average (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (h : Pt 2 → ℝ) (hc : Continuous h) (hp : IsPeriodic h)
    (φ : BlockParam L₀ → ℝ → Pt 2 → ℝ)
    (hφ : ∀ b, IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t)) h (φ b))
    (m : Fin 2 → ℤ) :
    ∫ b, ‖fc (fun x => (φ b (δs j) x : ℂ)) m‖ ^ 2 ∂(blockMeasure L₀) =
      ∑' ℓ, kernelK N j ℓ m * ‖fc (fun x => (h x : ℂ)) ℓ‖ ^ 2 :=
  (pulse_average_hasSum hSc hj hjN h hc hp φ hφ m).tsum_eq.symm

/-! ### Independence of the blocks -/

/-- Resampling the `j`-th block preserves the law of the phase sequence. -/
lemma phase_update_preserving (j : ℕ) :
    MeasurePreserving (fun p : Phase × BlockParam L₀ => Function.update p.1 j p.2)
      (phaseMeasure.prod (blockMeasure L₀)) phaseMeasure := by
  classical
  have hmeas : Measurable (fun p : Phase × BlockParam L₀ => Function.update p.1 j p.2) := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i = j
    · subst hi; simpa using measurable_snd
    · simpa [Function.update_of_ne hi, Function.comp_def] using
        (measurable_pi_apply i).comp measurable_fst
  refine ⟨hmeas, ?_⟩
  unfold phaseMeasure
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun p : Phase × BlockParam L₀ => Function.update p.1 j p.2) ⁻¹'
      (Set.pi ↑s t) = Set.pi ↑(s.erase j) t ×ˢ (if j ∈ s then t j else Set.univ) := by
    ext ⟨w, b⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i ⟨hij, his⟩ => ?_, ?_⟩
      · have := h i his; rwa [Function.update_of_ne hij] at this
      · split_ifs with hjs
        · have := h j hjs; rwa [Function.update_self] at this
        · trivial
    · rintro ⟨h1, h2⟩ i his
      by_cases hij : i = j
      · subst hij; rw [Function.update_self]; simpa [his] using h2
      · rw [Function.update_of_ne hij]; exact h1 i ⟨hij, his⟩
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht i)]
  by_cases hjs : j ∈ s
  · rw [if_pos hjs, ← Finset.prod_erase_mul _ _ hjs]
  · rw [if_neg hjs, measure_univ, mul_one, Finset.erase_eq_of_notMem hjs]

/-- The comparison scalar up to `s_j` does not depend on the blocks `ω_i`, `i ≥ j`. -/
lemma compScalar_update_eq (hSc : ExternalScalar) (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀)
    (hp : IsPeriodic θ₀) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) (w : Phase) (b : BlockParam L₀) :
    compScalar N (Function.update w j b) θ₀ (sj j) = compScalar N w θ₀ (sj j) := by
  have hN : 1 ≤ N := hj.trans hjN
  have hν := (viscosity_properties.2.2.1 N hN).le
  set w' := Function.update w j b
  have hs := compScalar_spec hSc N hN w θ₀ hθ₀ hp
  have hs' := compScalar_spec hSc N hN w' θ₀ hθ₀ hp
  have hV : ∀ i, i < j → (fun t => Vpulse (nuN N) w' i (sj i + t)) =
      fun t => Vpulse (nuN N) w i (sj i + t) := by
    intro i hi
    funext t x
    simp only [Vpulse, w', Function.update_of_ne hi.ne]
  have key := staged_induction (j - 1) (fun t => compScalar N w' θ₀ t = compScalar N w θ₀ t)
    (by show compScalar N w' θ₀ 0 = compScalar N w θ₀ 0; rw [hs.1, hs'.1]) ?_ ?_
  · have hT : TN (j - 1) = sj j := by unfold TN; congr 1; omega
    have := key (sj j) ⟨(sj_bounds j).1, hT.ge⟩
    exact this
  · intro i hi hij hQ τ hτ
    have h1 := (hs'.2 i hi (by omega)).1
    rw [hV i (by omega), hQ] at h1
    exact classical_scalar_unique _ _ hν _ _ _ _ h1 (hs.2 i hi (by omega)).1 τ hτ
  · intro i hi hij hQ τ hτ
    have h1 := (hs'.2 i hi (by omega)).2
    rw [hQ] at h1
    exact classical_scalar_unique _ _ hν _ _ _ _ h1 (hs.2 i hi (by omega)).2 τ hτ

/-- **Lemma 7.5 (2)**: evolution of the expected Fourier energies. -/
theorem kernel_evolution (hSc : ExternalScalar) (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀)
    (hp : IsPeriodic θ₀) (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (m : Fin 2 → ℤ) :
    ∫ w, ‖fc (fun x => (compScalar N w θ₀ (sj (j + 1)) x : ℂ)) m‖ ^ 2 ∂phaseMeasure =
      heatFactor N j m * ∑' ℓ, kernelK N j ℓ m *
        ∫ w, ‖fc (fun x => (compScalar N w θ₀ (sj j) x : ℂ)) ℓ‖ ^ 2 ∂phaseMeasure := by
  have hN : 1 ≤ N := hj.trans hjN
  set G : Phase → ℝ := fun w => ‖fc (fun x => (compScalar N w θ₀ (sj (j + 1)) x : ℂ)) m‖ ^ 2
    with hG
  set X : (Fin 2 → ℤ) → Phase → ℝ :=
    fun ℓ w => ‖fc (fun x => (compScalar N w θ₀ (sj j) x : ℂ)) ℓ‖ ^ 2 with hX
  have hGm : Measurable G :=
    (compScalar_fourier_measurable_gen hSc θ₀ hθ₀ hp N hN (j + 1) (by omega) (by omega) m).norm.pow_const 2
  have hXm : ∀ ℓ, Measurable (X ℓ) := fun ℓ =>
    (compScalar_fourier_measurable_gen hSc θ₀ hθ₀ hp N hN j hj (by omega) ℓ).norm.pow_const 2
  have hl2 : ∀ w, ∀ t ∈ Icc 0 (TN N), l2sq (compScalar N w θ₀ t) ≤ l2sq θ₀ :=
    fun w t ht => compScalar_l2_le hSc N hN w θ₀ hθ₀ hp t ht
  have hsjI : ∀ i, i ≤ N + 1 → sj i ∈ Icc 0 (TN N) := fun i hi => ⟨(sj_bounds i).1, sj_mono hi⟩
  have hGle : ∀ w, G w ≤ l2sq θ₀ := fun w => by
    obtain ⟨hc, hpp⟩ := compScalar_regular hSc N hN w θ₀ hθ₀ hp (j + 1) (by omega) (by omega)
    exact (fc_sq_le _ hc hpp m).trans (hl2 w _ (hsjI _ (by omega)))
  -- the pointwise identity after resampling block `j`
  have hpt : ∀ w, ∫ b, G (Function.update w j b) ∂(blockMeasure L₀) =
      heatFactor N j m * ∑' ℓ, kernelK N j ℓ m * X ℓ w := by
    intro w
    set w' : BlockParam L₀ → Phase := fun b => Function.update w j b
    have hs := fun b => compScalar_spec hSc N hN (w' b) θ₀ hθ₀ hp
    have hupd : ∀ b, compScalar N (w' b) θ₀ (sj j) = compScalar N w θ₀ (sj j) :=
      fun b => compScalar_update_eq hSc θ₀ hθ₀ hp hj hjN w b
    have hI : ∀ b, IsClassicalScalar (δs j) (nuN N)
        (fun t => VpulseB (nuN N) j b (sj j + t)) (compScalar N w θ₀ (sj j))
        (fun t => compScalar N (w' b) θ₀ (sj j + t)) := by
      intro b
      have := ((hs b).2 j hj hjN).1
      rw [hupd b] at this
      have hV : (fun t => Vpulse (nuN N) (w' b) j (sj j + t)) =
          fun t => VpulseB (nuN N) j b (sj j + t) := by
        funext t x; simp only [Vpulse, w', Function.update_self]
      rwa [hV] at this
    have hJ : ∀ b, G (w' b) = heatFactor N j m *
        ‖fc (fun x => (compScalar N (w' b) θ₀ (sj j + δs j) x : ℂ)) m‖ ^ 2 := by
      intro b
      have hheat := heat_fourier (ηs_nonneg j) _ _ ((hs b).2 j hj hjN).2 m
      show ‖fc (fun x => (compScalar N (w' b) θ₀ (sj (j + 1)) x : ℂ)) m‖ ^ 2 = _
      rw [sj_succ j hj, hheat, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
    obtain ⟨hc, hpp⟩ := compScalar_regular hSc N hN w θ₀ hθ₀ hp j hj (by omega)
    have havg := pulse_average hSc hj hjN _ hc hpp (fun b t => compScalar N (w' b) θ₀ (sj j + t))
      hI m
    refine (integral_congr_ae (Eventually.of_forall fun b => hJ b)).trans ?_
    rw [integral_const_mul, havg]
  have hP := phase_update_preserving j
  have hKnn' : ∀ ℓ m', 0 ≤ kernelK N j ℓ m' := fun ℓ m' => integral_nonneg fun _ => sq_nonneg _
  have hKnn : ∀ ℓ, 0 ≤ kernelK N j ℓ m := fun ℓ => hKnn' ℓ m
  have hKle : ∀ ℓ, kernelK N j ℓ m ≤ 1 := by
    intro ℓ
    obtain ⟨hs, hle⟩ := kernel_substochastic hSc N j hj hjN ℓ
    exact (hs.le_tsum m (fun _ _ => hKnn' ℓ _)).trans hle
  have hXnn : ∀ ℓ w, 0 ≤ X ℓ w := fun _ _ => sq_nonneg _
  have h1 : ∫ w, G w ∂phaseMeasure =
      ∫ p, G (Function.update p.1 j p.2) ∂(phaseMeasure.prod (blockMeasure L₀)) := by
    conv_lhs => rw [← hP.map_eq]
    exact integral_map hP.measurable.aemeasurable hGm.aestronglyMeasurable
  have hGint : Integrable (fun p : Phase × BlockParam L₀ => G (Function.update p.1 j p.2))
      (phaseMeasure.prod (blockMeasure L₀)) := by
    refine Integrable.of_bound (hGm.comp hP.measurable).aestronglyMeasurable (l2sq θ₀)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hGle _
  rw [h1, integral_prod _ hGint]
  simp only [hpt]
  rw [integral_const_mul]
  congr 1
  rw [integral_tsum (fun ℓ => ((hXm ℓ).const_mul _).aestronglyMeasurable)]
  · congr 1; funext ℓ; rw [integral_const_mul]
  · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := l2sq θ₀)) ?_
    calc ∑' ℓ, ∫⁻ w, ‖kernelK N j ℓ m * X ℓ w‖ₑ ∂phaseMeasure
        ≤ ∑' ℓ, ∫⁻ w, ENNReal.ofReal (X ℓ w) ∂phaseMeasure := by
          refine ENNReal.tsum_le_tsum fun ℓ => lintegral_mono fun w => ?_
          rw [Real.enorm_eq_ofReal (mul_nonneg (hKnn ℓ) (hXnn ℓ w))]
          exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hXnn ℓ w) (hKle ℓ))
      _ = ∫⁻ w, ∑' ℓ, ENNReal.ofReal (X ℓ w) ∂phaseMeasure :=
          (lintegral_tsum fun ℓ => (hXm ℓ).ennreal_ofReal.aemeasurable).symm
      _ ≤ ∫⁻ _w, ENNReal.ofReal (l2sq θ₀) ∂phaseMeasure := by
          refine lintegral_mono fun w => ?_
          obtain ⟨hc, hpp⟩ := compScalar_regular hSc N hN w θ₀ hθ₀ hp j hj (by omega)
          have hpar := parseval_cell _ hc hpp
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => hXnn ℓ w) hpar.summable, hpar.tsum_eq]
          exact ENNReal.ofReal_le_ofReal (hl2 w _ (hsjI j (by omega)))
      _ = ENNReal.ofReal (l2sq θ₀) := by simp

/-- **Lemma 7.5** (kernel properties): (1) the kernels are substochastic; (2) the expected
Fourier energies of the comparison scalar evolve by
`X_j(m) = d_{j,N}(m) ∑_ℓ K_{j,N}(ℓ,m) X_{j-1}(ℓ)`; (3) for large `N`, every `j ≤ N` and
`|ℓ| ≥ Rk_j`, `∑ₘ W_{k_{j+1}}(m) K_{j,N}(ℓ,m) ≤ ½ W_{k_j}(ℓ)` (for every `R ≥ R₀`). -/
theorem kernel_properties (hSc : ExternalScalar) :
    (∀ N j, 1 ≤ j → j ≤ N → ∀ ℓ, Summable (fun m => kernelK N j ℓ m) ∧
      ∑' m, kernelK N j ℓ m ≤ 1) ∧
    (∀ θ₀ : Pt 2 → ℝ, ContDiff ℝ ∞ θ₀ → IsPeriodic θ₀ → ∀ N j, 1 ≤ j → j ≤ N → ∀ m,
      ∫ w, ‖fc (fun x => (compScalar N w θ₀ (sj (j + 1)) x : ℂ)) m‖ ^ 2 ∂phaseMeasure =
        heatFactor N j m * ∑' ℓ, kernelK N j ℓ m *
          ∫ w, ‖fc (fun x => (compScalar N w θ₀ (sj j) x : ℂ)) ℓ‖ ^ 2 ∂phaseMeasure) ∧
    (∃ N' : ℕ, ∀ R, R₀ ≤ R → ∀ N, N' ≤ N → ∀ j, 1 ≤ j → j ≤ N → ∀ ℓ : Fin 2 → ℤ,
      R * kk j ≤ euclNorm (intVec ℓ) →
      ∑' m, weightW σ₀ R (kk (j + 1)) (intVec m) * kernelK N j ℓ m
        ≤ weightW σ₀ R (kk j) (intVec ℓ) / 2) :=
  ⟨kernel_substochastic hSc, kernel_evolution hSc, kernel_drift hSc⟩

end AnomDiss
