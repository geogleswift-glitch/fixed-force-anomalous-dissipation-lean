module

public import RequestProject.Kernel
public import RequestProject.Rescale

/-!
# Section 7: the weighted drift inequality for the averaged kernels (Lemma 7.5 (3))

The pulse operator across `I_j`, rescaled by `s = (t - s_j)/δ_j` and `y = k_j x`, is the
time-one solution operator of the cell problem of Definition 3.6 with `μ = μ_{j,N}`; its matrix
coefficients are the coefficients `a_n^{μ,ω}(ℓ/k_j)`, so the drift inequality is Proposition 3.11.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

section TorusScaling

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- `∫_{𝕋²} g(kx) dx = ∫_{𝕋²} g` for periodic `g` and a positive integer `k`. -/
lemma integral_cell_comp_nsmul (g : Pt 2 → ℂ) (hg : Continuous g) (hp : IsPeriodic g) (k : ℕ)
    (hk : 0 < k) : ∫ x in cell 2, g ((k : ℝ) • x) = ∫ x in cell 2, g x := by
  have hmap := map_cell_comp_of_torus g hg hp (fun z => (k : ℝ) • z)
    (fun u i => (k : ℤ) • u i) ?_ ?_
  · have := congrArg (fun μ : Measure ℂ => ∫ y, y ∂μ) hmap
    rwa [integral_map (show AEMeasurable (fun z => g ((k : ℝ) • z)) _ from
      (hg.comp (continuous_const_smul _)).aemeasurable) measurable_id'.aestronglyMeasurable,
      integral_map hg.aemeasurable measurable_id'.aestronglyMeasurable] at this
  · exact measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun i => Measure.measurePreserving_zsmul volume (by exact_mod_cast hk.ne')
  · intro z; funext i; simp [torusProj]

end TorusScaling

/-- Classical solutions inherit a quasi-periodicity of the initial datum under translations
preserving the drift. -/
lemma scalar_quasi {T ν : ℝ} (hT : 0 < T) (hν : 0 ≤ ν) (v : ℝ → Pt 2 → Pt 2)
    (θ₀ : Pt 2 → ℂ) (θ : ℝ → Pt 2 → ℂ) (hθ : IsClassicalScalar T ν v θ₀ θ) (c : Pt 2)
    (hv : ∀ t ∈ Icc 0 T, ∀ x, v t (x + c) = v t x) (lam : ℂ) (hlam : lam ≠ 0)
    (hinit : ∀ y, θ₀ (y + c) = lam * θ₀ y) :
    ∀ t ∈ Icc 0 T, ∀ x, θ t (x + c) = lam * θ t x := by
  intro t ht x
  have hθ2 := (hθ.translate c hv).clm hT (ContinuousLinearMap.mul ℝ ℂ lam⁻¹)
  have hinit' : (fun y => ContinuousLinearMap.mul ℝ ℂ lam⁻¹ (θ₀ (y + c))) = θ₀ := by
    funext y
    rw [ContinuousLinearMap.mul_apply', hinit, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  rw [hinit'] at hθ2
  have := congrFun (complex_scalar_unique hT hν v _ _ _ hθ2 hθ t ht) x
  rw [ContinuousLinearMap.mul_apply'] at this
  rw [← this, ← mul_assoc, mul_inv_cancel₀ hlam, one_mul]

lemma intVec_nsmul (k : ℕ) (n : Fin 2 → ℤ) : intVec ((k : ℤ) • n) = (k : ℝ) • intVec n := by
  funext i; simp [intVec]

/-- The pulse drift is invariant under translations by `k_j⁻¹ ℤ²`. -/
lemma VpulseB_shift (ν : ℝ) (j : ℕ) (b : BlockParam L₀) (t : ℝ) (x : Pt 2) (n : Fin 2 → ℤ) :
    VpulseB ν j b t (x + (kk j)⁻¹ • intVec n) = VpulseB ν j b t x := by
  have hk : kk j ≠ 0 := (kk_pos' j).ne'
  simp only [VpulseB, dampedB_eq]
  have e : kk j • (x + (kk j)⁻¹ • intVec n) - b.2 = (kk j • x - b.2) + intVec n := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hk, one_smul]; abel
  rw [e, (eigenspace_properties _).2.1]

lemma expChar_smul_left (ξ x : Pt 2) (c : ℝ) : expChar ξ (c • x) = expChar (c • ξ) x := by
  unfold expChar; congr 3; simp only [dot, Pi.smul_apply, smul_eq_mul]
  congr 1; funext i; ring

/-- The rescaled pulse solution `h(s,y) = θ(δ_j s, y/k_j)` solves the cell problem of
Definition 3.6 with `μ = μ_{j,N}` and `ξ = ℓ/k_j`. -/
lemma pulse_cell_solution {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) (b : BlockParam L₀)
    (ℓ : Fin 2 → ℤ) (θ : ℝ → Pt 2 → ℂ) (hreg : IsParabolicC12 (δs j) (1 / 2) θ)
    (hθ : IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t))
      (expChar (intVec ℓ)) θ) :
    IsCellSolution (dampedB cf₀ (muJN j N) b) (muJN j N) ((kk j)⁻¹ • intVec ℓ)
      (fun s y => θ (δs j * s) ((kk j)⁻¹ • y)) := by
  have hν := viscosity_properties.2.2.1 N (hj.trans hjN)
  have hδ := δs_pos j hj
  have hk := kk_pos' j
  have hk0 : kk j ≠ 0 := hk.ne'
  have hreg1 : IsParabolicC12 (δs j * 1) (1 / 2) θ := by rw [mul_one]; exact hreg
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, δs j * s ∈ Icc 0 (δs j) := fun s hs => by
    have := mem_Icc_mul hδ hs; rwa [mul_one] at this
  refine ⟨⟨1 / 2, by norm_num, by norm_num, hreg1.rescale one_pos hδ (inv_pos.2 hk)⟩,
    ?_, ?_, ?_⟩
  · -- quasi-periodicity
    intro s hs y n
    have hq := scalar_quasi hδ hν.le _ _ θ hθ ((kk j)⁻¹ • intVec n)
      (fun t _ x => VpulseB_shift _ j b _ x n) (expChar (intVec ℓ) ((kk j)⁻¹ • intVec n))
      (Complex.exp_ne_zero _) (fun y => by rw [expChar_add_right, mul_comm]) _ (hmem s hs) ((kk j)⁻¹ • y)
    rw [smul_add, hq, expChar_smul_left]
  · -- initial datum
    funext y
    simp only [mul_zero, hθ.init]
    rw [expChar_smul_left]
  · -- the equation
    intro s hs y
    have ht := hmem s hs
    set t := δs j * s
    set x := (kk j)⁻¹ • y
    have e := hθ.eqn t ht x
    have hdt : dt 1 (fun s y => θ (δs j * s) ((kk j)⁻¹ • y)) s y = δs j • dt (δs j) θ t x := by
      have := dt_rescale (c := (kk j)⁻¹) one_pos hδ hreg1 s hs y
      rwa [mul_one] at this
    have hpd : ∀ i, pd i (fun y => θ (δs j * s) ((kk j)⁻¹ • y)) y =
        (kk j)⁻¹ • pd i (θ t) x := fun i =>
      congrFun (pd_rescale_slice (c := (kk j)⁻¹) hδ hreg1 i s hs) y
    have hpd2 : ∀ i, pd i (pd i (fun y => θ (δs j * s) ((kk j)⁻¹ • y))) y =
        ((kk j)⁻¹ * (kk j)⁻¹) • pd i (pd i (θ t)) x := fun i =>
      congrFun (pd_pd_rescale_slice (c := (kk j)⁻¹) hδ hreg1 i i s hs) y
    have hB : ∀ i, dampedB cf₀ (muJN j N) b s y i =
        kk j * δs j * VpulseB (nuN N) j b (sj j + t) x i := by
      intro i
      simp only [VpulseB, Pi.smul_apply, smul_eq_mul]
      have e1 : (sj j + t - sj j) / δs j = s := by
        simp only [t]; field_simp; ring
      have e2 : kk j • x = y := by
        simp only [x]; rw [smul_smul, mul_inv_cancel₀ hk0, one_smul]
      rw [e1, e2, show muNu (nuN N) j = muJN j N from rfl]
      field_simp
    simp only [conv, lap, Fin.sum_univ_two] at e ⊢
    rw [hdt, hpd, hpd, hpd2, hpd2, hB, hB]
    simp only [Complex.real_smul] at e ⊢
    unfold muJN
    push_cast at e ⊢
    have hk' : (kk j : ℂ) ≠ 0 := by exact_mod_cast hk0
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    linear_combination (↑(δs j) : ℂ) * e

/-- The coefficients of the rescaled pulse solution are the matrix entries of the pulse
operator: `a_n(ℓ/k_j) = ⟨T e_ℓ, e_{ℓ + k_j n}⟩`. -/
lemma pulse_cellCoeff {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) (b : BlockParam L₀)
    (ℓ : Fin 2 → ℤ) (θ : ℝ → Pt 2 → ℂ) (hreg : IsParabolicC12 (δs j) (1 / 2) θ)
    (hθ : IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t))
      (expChar (intVec ℓ)) θ) (n : Fin 2 → ℤ) :
    cellCoeff (fun s y => θ (δs j * s) ((kk j)⁻¹ • y)) ((kk j)⁻¹ • intVec ℓ) n =
      fc (θ (δs j)) (ℓ + ((qq ^ j : ℕ) : ℤ) • n) := by
  have hcell := pulse_cell_solution hj hjN b ℓ θ hreg hθ
  have hδ := δs_pos j hj
  have hk0 : kk j ≠ 0 := (kk_pos' j).ne'
  have hkq : ((qq ^ j : ℕ) : ℝ) = kk j := (kk_eq_cast j).symm
  have hθc : Continuous (θ (δs j)) := (hreg.smooth_x _ ⟨hδ.le, le_rfl⟩).continuous
  set ξ := (kk j)⁻¹ • intVec ℓ with hξ
  set F : Pt 2 → ℂ := fun y => θ (δs j * 1) ((kk j)⁻¹ • y) * expChar (-(ξ + intVec n)) y
    with hF
  set G : Pt 2 → ℂ := fun x => θ (δs j) x * expChar (-intVec (ℓ + ((qq ^ j : ℕ) : ℤ) • n)) x
    with hG
  have hFc : Continuous F := by
    simp only [hF, mul_one]
    exact (hθc.comp (continuous_const_smul _)).mul (continuous_expChar _)
  have hFp : IsPeriodic F := by
    intro y m
    have hq := hcell.quasi_periodic 1 ⟨zero_le_one, le_rfl⟩ y m
    simp only [hF]
    rw [hq, expChar_add_right]
    have h1 : expChar ξ (intVec m) * expChar (-(ξ + intVec n)) (intVec m) = 1 := by
      rw [expChar_mul, show ξ + -(ξ + intVec n) = intVec (-n) by rw [intVec_neg]; abel,
        expChar_intVec_intVec]
    calc expChar ξ (intVec m) * θ (δs j * 1) ((kk j)⁻¹ • y) *
          (expChar (-(ξ + intVec n)) y * expChar (-(ξ + intVec n)) (intVec m))
        = (expChar ξ (intVec m) * expChar (-(ξ + intVec n)) (intVec m)) *
          (θ (δs j * 1) ((kk j)⁻¹ • y) * expChar (-(ξ + intVec n)) y) := by ring
      _ = _ := by rw [h1, one_mul]
  have hFG : ∀ x, F (((qq ^ j : ℕ) : ℝ) • x) = G x := by
    intro x
    simp only [hF, hG, mul_one, hkq]
    rw [smul_smul, inv_mul_cancel₀ hk0, one_smul]
    congr 1
    rw [expChar_smul_left]
    congr 1
    rw [intVec_add', intVec_nsmul, hkq, hξ]
    funext i
    simp only [Pi.smul_apply, Pi.neg_apply, Pi.add_apply, smul_eq_mul]
    field_simp
  have h1 := integral_cell_comp_nsmul F hFc hFp (qq ^ j) (by have := qq_ge; positivity)
  simp only [hFG] at h1
  unfold cellCoeff fc
  rw [← h1]

/-- `|ĝ(m)|² ≤ ∫|g|²` for continuous periodic complex `g`. -/
lemma fc_normSq_le (g : Pt 2 → ℂ) (hc : Continuous g) (hp : IsPeriodic g) (m : Fin 2 → ℤ) :
    ‖fc g m‖ ^ 2 ≤ ∫ x in cell 2, ‖g x‖ ^ 2 := by
  have := parseval_cell_complex g hc hp
  exact (this.summable.le_tsum m (fun _ _ => sq_nonneg _)).trans_eq this.tsum_eq


lemma fc_sub (g g' : Pt 2 → ℂ) (hg : Continuous g) (hg' : Continuous g') (m : Fin 2 → ℤ) :
    fc g m - fc g' m = fc (fun x => g x - g' x) m := by
  unfold fc
  rw [← integral_sub]
  · congr 1; funext x; ring
  · exact (hg.mul (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc
  · exact (hg'.mul (continuous_expChar _)).continuousOn.integrableOn_compact isCompact_Icc

/-- The pulse matrix entries depend continuously on the block parameter. -/
lemma continuous_pulseEntry (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (ℓ m : Fin 2 → ℤ) : Continuous (fun b => pulseEntry N j b ℓ m) := by
  have hν := viscosity_properties.2.2.1 N (hj.trans hjN)
  have hδ := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hδ.le, le_rfl⟩
  choose θ hreg hθ hout using fun b : BlockParam L₀ =>
    pulseOp_spec hSc hj hjN b _ (contDiff_expChar (intVec ℓ)) (isPeriodic_expChar ℓ)
  have hcont : ∀ b, Continuous (θ b (δs j)) := fun b => ((hreg b).smooth_x _ hTmem).continuous
  have hper : ∀ b, IsPeriodic (θ b (δs j)) := fun b => (hθ b).periodic _ hTmem
  have hregV : ∀ b : BlockParam L₀, ∀ t ∈ Icc (0 : ℝ) (δs j),
      ContDiff ℝ 1 (VpulseB (nuN N) j b (sj j + t)) ∧
      IsPeriodic (VpulseB (nuN N) j b (sj j + t)) ∧
      ∀ x, divergence (VpulseB (nuN N) j b (sj j + t)) x = 0 := fun b t _ =>
    ⟨(Vpulse_slice_C2 _ (fun _ => b) j _).of_le (by norm_num),
      (vpulse_stage_props (nuN N) (fun _ => b) j).1 t,
      (vpulse_stage_props (nuN N) (fun _ => b) j).2.2 t⟩
  have hD : ∀ b : BlockParam L₀, ContinuousOn
      (fun q : ℝ × Pt 2 => VpulseB (nuN N) j b (sj j + q.1) q.2) (Icc 0 (δs j) ×ˢ univ) :=
    fun b => (vpulse_stage_props (nuN N) (fun _ => b) j).2.1.continuous.continuousOn
  have hvreg : ∀ b : BlockParam L₀, IsParabolicC01 (δs j) (1 / 2)
      (fun t => VpulseB (nuN N) j b (sj j + t)) := fun b =>
    parabolicC01_of_contDiff hδ.le (by norm_num) (by norm_num) _
      (vpulse_stage_props (nuN N) (fun _ => b) j).2.1 (vpulse_stage_props (nuN N) (fun _ => b) j).1
  set disc : BlockParam L₀ → BlockParam L₀ → ℝ := fun b b₀ => ∫ t in (0 : ℝ)..δs j,
    l2sqV (fun x => VpulseB (nuN N) j b (sj j + t) x - VpulseB (nuN N) j b₀ (sj j + t) x)
    with hdisc
  -- the stability estimate for a real part
  have key : ∀ (L : ℂ →L[ℝ] ℝ), (∀ x, |L (expChar (intVec ℓ) x)| ≤ 1) → ∀ b b₀,
      l2sq (fun x => L (θ b (δs j) x) - L (θ b₀ (δs j) x)) ≤ 1 / (2 * nuN N) * disc b b₀ := by
    intro L hL b b₀
    have h1 := (hθ b).clm hδ L
    have h2 := (hθ b₀).clm hδ L
    have hM := (scalar_energy_max (δs j) (nuN N) (1 / 2) hν _ (fun t ht => (hregV b t ht).2.1)
      (hvreg b) (fun t ht => (hregV b t ht).2.2) _ _ h1).1 1 hL
    have hS := stage_stability hδ hν _ (hD b) (hregV b) _ (hD b₀) (hregV b₀) _ _ h1 hM _ _ h2
    simp only [(hθ b).init, (hθ b₀).init, sub_self, one_pow] at hS
    have h0 : l2sq (fun _ : Pt 2 => (0 : ℝ)) = 0 := by simp [l2sq]
    rw [h0, zero_add] at hS
    exact hS
  have hre : ∀ x, |Complex.reCLM (expChar (intVec ℓ) x)| ≤ 1 := fun x =>
    (Complex.abs_re_le_norm _).trans (norm_expChar _ _).le
  have him : ∀ x, |Complex.imCLM (expChar (intVec ℓ) x)| ≤ 1 := fun x =>
    (Complex.abs_im_le_norm _).trans (norm_expChar _ _).le
  have hbound : ∀ b b₀, ‖pulseEntry N j b ℓ m - pulseEntry N j b₀ ℓ m‖ ^ 2 ≤
      2 * (1 / (2 * nuN N) * disc b b₀) := by
    intro b b₀
    simp only [pulseEntry, hout]
    rw [fc_sub _ _ (hcont b) (hcont b₀)]
    refine (fc_normSq_le _ ((hcont b).sub (hcont b₀))
      (fun x n => by simp only [Pi.sub_apply, hper b x n, hper b₀ x n]) m).trans ?_
    rw [integral_normSq_eq_re_im _ ((hcont b).sub (hcont b₀))]
    have k1 := key Complex.reCLM hre b b₀
    have k2 := key Complex.imCLM him b b₀
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at k1 k2
    simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im]
    linarith
  refine continuous_iff_continuousAt.2 fun b₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set G : BlockParam L₀ → ℝ := fun b => 2 * (1 / (2 * nuN N) * disc b b₀) with hG
  have hGc : Continuous G :=
    continuous_const.mul (continuous_const.mul (continuous_stage_discrepancy (nuN N) j b₀))
  have hG0 : G b₀ = 0 := by simp [hG, hdisc, l2sqV]
  have hlim : Tendsto (fun b => Real.sqrt (G b)) (𝓝 b₀) (𝓝 0) := by
    have := (Real.continuous_sqrt.comp hGc).tendsto b₀
    simpa [Function.comp_def, hG0] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun b => norm_nonneg _) (fun b => ?_)
  have := Real.abs_le_sqrt (hbound b b₀)
  rwa [abs_of_nonneg (norm_nonneg _)] at this


/-- The defining property of `μ_*` and `R₀` (Proposition 3.11 for the fixed parameters). -/
lemma diffusive_spec : 0 < μstar ∧ 1 ≤ R₀ ∧ ∀ R, R₀ ≤ R → ∀ μ ∈ Icc 0 μstar,
      ∀ k : ℕ, 1 ≤ k → ∀ ℓ : Fin 2 → ℤ, R * k ≤ euclNorm (intVec ℓ) →
      ∀ h : BlockParam L₀ → ℝ → Pt 2 → ℂ,
        (∀ w, IsCellSolution (dampedB cf₀ μ w) μ ((k : ℝ)⁻¹ • intVec ℓ) (h w)) →
        ∫ w, ∑' m, weightW σ₀ R ((qq : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec m) *
            ‖cellCoeff (h w) ((k : ℝ)⁻¹ • intVec ℓ) m‖ ^ 2 ∂(blockMeasure L₀)
          ≤ weightW σ₀ R k (intVec ℓ) / 2 :=
  Classical.choose_spec
    (Classical.choose_spec (diffusive_fourier qq qq_ge σ₀ σ₀_pos σ₀_lt_one L₀ negMoment₀ cf₀))

lemma intVec_zsmul_pow (j : ℕ) (n : Fin 2 → ℤ) :
    intVec (((qq : ℤ) ^ j) • n) = kk j • intVec n := by
  funext i; simp [intVec, kk]

/-- **Lemma 7.5 (3)**: the weighted drift inequality for the averaged kernels. -/
theorem kernel_drift (hSc : ExternalScalar) :
    ∃ N' : ℕ, ∀ R, R₀ ≤ R → ∀ N, N' ≤ N → ∀ j, 1 ≤ j → j ≤ N → ∀ ℓ : Fin 2 → ℤ,
      R * kk j ≤ euclNorm (intVec ℓ) →
      ∑' m, weightW σ₀ R (kk (j + 1)) (intVec m) * kernelK N j ℓ m
        ≤ weightW σ₀ R (kk j) (intVec ℓ) / 2 := by
  obtain ⟨hμ, hR₀, hspec⟩ := diffusive_spec
  obtain ⟨N₀, hN₀⟩ := viscosity_properties.2.2.2.2.2.2 μstar hμ
  refine ⟨max N₀ 1, fun R hR N hN j hj hjN ℓ hℓ => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hν := viscosity_properties.2.2.1 N hN1
  have hR0 : 0 ≤ R := le_trans (by linarith) hR
  set k : ℕ := qq ^ j with hkdef
  have hk1 : 1 ≤ k := Nat.one_le_pow _ _ (by have := qq_ge; omega)
  have hkk : (k : ℝ) = kk j := (kk_eq_cast j).symm
  have hμmem : muJN j N ∈ Icc 0 μstar :=
    ⟨by unfold muJN; have := δs_pos j hj; have := kk_pos' j; positivity,
      hN₀ N (le_trans (le_max_left _ _) hN) j hj hjN⟩
  choose θ hreg hθ hout using fun b : BlockParam L₀ =>
    pulseOp_spec hSc hj hjN b _ (contDiff_expChar (intVec ℓ)) (isPeriodic_expChar ℓ)
  set h : BlockParam L₀ → ℝ → Pt 2 → ℂ := fun b s y => θ b (δs j * s) ((kk j)⁻¹ • y) with hh
  have hcell : ∀ b, IsCellSolution (dampedB cf₀ (muJN j N) b) (muJN j N)
      ((k : ℝ)⁻¹ • intVec ℓ) (h b) := fun b => by
    rw [hkk]; exact pulse_cell_solution hj hjN b ℓ (θ b) (hreg b) (hθ b)
  have hmain := hspec R hR _ hμmem k hk1 ℓ (by rw [hkk]; exact hℓ) h hcell
  -- the coefficients are the pulse entries
  set g : (Fin 2 → ℤ) → Fin 2 → ℤ := fun n => ℓ + ((qq : ℤ) ^ j) • n with hg
  have hcoef : ∀ b n, cellCoeff (h b) ((k : ℝ)⁻¹ • intVec ℓ) n = pulseEntry N j b ℓ (g n) := by
    intro b n
    rw [hkk, pulse_cellCoeff hj hjN b ℓ (θ b) (hreg b) (hθ b) n, pulseEntry, hout b]
    simp [hg]
  have hW : ∀ n, weightW σ₀ R ((qq : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) =
      weightW σ₀ R (kk (j + 1)) (intVec (g n)) := by
    intro n
    rw [hkk, hg, intVec_add', intVec_zsmul_pow]
    congr 1
    simp [kk, pow_succ]; ring
  simp only [hcoef, hW] at hmain
  -- reindex the sum over the residue class of `ℓ`
  have hginj : Function.Injective g := by
    intro n n' hn
    have hq0 : ((qq : ℤ) ^ j) ≠ 0 := pow_ne_zero _ (by have := qq_ge; omega)
    have := add_left_cancel hn
    funext i
    have hi := congrFun this i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hq0 hi
  have hsupp : Function.support
      (fun m => weightW σ₀ R (kk (j + 1)) (intVec m) * kernelK N j ℓ m) ⊆ Set.range g := by
    intro m hm
    by_contra hnot
    apply hm
    have hres : ¬ ∃ n : Fin 2 → ℤ, m - ℓ = (qq ^ j : ℤ) • n := by
      rintro ⟨n, hn⟩
      exact hnot ⟨n, by simp only [hg]; rw [← hn]; abel⟩
    have : kernelK N j ℓ m = 0 := by
      unfold kernelK
      simp [residue_classes hSc N j hj hjN _ ℓ m hres]
    simp [this]
  rw [← hginj.tsum_eq hsupp]
  -- interchange the sum and the expectation
  set f : (Fin 2 → ℤ) → BlockParam L₀ → ℝ := fun n b =>
    weightW σ₀ R (kk (j + 1)) (intVec (g n)) * ‖pulseEntry N j b ℓ (g n)‖ ^ 2 with hf
  have hWnn : ∀ n, 0 ≤ weightW σ₀ R (kk (j + 1)) (intVec (g n)) := fun n =>
    weightW_nonneg (mul_nonneg hR0 (kk_pos' _).le) _
  have hWle : ∀ n, weightW σ₀ R (kk (j + 1)) (intVec (g n)) ≤ 1 := fun n => weightW_le_one _ _ _ _
  have hfm : ∀ n, Measurable (f n) := fun n =>
    measurable_const.mul ((continuous_pulseEntry hSc hj hjN ℓ (g n)).measurable.norm.pow_const 2)
  have hfle : ∀ n b, ‖f n b‖ ≤ ‖pulseEntry N j b ℓ (g n)‖ ^ 2 := by
    intro n b
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hWnn n) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (hWle n)
  have hfint : ∀ n, Integrable (f n) (blockMeasure L₀) := by
    intro n
    refine Integrable.of_bound (hfm n).aestronglyMeasurable 1 (Eventually.of_forall fun b => ?_)
    refine (hfle n b).trans ?_
    obtain ⟨hs, hle⟩ := pulseEntry_hasSum_le hSc hj hjN b ℓ
    exact (hs.le_tsum (g n) (fun _ _ => sq_nonneg _)).trans hle
  have hKs : Summable fun n => kernelK N j ℓ (g n) :=
    (kernel_substochastic hSc N j hj hjN ℓ).1.comp_injective hginj
  have hsum : Summable fun n => ∫ b, ‖f n b‖ ∂(blockMeasure L₀) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) hKs
    exact integral_mono (hfint n).norm
      ((continuous_pulseEntry hSc hj hjN ℓ (g n)).norm.pow 2 |>.measurable.aestronglyMeasurable
        |> fun hm => Integrable.of_bound hm 1 (Eventually.of_forall fun b => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          obtain ⟨hs, hle⟩ := pulseEntry_hasSum_le hSc hj hjN b ℓ
          exact (hs.le_tsum (g n) (fun _ _ => sq_nonneg _)).trans hle))
      (hfle n)
  have hswap := integral_tsum_of_summable_integral_norm hfint hsum
  have hterm : ∀ n, ∫ b, f n b ∂(blockMeasure L₀) =
      weightW σ₀ R (kk (j + 1)) (intVec (g n)) * kernelK N j ℓ (g n) := by
    intro n; simp only [hf, kernelK]; rw [integral_const_mul]
  simp only [hterm] at hswap
  rw [hswap]
  rw [hkk] at hmain
  exact hmain

end AnomDiss
