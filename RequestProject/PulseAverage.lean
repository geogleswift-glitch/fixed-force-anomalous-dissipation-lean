module

public import RequestProject.KernelDrift

/-!
# Phase averaging across a pulse interval (Lemma 7.3)

Translating a block by its global phase conjugates the pulse operator; averaging over the phase
removes the cross terms between distinct input frequencies, which gives
`𝔼_b |(T_b h)^(m)|² = ∑_ℓ K_{j,N}(ℓ,m) |ĥ(ℓ)|²`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff ComplexConjugate

noncomputable section

namespace AnomDiss

/-- Translating a classical solution in space translates its drift. -/
lemma IsClassicalScalar.translate_drift {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T ν : ℝ} {v : ℝ → Pt d → Pt d} {θ₀ : Pt d → E} {θ : ℝ → Pt d → E}
    (h : IsClassicalScalar T ν v θ₀ θ) (c : Pt d) :
    IsClassicalScalar T ν (fun t x => v t (x + c)) (fun x => θ₀ (x + c))
      (fun t x => θ t (x + c)) := by
  obtain ⟨β, hβ0, hβ1, reg⟩ := h.regular
  refine ⟨fun t ht x n => by simp only [add_right_comm x _ c, h.periodic t ht (x + c) n],
    ⟨β, hβ0, hβ1, reg.translate c⟩, by simp only [h.init], fun t ht x => ?_⟩
  have e := h.eqn t ht (x + c)
  show dt T θ t (x + c) + conv (fun y => v t (y + c)) (fun y => θ t (y + c)) x =
    ν • lap (fun y => θ t (y + c)) x
  simp only [conv, lap, pd_translate] at e ⊢
  exact e

lemma expChar_neg_eq_conj (ξ x : Pt 2) : expChar (-ξ) x = conj (expChar ξ x) := by
  unfold expChar
  rw [← Complex.exp_conj]
  congr 1
  simp only [dot, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Pi.neg_apply,
    neg_mul, Finset.sum_neg_distrib]
  push_cast; ring

lemma expChar_neg_left (ξ x : Pt 2) : expChar ξ (-x) = (expChar ξ x)⁻¹ := by
  unfold expChar
  rw [← Complex.exp_neg]
  congr 1
  simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  push_cast; ring

/-- The pulse drift of a block with global phase `z` is the translate by `z/k_j` of the drift
with phase `0`. -/
lemma VpulseB_phase (ν : ℝ) (j : ℕ) (b₁ : Fin L₀ → Bool × Pt 2) (z : Pt 2) (t : ℝ) (x : Pt 2) :
    VpulseB ν j (b₁, z) t x = VpulseB ν j (b₁, 0) t (x + -((kk j)⁻¹ • z)) := by
  have hk : kk j ≠ 0 := (kk_pos' j).ne'
  simp only [VpulseB, dampedB_eq]
  congr 2
  simp only [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hk, one_smul, sub_eq_add_neg,
    neg_zero, add_zero]

/-- Translation structure of the pulse matrix entries:
`⟨T^{(b₁,z)} e_ℓ, e_m⟩ = e^{2πi(ℓ-m)·z/k_j} ⟨T^{(b₁,0)} e_ℓ, e_m⟩`. -/
lemma pulseEntry_phase (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (b₁ : Fin L₀ → Bool × Pt 2) (z : Pt 2) (ℓ m : Fin 2 → ℤ) :
    pulseEntry N j (b₁, z) ℓ m =
      expChar (intVec ℓ - intVec m) ((kk j)⁻¹ • z) * pulseEntry N j (b₁, 0) ℓ m := by
  have hν := viscosity_properties.2.2.1 N (hj.trans hjN)
  have hδ := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hδ.le, le_rfl⟩
  obtain ⟨θ, hreg, hθ, hout⟩ :=
    pulseOp_spec hSc hj hjN (b₁, z) _ (contDiff_expChar (intVec ℓ)) (isPeriodic_expChar ℓ)
  obtain ⟨θ₀, hreg₀, hθ₀, hout₀⟩ :=
    pulseOp_spec hSc hj hjN (b₁, 0) _ (contDiff_expChar (intVec ℓ)) (isPeriodic_expChar ℓ)
  set c : Pt 2 := -((kk j)⁻¹ • z) with hc
  set lam : ℂ := expChar (intVec ℓ) c with hlam
  have hlam0 : lam ≠ 0 := Complex.exp_ne_zero _
  -- the translated solution
  have h1 := (hθ₀.translate_drift c).clm hδ (ContinuousLinearMap.mul ℝ ℂ lam⁻¹)
  have hinit : (fun x => ContinuousLinearMap.mul ℝ ℂ lam⁻¹ (expChar (intVec ℓ) (x + c))) =
      expChar (intVec ℓ) := by
    funext x
    rw [ContinuousLinearMap.mul_apply', expChar_add_right, ← hlam]
    field_simp
  have hdrift : (fun t x => VpulseB (nuN N) j (b₁, 0) (sj j + t) (x + c)) =
      fun t => VpulseB (nuN N) j (b₁, z) (sj j + t) := by
    funext t x; exact (VpulseB_phase _ _ _ _ _ _).symm
  rw [hinit, hdrift] at h1
  have huniq := congrFun (complex_scalar_unique hδ hν.le _ _ _ _ hθ h1 _ hTmem)
  simp only [ContinuousLinearMap.mul_apply'] at huniq
  -- Fourier coefficients
  unfold pulseEntry
  rw [hout, hout₀]
  have hθ₀c : Continuous (θ₀ (δs j)) := (hreg₀.smooth_x _ hTmem).continuous
  have hθ₀p : IsPeriodic (θ₀ (δs j)) := hθ₀.periodic _ hTmem
  set G : Pt 2 → ℂ := fun y => θ₀ (δs j) y * expChar (-intVec m) (y - c) with hG
  have hGc : Continuous G := hθ₀c.mul ((continuous_expChar _).comp (continuous_sub_right c))
  have hGp : IsPeriodic G := fun y n => by
    simp only [hG, hθ₀p y n, add_sub_right_comm, ← intVec_neg, expChar_add_right,
      expChar_intVec_intVec, mul_one]
  have hI := integral_cell_add_right G hGc hGp c
  unfold fc
  simp only [huniq]
  have e1 : ∀ x, lam⁻¹ * θ₀ (δs j) (x + c) * expChar (-intVec m) x = lam⁻¹ * G (x + c) := by
    intro x; simp only [hG, add_sub_cancel_right]; ring
  simp only [e1]
  rw [integral_const_mul, hI]
  have e2 : ∀ y, G y = expChar (-intVec m) (-c) * (θ₀ (δs j) y * expChar (-intVec m) y) := by
    intro y
    simp only [hG, sub_eq_add_neg, expChar_add_right]; ring
  simp only [e2]
  rw [integral_const_mul, ← mul_assoc]
  congr 1
  rw [hlam, ← expChar_neg_left, expChar_mul, hc, neg_neg, sub_eq_add_neg]

lemma norm_pulseEntry_le (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (b : BlockParam L₀) (ℓ m : Fin 2 → ℤ) : ‖pulseEntry N j b ℓ m‖ ≤ 1 := by
  obtain ⟨hs, hle⟩ := pulseEntry_hasSum_le hSc hj hjN b ℓ
  have h1 := (hs.le_tsum m (fun _ _ => sq_nonneg _)).trans hle
  nlinarith [norm_nonneg (pulseEntry N j b ℓ m)]

/-- Orthogonality of distinct input frequencies after phase averaging (Lemma 7.3). -/
lemma pulseEntry_orth (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (ℓ ℓ' m : Fin 2 → ℤ) (hne : ℓ ≠ ℓ') :
    ∫ b, pulseEntry N j b ℓ m * conj (pulseEntry N j b ℓ' m) ∂(blockMeasure L₀) = 0 := by
  have hc : Continuous fun b : BlockParam L₀ =>
      pulseEntry N j b ℓ m * conj (pulseEntry N j b ℓ' m) :=
    (continuous_pulseEntry hSc hj hjN ℓ m).mul
      (Complex.continuous_conj.comp (continuous_pulseEntry hSc hj hjN ℓ' m))
  have hint : Integrable (fun b : BlockParam L₀ =>
      pulseEntry N j b ℓ m * conj (pulseEntry N j b ℓ' m)) (blockMeasure L₀) := by
    refine Integrable.of_bound hc.aestronglyMeasurable 1 (Eventually.of_forall fun b => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (norm_pulseEntry_le hSc hj hjN b ℓ m) (norm_nonneg _)
      (norm_pulseEntry_le hSc hj hjN b ℓ' m)
  unfold blockMeasure at hint ⊢
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun b₁ => ?_)
  simp only [Pi.zero_apply]
  set A := pulseEntry N j (b₁, 0) ℓ m
  set A' := pulseEntry N j (b₁, 0) ℓ' m
  have e : ∀ z : Pt 2, pulseEntry N j (b₁, z) ℓ m * conj (pulseEntry N j (b₁, z) ℓ' m) =
      A * conj A' * expChar (intVec ℓ - intVec ℓ') ((kk j)⁻¹ • z) := by
    intro z
    rw [pulseEntry_phase hSc hj hjN b₁ z ℓ m, pulseEntry_phase hSc hj hjN b₁ z ℓ' m, map_mul,
      ← expChar_neg_eq_conj]
    have : expChar (intVec ℓ - intVec m) ((kk j)⁻¹ • z) *
        expChar (-(intVec ℓ' - intVec m)) ((kk j)⁻¹ • z) =
        expChar (intVec ℓ - intVec ℓ') ((kk j)⁻¹ • z) := by
      rw [expChar_mul]; congr 1; abel
    rw [← this]; ring
  simp only [e]
  rw [integral_const_mul]
  by_cases hA : A = 0
  · simp [hA]
  by_cases hA' : A' = 0
  · simp [hA']
  obtain ⟨n, hn⟩ : ∃ n : Fin 2 → ℤ, m - ℓ = (qq ^ j : ℤ) • n := by
    by_contra h; exact hA (residue_classes hSc N j hj hjN _ ℓ m h)
  obtain ⟨n', hn'⟩ : ∃ n : Fin 2 → ℤ, m - ℓ' = (qq ^ j : ℤ) • n := by
    by_contra h; exact hA' (residue_classes hSc N j hj hjN _ ℓ' m h)
  have hdiff : intVec ℓ - intVec ℓ' = kk j • intVec (n' - n) := by
    have : ℓ - ℓ' = ((qq : ℤ) ^ j) • (n' - n) := by
      rw [smul_sub, ← hn, ← hn']; abel
    rw [← intVec_zsmul_pow, ← this]
    funext i; simp [intVec]
  have hk : kk j ≠ 0 := (kk_pos' j).ne'
  have e2 : ∀ z : Pt 2, expChar (intVec ℓ - intVec ℓ') ((kk j)⁻¹ • z) =
      expChar (intVec (n' - n)) z := by
    intro z
    rw [expChar_smul_left, hdiff, smul_smul, inv_mul_cancel₀ hk, one_smul]
  simp only [e2]
  have hne' : n' - n ≠ 0 := by
    intro h0
    apply hne
    have : n' = n := sub_eq_zero.1 h0
    have h1 : ℓ = m - (qq ^ j : ℤ) • n := by rw [← hn]; abel
    have h2 : ℓ' = m - (qq ^ j : ℤ) • n' := by rw [← hn']; abel
    rw [h1, h2, this]
  have := integral_cell_expChar (n' - n)
  rw [if_neg hne'] at this
  rw [show uniformTorus = volume.restrict (cell 2) from rfl, this, mul_zero]

lemma integrable_pulseEntry_mul (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (ℓ ℓ' m : Fin 2 → ℤ) (a : ℂ) :
    Integrable (fun b => a * (pulseEntry N j b ℓ m * conj (pulseEntry N j b ℓ' m)))
      (blockMeasure L₀) := by
  have hc : Continuous fun b : BlockParam L₀ =>
      a * (pulseEntry N j b ℓ m * conj (pulseEntry N j b ℓ' m)) :=
    continuous_const.mul ((continuous_pulseEntry hSc hj hjN ℓ m).mul
      (Complex.continuous_conj.comp (continuous_pulseEntry hSc hj hjN ℓ' m)))
  refine Integrable.of_bound hc.aestronglyMeasurable ‖a‖ (Eventually.of_forall fun b => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h1 := norm_pulseEntry_le hSc hj hjN b ℓ m
  have h2 := norm_pulseEntry_le hSc hj hjN b ℓ' m
  have : ‖pulseEntry N j b ℓ m‖ * ‖pulseEntry N j b ℓ' m‖ ≤ 1 :=
    mul_le_one₀ h1 (norm_nonneg _) h2
  nlinarith [norm_nonneg a, norm_nonneg (pulseEntry N j b ℓ m), norm_nonneg (pulseEntry N j b ℓ' m)]

/-- Phase averaging of finite combinations: `𝔼_b |∑_{ℓ∈S} c_ℓ ⟨T_b e_ℓ, e_m⟩|² =
∑_{ℓ∈S} |c_ℓ|² K_{j,N}(ℓ,m)`. -/
lemma pulse_finite_average (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (S : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ) (m : Fin 2 → ℤ) :
    ∫ b, ‖∑ ℓ ∈ S, c ℓ * pulseEntry N j b ℓ m‖ ^ 2 ∂(blockMeasure L₀) =
      ∑ ℓ ∈ S, ‖c ℓ‖ ^ 2 * kernelK N j ℓ m := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hsq, map_sum, map_mul, Finset.sum_mul_sum]
  have e : ∀ b, ∑ ℓ ∈ S, ∑ ℓ' ∈ S, c ℓ * pulseEntry N j b ℓ m *
      (conj (c ℓ') * conj (pulseEntry N j b ℓ' m)) =
      ∑ ℓ ∈ S, ∑ ℓ' ∈ S, (c ℓ * conj (c ℓ')) *
        (pulseEntry N j b ℓ m * conj (pulseEntry N j b ℓ' m)) := fun b => by
    congr 1; funext ℓ; congr 1; funext ℓ'; ring
  simp only [e]
  rw [integral_finset_sum _ (fun ℓ _ => integrable_finset_sum _ (fun ℓ' _ =>
    integrable_pulseEntry_mul hSc hj hjN ℓ ℓ' m _))]
  push_cast
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [integral_finset_sum _ (fun ℓ' _ => integrable_pulseEntry_mul hSc hj hjN ℓ ℓ' m _)]
  rw [Finset.sum_eq_single ℓ]
  · rw [integral_const_mul]
    have hK : ∫ b, pulseEntry N j b ℓ m * conj (pulseEntry N j b ℓ m) ∂(blockMeasure L₀) =
        (kernelK N j ℓ m : ℂ) := by
      unfold kernelK
      rw [← integral_complex_ofReal]
      simp only [hsq]
    rw [hK, ← hsq]; push_cast; ring
  · intro ℓ' _ hne
    rw [integral_const_mul, pulseEntry_orth hSc hj hjN ℓ ℓ' m (Ne.symm hne), mul_zero]
  · intro h; exact absurd hℓ h

/-- `L²` stability across a pulse interval: two complex classical solutions with the same pulse
drift satisfy `‖θ(δ_j) - φ(δ_j)‖₂ ≤ ‖θ(0) - φ(0)‖₂`. -/
lemma pulse_pair_l2 {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) (b : BlockParam L₀)
    (θ₀ φ₀ : Pt 2 → ℂ) (θ φ : ℝ → Pt 2 → ℂ)
    (hθ : IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t)) θ₀ θ)
    (hφ : IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t)) φ₀ φ)
    (hθ₀ : Continuous θ₀) (hφ₀ : Continuous φ₀) :
    ∫ x in cell 2, ‖θ (δs j) x - φ (δs j) x‖ ^ 2 ≤ ∫ x in cell 2, ‖θ₀ x - φ₀ x‖ ^ 2 := by
  have hν := viscosity_properties.2.2.1 N (hj.trans hjN)
  have hδ := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hδ.le, le_rfl⟩
  have hregV : ∀ t ∈ Icc (0 : ℝ) (δs j),
      ContDiff ℝ 1 (VpulseB (nuN N) j b (sj j + t)) ∧
      IsPeriodic (VpulseB (nuN N) j b (sj j + t)) ∧
      ∀ x, divergence (VpulseB (nuN N) j b (sj j + t)) x = 0 := fun t _ =>
    ⟨(Vpulse_slice_C2 _ (fun _ => b) j _).of_le (by norm_num),
      (vpulse_stage_props (nuN N) (fun _ => b) j).1 t,
      (vpulse_stage_props (nuN N) (fun _ => b) j).2.2 t⟩
  have hD : ContinuousOn
      (fun q : ℝ × Pt 2 => VpulseB (nuN N) j b (sj j + q.1) q.2) (Icc 0 (δs j) ×ˢ univ) :=
    (vpulse_stage_props (nuN N) (fun _ => b) j).2.1.continuous.continuousOn
  have key : ∀ L : ℂ →L[ℝ] ℝ, l2sq (fun x => L (θ (δs j) x) - L (φ (δs j) x)) ≤
      l2sq (fun x => L (θ₀ x) - L (φ₀ x)) := by
    intro L
    have h1 := hθ.clm hδ L
    have h2 := hφ.clm hδ L
    obtain ⟨β, -, -, reg⟩ := h1.regular
    obtain ⟨M, hM⟩ := reg.bdd
    have hM' : ∀ t ∈ Icc 0 (δs j), ∀ x, |L (θ t x)| ≤ M := fun t ht x => by
      have := hM t ht x; rwa [Real.norm_eq_abs] at this
    have hS := stage_stability hδ hν _ hD hregV _ hD hregV _ _ h1 hM' _ _ h2
    simp only [sub_self, hθ.init, hφ.init] at hS
    have h0 : l2sqV (fun _ : Pt 2 => (0 : Pt 2)) = 0 := by simp [l2sqV]
    simp only [h0, intervalIntegral.integral_const, smul_zero, mul_zero, add_zero] at hS
    exact hS
  have hθc : Continuous (θ (δs j)) := by
    obtain ⟨β, -, -, reg⟩ := hθ.regular; exact (reg.smooth_x _ hTmem).continuous
  have hφc : Continuous (φ (δs j)) := by
    obtain ⟨β, -, -, reg⟩ := hφ.regular; exact (reg.smooth_x _ hTmem).continuous
  rw [integral_normSq_eq_re_im (fun x => θ (δs j) x - φ (δs j) x) (hθc.fun_sub hφc),
    integral_normSq_eq_re_im (fun x => θ₀ x - φ₀ x) (hθ₀.fun_sub hφ₀)]
  have k1 := key Complex.reCLM
  have k2 := key Complex.imCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at k1 k2
  simp only [Complex.sub_re, Complex.sub_im]
  linarith

/-- Finite linear combinations of the pulse solutions of the characters. -/
lemma pulse_lincomb (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (b : BlockParam L₀) (S : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ) :
    ∃ Sg : ℝ → Pt 2 → ℂ, IsParabolicC12 (δs j) (1 / 2) Sg ∧
      IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t))
        (fun x => ∑ ℓ ∈ S, c ℓ * expChar (intVec ℓ) x) Sg ∧
      Sg (δs j) = fun x => ∑ ℓ ∈ S, c ℓ * pulseOp N j b (expChar (intVec ℓ)) x := by
  classical
  have hδ := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hδ.le, le_rfl⟩
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨θ, hreg, hθ, -⟩ :=
      pulseOp_spec hSc hj hjN b _ (contDiff_expChar (intVec 0)) (isPeriodic_expChar 0)
    have h0 := hθ.clm hδ (0 : ℂ →L[ℝ] ℂ)
    refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · have := hreg.clm hδ (0 : ℂ →L[ℝ] ℂ)
      simpa using this
    · simpa using h0
    · funext x; simp
  | insert ℓ S hℓ ih =>
    obtain ⟨Sg, hreg, hSg, hout⟩ := ih
    obtain ⟨θ, hregθ, hθ, houtθ⟩ :=
      pulseOp_spec hSc hj hjN b _ (contDiff_expChar (intVec ℓ)) (isPeriodic_expChar ℓ)
    have h1 := hθ.clm hδ (ContinuousLinearMap.mul ℝ ℂ (c ℓ))
    have hr1 := hregθ.clm hδ (ContinuousLinearMap.mul ℝ ℂ (c ℓ))
    have h2 := h1.add hδ (by norm_num : (0:ℝ) < 1 / 2) (by norm_num) hSg hr1 hreg
    refine ⟨_, hr1.add hδ hreg, ?_, ?_⟩
    · simpa [Finset.sum_insert hℓ] using h2
    · funext x
      simp only [Finset.sum_insert hℓ, ContinuousLinearMap.mul_apply', houtθ, hout]

lemma fc_finset_sum (S : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ)
    (g : (Fin 2 → ℤ) → Pt 2 → ℂ) (hg : ∀ ℓ, Continuous (g ℓ)) (m : Fin 2 → ℤ) :
    fc (fun x => ∑ ℓ ∈ S, c ℓ * g ℓ x) m = ∑ ℓ ∈ S, c ℓ * fc (g ℓ) m := by
  unfold fc
  simp only [Finset.sum_mul]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← integral_const_mul]; congr 1; funext x; ring
  · intro ℓ _
    exact ((continuous_const.mul (hg ℓ)).mul (continuous_expChar _)).continuousOn.integrableOn_compact
      isCompact_Icc

lemma fc_expChar (ℓ n : Fin 2 → ℤ) : fc (expChar (intVec ℓ)) n = if ℓ = n then 1 else 0 := by
  unfold fc
  have e : ∀ x, expChar (intVec ℓ) x * expChar (-intVec n) x = expChar (intVec (ℓ - n)) x := by
    intro x
    rw [expChar_mul, sub_eq_add_neg, intVec_add', intVec_neg]
  simp only [e, integral_cell_expChar, sub_eq_zero]

lemma fc_lincomb_expChar (S : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ) (n : Fin 2 → ℤ) :
    fc (fun x => ∑ ℓ ∈ S, c ℓ * expChar (intVec ℓ) x) n = if n ∈ S then c n else 0 := by
  classical
  rw [fc_finset_sum S c _ (fun ℓ => continuous_expChar _)]
  simp only [fc_expChar, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

/-- Bessel's identity for a Fourier truncation. -/
lemma bessel_truncation (g : Pt 2 → ℂ) (hc : Continuous g) (hp : IsPeriodic g)
    (S : Finset (Fin 2 → ℤ)) :
    ∫ x in cell 2, ‖g x - ∑ ℓ ∈ S, fc g ℓ * expChar (intVec ℓ) x‖ ^ 2 =
      (∫ x in cell 2, ‖g x‖ ^ 2) - ∑ ℓ ∈ S, ‖fc g ℓ‖ ^ 2 := by
  classical
  have hsc : Continuous fun x => ∑ ℓ ∈ S, fc g ℓ * expChar (intVec ℓ) x :=
    continuous_finset_sum _ fun ℓ _ => continuous_const.mul (continuous_expChar _)
  have hsp : IsPeriodic fun x => ∑ ℓ ∈ S, fc g ℓ * expChar (intVec ℓ) x := fun x n => by
    simp only [isPeriodic_expChar _ x n]
  have h1 := parseval_cell_complex (fun x => g x - ∑ ℓ ∈ S, fc g ℓ * expChar (intVec ℓ) x)
    (hc.fun_sub hsc) (fun x n => by simp only [hp x n, hsp x n])
  have h2 := parseval_cell_complex g hc hp
  have h3 : HasSum (fun n => if n ∈ S then ‖fc g n‖ ^ 2 else 0) (∑ ℓ ∈ S, ‖fc g ℓ‖ ^ 2) := by
    have := hasSum_sum_of_ne_finset_zero (f := fun n => if n ∈ S then ‖fc g n‖ ^ 2 else 0)
      (s := S) (L := SummationFilter.unconditional _) (fun n hn => if_neg hn)
    simpa [Finset.sum_ite_mem] using this
  refine h1.unique ?_
  convert h2.sub h3 using 1
  funext n
  rw [← fc_sub _ _ hc hsc, fc_lincomb_expChar]
  split_ifs <;> simp

/-- Truncation estimate across the pulse interval:
`|φ_b(δ_j)^(m) - ∑_{ℓ∈S} ĥ(ℓ) ⟨T_b e_ℓ, e_m⟩|² ≤ ‖h‖₂² - ∑_{ℓ∈S} |ĥ(ℓ)|²`. -/
lemma pulse_truncation (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (h : Pt 2 → ℝ) (hc : Continuous h) (hp : IsPeriodic h) (b : BlockParam L₀)
    (φ : ℝ → Pt 2 → ℝ)
    (hφ : IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t)) h φ)
    (S : Finset (Fin 2 → ℤ)) (m : Fin 2 → ℤ) :
    ‖fc (fun x => (φ (δs j) x : ℂ)) m -
        ∑ ℓ ∈ S, fc (fun x => (h x : ℂ)) ℓ * pulseEntry N j b ℓ m‖ ^ 2 ≤
      (∫ x in cell 2, ‖(h x : ℂ)‖ ^ 2) - ∑ ℓ ∈ S, ‖fc (fun x => (h x : ℂ)) ℓ‖ ^ 2 := by
  have hδ := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hδ.le, le_rfl⟩
  set g : Pt 2 → ℂ := fun x => (h x : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp hc
  have hgp : IsPeriodic g := fun x n => by simp only [hg, hp x n]
  have hΦ := hφ.clm hδ Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hΦ
  obtain ⟨Sg, hSreg, hSg, hout⟩ := pulse_lincomb hSc hj hjN b S (fc g)
  have hpair := pulse_pair_l2 hj hjN b _ _ _ _ hΦ hSg hgc
    (continuous_finset_sum _ fun ℓ _ => continuous_const.mul (continuous_expChar _))
  have hΦc : Continuous fun x => (φ (δs j) x : ℂ) := by
    obtain ⟨β, -, -, reg⟩ := hΦ.regular; exact (reg.smooth_x _ hTmem).continuous
  have hΦp : IsPeriodic fun x => (φ (δs j) x : ℂ) := hΦ.periodic _ hTmem
  have hSc' : Continuous (Sg (δs j)) := (hSreg.smooth_x _ hTmem).continuous
  have hSp : IsPeriodic (Sg (δs j)) := hSg.periodic _ hTmem
  have hX : ∑ ℓ ∈ S, fc g ℓ * pulseEntry N j b ℓ m = fc (Sg (δs j)) m := by
    rw [hout, fc_finset_sum S (fc g) _ (fun ℓ => ?_)]
    · rfl
    · exact (pulseOp_l2_le hSc hj hjN b _ (contDiff_expChar (intVec ℓ))
        (isPeriodic_expChar ℓ)).1
  rw [hX, fc_sub _ _ hΦc hSc', ← bessel_truncation g hgc hgp S]
  exact (fc_normSq_le (fun x => (φ (δs j) x : ℂ) - Sg (δs j) x) (hΦc.fun_sub hSc')
    (fun x n => by simp only [hΦp x n, hSp x n]) m).trans hpair

lemma sq_sub_sq_le_aux {a x d s r : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hd : 0 ≤ d)
    (hax : |x - a| ≤ d) (hds : d ≤ s) (har : a ≤ r) : |x ^ 2 - a ^ 2| ≤ s * (2 * r + s) := by
  have h1 : x ≤ a + d := by linarith [(abs_le.1 hax).2]
  have h2 : |x ^ 2 - a ^ 2| = |x - a| * (x + a) := by
    rw [show x ^ 2 - a ^ 2 = (x - a) * (x + a) by ring, abs_mul,
      abs_of_nonneg (show 0 ≤ x + a by linarith)]
  rw [h2]
  calc |x - a| * (x + a) ≤ d * (2 * a + d) := by
        apply mul_le_mul hax (by linarith) (by linarith) hd
    _ ≤ s * (2 * r + s) := by
        apply mul_le_mul hds (by linarith) (by linarith) (by linarith)

/-- **Lemma 7.3 + Parseval** (phase averaging across a pulse interval): for continuous periodic
real `h` and solutions `φ_b` across `I_j` started from `h`,
`𝔼_b |φ_b(δ_j)^(m)|² = ∑_ℓ K_{j,N}(ℓ,m) |ĥ(ℓ)|²` (as an unconditional sum). -/
lemma pulse_average_hasSum (hSc : ExternalScalar) {N j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (h : Pt 2 → ℝ) (hc : Continuous h) (hp : IsPeriodic h)
    (φ : BlockParam L₀ → ℝ → Pt 2 → ℝ)
    (hφ : ∀ b, IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t)) h (φ b))
    (m : Fin 2 → ℤ) :
    HasSum (fun ℓ => kernelK N j ℓ m * ‖fc (fun x => (h x : ℂ)) ℓ‖ ^ 2)
      (∫ b, ‖fc (fun x => (φ b (δs j) x : ℂ)) m‖ ^ 2 ∂(blockMeasure L₀)) := by
  classical
  set g : Pt 2 → ℂ := fun x => (h x : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp hc
  have hgp : IsPeriodic g := fun x n => by simp only [hg, hp x n]
  set c := fc g with hcdef
  set H := ∫ x in cell 2, ‖g x‖ ^ 2 with hH
  have hpar : HasSum (fun ℓ => ‖c ℓ‖ ^ 2) H := parseval_cell_complex g hgc hgp
  set Y : BlockParam L₀ → ℂ := fun b => fc (fun x => (φ b (δs j) x : ℂ)) m with hY
  set X : Finset (Fin 2 → ℤ) → BlockParam L₀ → ℂ :=
    fun S b => ∑ ℓ ∈ S, c ℓ * pulseEntry N j b ℓ m with hX
  set ε : Finset (Fin 2 → ℤ) → ℝ := fun S => H - ∑ ℓ ∈ S, ‖c ℓ‖ ^ 2 with hε
  have hYX : ∀ S b, ‖Y b - X S b‖ ^ 2 ≤ ε S := fun S b =>
    pulse_truncation hSc hj hjN h hc hp b (φ b) (hφ b) S m
  have hε0 : ∀ S, 0 ≤ ε S := fun S => (sq_nonneg _).trans (hYX S default)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := H)).sub hpar
    simpa [hε, sub_self] using this
  have hXc : ∀ S, Continuous (X S) := fun S =>
    continuous_finset_sum _ fun ℓ _ => continuous_const.mul (continuous_pulseEntry hSc hj hjN ℓ m)
  have hdist : ∀ S b, ‖Y b - X S b‖ ≤ Real.sqrt (ε S) := fun S b =>
    Real.le_sqrt_of_sq_le (hYX S b)
  have hYb : ∀ b, ‖Y b‖ ≤ Real.sqrt H := fun b => by
    have := hdist ∅ b
    simpa [hX, hε] using this
  have hYc : Continuous Y := by
    refine TendstoUniformly.continuous (F := X) (p := atTop) ?_ (Eventually.of_forall hXc).frequently
    rw [Metric.tendstoUniformly_iff]
    intro e he
    have hsq : Tendsto (fun S => Real.sqrt (ε S)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hεlim
    filter_upwards [hsq.eventually (gt_mem_nhds he)] with S hS b
    rw [dist_eq_norm]
    exact (hdist S b).trans_lt hS
  -- integrability
  have hYi : Integrable (fun b => ‖Y b‖ ^ 2) (blockMeasure L₀) :=
    Integrable.of_bound (hYc.norm.pow 2).aestronglyMeasurable H (Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := hYX ∅ b
      simpa [hX, hε] using this)
  have hXi : ∀ S, Integrable (fun b => ‖X S b‖ ^ 2) (blockMeasure L₀) := fun S =>
    Integrable.of_bound ((hXc S).norm.pow 2).aestronglyMeasurable ((∑ ℓ ∈ S, ‖c ℓ‖) ^ 2)
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have : ‖X S b‖ ≤ ∑ ℓ ∈ S, ‖c ℓ‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (norm_pulseEntry_le hSc hj hjN b ℓ m)
        exact pow_le_pow_left₀ (norm_nonneg _) this 2)
  -- the finite sums
  have hfin : ∀ S, ∑ ℓ ∈ S, kernelK N j ℓ m * ‖c ℓ‖ ^ 2 = ∫ b, ‖X S b‖ ^ 2 ∂(blockMeasure L₀) :=
    fun S => by
      rw [pulse_finite_average hSc hj hjN S c m]
      exact Finset.sum_congr rfl fun ℓ _ => mul_comm _ _
  set B : ℝ → ℝ := fun e => Real.sqrt e * (2 * Real.sqrt H + Real.sqrt e) with hB
  have hbound : ∀ S, ‖(∫ b, ‖X S b‖ ^ 2 ∂(blockMeasure L₀)) -
      ∫ b, ‖Y b‖ ^ 2 ∂(blockMeasure L₀)‖ ≤ B (ε S) := fun S => by
    rw [← integral_sub (hXi S) hYi]
    refine (norm_integral_le_of_norm_le_const (C := B (ε S)) (Eventually.of_forall fun b => ?_)).trans_eq
      (by simp)
    rw [Real.norm_eq_abs]
    refine sq_sub_sq_le_aux (norm_nonneg _) (norm_nonneg _) (norm_nonneg (Y b - X S b)) ?_
      (hdist S b) (hYb b)
    rw [norm_sub_rev (Y b)]
    exact abs_norm_sub_norm_le _ _
  have hBlim : Tendsto (fun S => B (ε S)) atTop (𝓝 0) := by
    have hBc : Continuous B := by
      simp only [hB]; fun_prop
    have := (hBc.tendsto 0).comp hεlim
    simpa [hB, Function.comp_def] using this
  unfold HasSum
  simp only [SummationFilter.unconditional_filter]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [hfin]
  exact squeeze_zero (fun S => norm_nonneg _) hbound hBlim

end AnomDiss
