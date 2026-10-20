module

public import RequestProject.Transfer

/-!
# Continuous dependence of the comparison scalar on the phases

The comparison scalar of Definition 5.5 depends continuously on the phase sequence `ω`
(with the product topology).  This is used to see that the Fourier coefficients of the
comparison scalar are measurable functions of `ω`, so that the expectations of Section 7
make sense.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- `L²` stability of the advection–diffusion equation with respect to the drift: two classical
solutions on `[0,T]` with drifts `D₁`, `D₂` satisfy
`‖θ(T) - φ(T)‖² ≤ ‖θ(0) - φ(0)‖² + (M²/(2ν)) ∫₀ᵀ ‖D₁ - D₂‖₂²`, where `|θ| ≤ M`. -/
lemma stage_stability {T ν M : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (D₁ : ℝ → Pt 2 → Pt 2) (hD₁c : ContinuousOn (fun q : ℝ × Pt 2 => D₁ q.1 q.2) (Icc 0 T ×ˢ univ))
    (hD₁reg : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (D₁ t) ∧ IsPeriodic (D₁ t) ∧
      ∀ x, divergence (D₁ t) x = 0)
    (D₂ : ℝ → Pt 2 → Pt 2) (hD₂c : ContinuousOn (fun q : ℝ × Pt 2 => D₂ q.1 q.2) (Icc 0 T ×ˢ univ))
    (hD₂reg : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (D₂ t) ∧ IsPeriodic (D₂ t) ∧
      ∀ x, divergence (D₂ t) x = 0)
    (θ₀ : Pt 2 → ℝ) (θ : ℝ → Pt 2 → ℝ) (hθ : IsClassicalScalar T ν D₁ θ₀ θ)
    (hθM : ∀ t ∈ Icc 0 T, ∀ x, |θ t x| ≤ M)
    (φ₀ : Pt 2 → ℝ) (φ : ℝ → Pt 2 → ℝ) (hφ : IsClassicalScalar T ν D₂ φ₀ φ) :
    l2sq (fun x => θ T x - φ T x) ≤ l2sq (fun x => θ 0 x - φ 0 x) +
      M ^ 2 / (2 * ν) * ∫ s in (0 : ℝ)..T, l2sqV (fun x => D₁ s x - D₂ s x) := by
  obtain ⟨β, hβ0, -, reg⟩ := hθ.regular
  obtain ⟨β', hβ0', -, regφ⟩ := hφ.regular
  have hab : (0 : ℝ) ≤ T := hT.le
  set z : ℝ → Pt 2 → ℝ := fun s x => θ s x - φ s x with hz
  set z' : ℝ → Pt 2 → ℝ := fun s x => dt T θ s x - dt T φ s x with hz'
  have hzc : ContinuousOn (fun q : ℝ × Pt 2 => z q.1 q.2) (Icc 0 T ×ˢ univ) :=
    reg.continuousOn.sub regφ.continuousOn
  have hz'c : ContinuousOn (fun q : ℝ × Pt 2 => z' q.1 q.2) (Icc 0 T ×ˢ univ) :=
    (reg.holder_dt.continuousOn hβ0).sub (regφ.holder_dt.continuousOn hβ0')
  have hd : ∀ s ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => z r x) (z' s x) s := by
    intro s hs x
    have h1 : HasDerivAt (fun r => θ r x) (dt T θ s x) s :=
      (reg.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)
    have h2 : HasDerivAt (fun r => φ r x) (dt T φ s x) s :=
      (regφ.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)
    exact h1.sub h2
  obtain ⟨hform, hcont⟩ := l2sq_integral_form hab z z' hzc hz'c hd
  set g : ℝ → ℝ := fun s => l2sqV (fun x => D₁ s x - D₂ s x) with hg
  have hgc : ContinuousOn g (Icc 0 T) := by
    refine continuousOn_integral_cell' hab _ ?_
    refine continuousOn_finset_sum _ fun k _ => ?_
    exact ((continuous_apply k).comp_continuousOn (hD₁c.sub hD₂c)).pow 2
  have hle : ∀ s ∈ Icc 0 T, ∫ x in cell 2, 2 * z s x * z' s x ≤ M ^ 2 / (2 * ν) * g s := by
    intro s hs
    obtain ⟨hv1, hvp, hvdiv⟩ := hD₁reg s hs
    obtain ⟨hD1, hDp, hDdiv⟩ := hD₂reg s hs
    have hθs := reg.smooth_x s hs
    have hφs := regφ.smooth_x s hs
    refine scalar_diff_energy_le ν M hν (D₂ s) (fun x => D₁ s x - D₂ s x) (θ s) (z s)
      (z' s) hD1 hDp hDdiv (hv1.sub hD1) (fun x n => by simp only [hvp x n, hDp x n])
      (fun x => by
        rw [divergence_sub_fun _ _ (hv1.differentiable one_ne_zero)
          (hD1.differentiable one_ne_zero), hvdiv, hDdiv, sub_zero])
      (hθs.of_le (by norm_num)) (hθ.periodic s hs) (hθM s hs) (hθs.sub hφs)
      (fun x n => by simp only [hz, hθ.periodic s hs x n, hφ.periodic s hs x n])
      (fun x => ?_)
    have h1 := hθ.eqn s hs x
    have h2 := hφ.eqn s hs x
    simp only [smul_eq_mul] at h1 h2
    simp only [hz, hz']
    rw [conv_sub_right _ _ _ (hθs.differentiable (by norm_num)) (hφs.differentiable (by norm_num)),
      conv_sub_left, lap_sub_fun _ _ hθs hφs]
    linear_combination h1 - h2
  have hfin := hform T ⟨hab, le_rfl⟩
  have hint : ∫ s in (0 : ℝ)..T, ∫ x in cell 2, 2 * z s x * z' s x ≤
      ∫ s in (0 : ℝ)..T, M ^ 2 / (2 * ν) * g s :=
    intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable_of_Icc hab)
      ((continuousOn_const.mul hgc).intervalIntegrable_of_Icc hab) hle
  rw [intervalIntegral.integral_const_mul] at hint
  linarith

lemma l2sqV_zero_sub : l2sqV (fun _ : Pt 2 => (0 : Pt 2) - 0) = 0 := by
  simp [l2sqV]

/-- Chaining `stage_stability` over the stages: two comparison scalars with the same initial
datum and phases `ω`, `ω'` satisfy
`‖θ̄_ω(s_j) - θ̄_{ω'}(s_j)‖² ≤ (M²/(2ν_N)) ∑_{i<j} ∫₀^{δ_i} ‖V_i^ω - V_i^{ω'}‖₂²`. -/
lemma comparison_chain {N : ℕ} (hN : 1 ≤ N) (w w' : Phase) (θ₀ : Pt 2 → ℝ) {M : ℝ}
    (hM : ∀ x, |θ₀ x| ≤ M) (θb θb' : ℝ → Pt 2 → ℝ) (h : IsComparisonScalar N w θ₀ θb)
    (h' : IsComparisonScalar N w' θ₀ θb') :
    ∀ j, 1 ≤ j → j ≤ N + 1 → l2sq (fun x => θb (sj j) x - θb' (sj j) x) ≤
      M ^ 2 / (2 * nuN N) * ∑ i ∈ Finset.Ico 1 j, ∫ t in (0 : ℝ)..δs i,
        l2sqV (fun x => Vpulse (nuN N) w i (sj i + t) x - Vpulse (nuN N) w' i (sj i + t) x) := by
  have hν := viscosity_properties.2.2.1 N hN
  have hθM : ∀ t ∈ Icc 0 (TN N), ∀ x, |θb t x| ≤ M := staged_abs_le hν.le h hM
  intro j hj hjN
  induction j, hj using Nat.le_induction with
  | base =>
    rw [sj_one, h.1, h'.1]
    simp [l2sq]
  | succ j hj ih =>
    have ih := ih (by omega)
    obtain ⟨hI, hJ⟩ := h.2 j hj (by omega)
    obtain ⟨hI', hJ'⟩ := h'.2 j hj (by omega)
    have hδ := δs_pos j hj
    have hη := ηs_pos j hj
    have hsj0 := (sj_bounds j).1
    have hjs : sj (j + 1) = sj j + δs j + ηs j := sj_succ j hj
    have hTN : sj (j + 1) ≤ TN N := sj_mono (by omega)
    have hreg : ∀ w : Phase, ∀ t ∈ Icc (0 : ℝ) (δs j),
        ContDiff ℝ 1 (Vpulse (nuN N) w j (sj j + t)) ∧
        IsPeriodic (Vpulse (nuN N) w j (sj j + t)) ∧
        ∀ x, divergence (Vpulse (nuN N) w j (sj j + t)) x = 0 := fun w t _ =>
      ⟨(Vpulse_slice_C2 _ w j _).of_le (by norm_num),
        (vpulse_stage_props (nuN N) w j).1 t, (vpulse_stage_props (nuN N) w j).2.2 t⟩
    have hSI := stage_stability hδ hν _
      (vpulse_stage_props (nuN N) w j).2.1.continuous.continuousOn (hreg w) _
      (vpulse_stage_props (nuN N) w' j).2.1.continuous.continuousOn (hreg w') _ _ hI
      (fun t ht x => hθM _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ x) _ _ hI'
    have hSJ := stage_stability hη hν (fun _ _ => 0) continuousOn_const
      (fun t _ => ⟨contDiff_const, fun _ _ => rfl, fun x => by simp [divergence, pd]⟩)
      (fun _ _ => 0) continuousOn_const
      (fun t _ => ⟨contDiff_const, fun _ _ => rfl, fun x => by simp [divergence, pd]⟩) _ _ hJ
      (fun t ht x => hθM _ ⟨by linarith [ht.1], by linarith [ht.2]⟩ x) _ _ hJ'
    simp only [add_zero, l2sqV_zero_sub, intervalIntegral.integral_zero, mul_zero] at hSI hSJ
    rw [Finset.sum_Ico_succ_top hj, hjs]
    have hc : 0 ≤ M ^ 2 / (2 * nuN N) := by positivity
    nlinarith

/-! ### Joint continuity of the pulses in the block parameter -/

lemma ControlFamily.continuous_coef_joint {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) :
    Continuous (fun p : (Fin L → Bool × Pt 2) × ℝ => cf.coef p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨b, s⟩
  set ιs : Fin L → Bool := fun i => (b i).1
  have hopen : IsOpen {p : (Fin L → Bool × Pt 2) × ℝ | ∀ i, (p.1 i).1 = ιs i} := by
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_discrete {ιs i}).preimage (by fun_prop : Continuous
        fun p : (Fin L → Bool × Pt 2) × ℝ => (p.1 i).1)
  have hU : (fun p : (Fin L → Bool × Pt 2) × ℝ => cf.coef (fun i => (ιs i, (p.1 i).2)) p.2)
      =ᶠ[𝓝 (b, s)] fun p => cf.coef p.1 p.2 := by
    filter_upwards [hopen.mem_nhds (fun i => rfl)] with p hp
    have : (fun i => (ιs i, (p.1 i).2)) = p.1 := by
      funext i; exact Prod.ext (hp i).symm rfl
    simp only [this]
  refine ContinuousAt.congr ?_ hU
  exact ((cf.smooth ιs).continuous.comp (by fun_prop : Continuous
    fun p : (Fin L → Bool × Pt 2) × ℝ => ((fun i => (p.1 i).2), p.2))).continuousAt

lemma continuous_dampedCoef_joint {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) (μ : ℝ) :
    Continuous (fun p : BlockParam L × ℝ => dampedCoef cf μ p.1 p.2) := by
  have hA := cf.continuous_coef_joint
  have h1 : Continuous (fun p : BlockParam L × ℝ => cf.coef p.1.1 p.2) :=
    hA.comp (by fun_prop : Continuous fun p : BlockParam L × ℝ => (p.1.1, p.2))
  have h2 : Continuous (Function.uncurry fun (p : BlockParam L × ℝ) (r : ℝ) =>
      Real.exp (-μ * (p.2 - r)) • cf.coef p.1.1 r) := by
    have : Continuous (fun q : (BlockParam L × ℝ) × ℝ => cf.coef q.1.1.1 q.2) :=
      hA.comp (by fun_prop : Continuous fun q : (BlockParam L × ℝ) × ℝ => (q.1.1.1, q.2))
    exact (by fun_prop : Continuous fun q : (BlockParam L × ℝ) × ℝ =>
      Real.exp (-μ * (q.1.2 - q.2))).smul this
  have h3 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) h2 (continuous_snd)
  exact h1.fun_sub (continuous_const.fun_smul h3)

lemma continuous_eField_joint : Continuous (fun q : (Fin 4 → ℝ) × Pt 2 => eField q.1 q.2) := by
  unfold eField
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).smul ((contDiff_eBasis i).continuous.comp continuous_snd)

lemma continuous_VpulseB_joint (ν : ℝ) (j : ℕ) :
    Continuous (fun p : BlockParam L₀ × ℝ × Pt 2 => VpulseB ν j p.1 p.2.1 p.2.2) := by
  have e : (fun p : BlockParam L₀ × ℝ × Pt 2 => VpulseB ν j p.1 p.2.1 p.2.2) = fun p =>
      (1 / (kk j * δs j)) • eField (dampedCoef cf₀ (muNu ν j) p.1 ((p.2.1 - sj j) / δs j))
        (kk j • p.2.2 - p.1.2) := by
    funext p; simp only [VpulseB, dampedB_eq]
  rw [e]
  refine continuous_const.fun_smul (continuous_eField_joint.comp (Continuous.prodMk ?_
    (by fun_prop : Continuous fun p : BlockParam L₀ × ℝ × Pt 2 => kk j • p.2.2 - p.1.2)))
  exact (continuous_dampedCoef_joint cf₀ (muNu ν j)).comp
    (by fun_prop : Continuous fun p : BlockParam L₀ × ℝ × Pt 2 => (p.1, (p.2.1 - sj j) / δs j))

/-- The stage velocity discrepancy `b ↦ ∫₀^{δ_j} ‖V_j^b - V_j^{b₀}‖₂²` is continuous in `b`. -/
lemma continuous_stage_discrepancy (ν : ℝ) (j : ℕ) (b₀ : BlockParam L₀) :
    Continuous (fun b : BlockParam L₀ => ∫ t in (0 : ℝ)..δs j,
      l2sqV (fun x => VpulseB ν j b (sj j + t) x - VpulseB ν j b₀ (sj j + t) x)) := by
  have hV := continuous_VpulseB_joint ν j
  have hF : Continuous (Function.uncurry fun (q : BlockParam L₀ × ℝ) (x : Pt 2) =>
      ∑ k, (VpulseB ν j q.1 (sj j + q.2) x - VpulseB ν j b₀ (sj j + q.2) x) k ^ 2) := by
    have h1 : Continuous (fun r : (BlockParam L₀ × ℝ) × Pt 2 =>
        VpulseB ν j r.1.1 (sj j + r.1.2) r.2) :=
      hV.comp (by fun_prop : Continuous
        fun r : (BlockParam L₀ × ℝ) × Pt 2 => (r.1.1, sj j + r.1.2, r.2))
    have h2 : Continuous (fun r : (BlockParam L₀ × ℝ) × Pt 2 =>
        VpulseB ν j b₀ (sj j + r.1.2) r.2) :=
      hV.comp (by fun_prop : Continuous
        fun r : (BlockParam L₀ × ℝ) × Pt 2 => (b₀, sj j + r.1.2, r.2))
    exact continuous_finset_sum _ fun k _ => ((continuous_apply k).comp (h1.sub h2)).pow 2
  have hG := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_Icc : IsCompact (cell 2))
  have hG' : Continuous (Function.uncurry fun (b : BlockParam L₀) (t : ℝ) =>
      l2sqV (fun x => VpulseB ν j b (sj j + t) x - VpulseB ν j b₀ (sj j + t) x)) := by
    simpa [l2sqV, Function.uncurry_def, cell] using hG
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG' 0 (δs j)

end AnomDiss
