module

public import RequestProject.EnergyCalc

/-!
# Section 5: isolated pulses and comparison estimates
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- `L²(𝕋²)` norm of a vector field. -/
def l2V (v : Pt 2 → Pt 2) : ℝ := Real.sqrt (l2sqV v)

/-- `μ_j^ν = 4π² ν k_j² δ_j` (Definition 5.1). -/
def muNu (ν : ℝ) (j : ℕ) : ℝ := 4 * π ^ 2 * ν * kk j ^ 2 * δs j

/-- The isolated pulse attached to a single block parameter `b`:
`(k_j δ_j)⁻¹ B_{μ_j^ν, b}((t - s_j)/δ_j, k_j x)`. -/
def VpulseB (ν : ℝ) (j : ℕ) (b : BlockParam L₀) (t : ℝ) (x : Pt 2) : Pt 2 :=
  (1 / (kk j * δs j)) • dampedB cf₀ (muNu ν j) b ((t - sj j) / δs j) (kk j • x)

/-- The isolated pulse
`V_j^ν(t,x) = (k_j δ_j)⁻¹ B_{μ_j^ν, ω_j}((t - s_j)/δ_j, k_j x)` (Definition 5.1). -/
def Vpulse (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) (x : Pt 2) : Pt 2 := VpulseB ν j (w j) t x

/-- `A_j^ν = ν^{M+1} k_j^{2M+1} δ_j^M` (Definition 5.1). -/
def Apulse (ν : ℝ) (j : ℕ) : ℝ := ν ^ (M₀ + 1) * kk j ^ (2 * M₀ + 1) * δs j ^ M₀

lemma kk_eq_cast (j : ℕ) : kk j = ((qq ^ j : ℕ) : ℝ) := by simp [kk]

lemma kk_pos' (j : ℕ) : 0 < kk j := by unfold kk; have := qq_ge; positivity

lemma Vpulse_eq (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) :
    Vpulse ν w j t = fun x => (1 / (kk j * δs j)) •
      eField (dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j)) (kk j • x - (w j).2) := by
  funext x; simp only [Vpulse, VpulseB, dampedB_eq]

/-- A potential `φ_c` with `b_c · ∇b_c = ∇φ_c` (Lemma 2.9). -/
def potE (c : Fin 4 → ℝ) : Pt 2 → ℝ := Classical.choose (eigenspace_properties c).2.2.2.2.2

lemma potE_spec (c : Fin 4 → ℝ) : ContDiff ℝ ∞ (potE c) ∧ IsPeriodic (potE c) ∧
    ∀ x, conv (eField c) (eField c) x = grad (potE c) x :=
  Classical.choose_spec (eigenspace_properties c).2.2.2.2.2

lemma affine_intVec (j : ℕ) (z x : Pt 2) (n : Fin 2 → ℤ) :
    kk j • (x + intVec n) - z = (kk j • x - z) + intVec (((qq ^ j : ℕ) : ℤ) • n) := by
  rw [kk_eq_cast]; funext i; simp [intVec]; ring

/-- The pressure of the isolated pulse. -/
def Ppulse (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) (x : Pt 2) : ℝ :=
  -(1 / (kk j * δs j)) ^ 2 *
    potE (dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j)) (kk j • x - (w j).2)

lemma Ppulse_periodic (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) : IsPeriodic (Ppulse ν w j t) := by
  intro x n
  simp only [Ppulse, affine_intVec]
  rw [(potE_spec _).2.1]

lemma Vpulse_hasDerivAt (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) (x : Pt 2) :
    HasDerivAt (fun t => Vpulse ν w j t x) ((1 / (kk j * δs j)) •
      eField ((1 / δs j) • (deriv (cf₀.coef (w j).1) ((t - sj j) / δs j) -
        muNu ν j • dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j))) (kk j • x - (w j).2)) t := by
  have ha : HasDerivAt (fun t => (t - sj j) / δs j) (1 / δs j) t := by
    simpa using ((hasDerivAt_id t).sub_const (sj j)).div_const (δs j)
  have hD := (hasDerivAt_dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j)).scomp t ha
  have hE := ((eFieldCLM (kk j • x - (w j).2)).hasFDerivAt.comp_hasDerivAt t hD).const_smul
    (1 / (kk j * δs j))
  simp only [Vpulse_eq]
  convert hE using 1
  · funext r
    simp only [Pi.smul_apply, Function.comp_apply, eFieldCLM_apply]
  · rw [eFieldCLM_apply]

/-- The isolated pulse solves the forced Navier–Stokes equation on `I_j`. -/
lemma Vpulse_equation (ν : ℝ) (w : Phase) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (ht : t ∈ Ij j)
    (x : Pt 2) :
    deriv (fun t => Vpulse ν w j t x) t + conv (Vpulse ν w j t) (Vpulse ν w j t) x +
      grad (Ppulse ν w j t) x = ν • lap (Vpulse ν w j t) x + gForce w t x := by
  have hδ := δs_pos j hj
  have hk := kk_pos' j
  set s := (t - sj j) / δs j with hs
  set D := dampedCoef cf₀ (muNu ν j) (w j) s
  set c' := deriv (cf₀.coef (w j).1) s
  set z := (w j).2
  set y := kk j • x - z
  set a := 1 / (kk j * δs j) with ha
  have hE := eigenspace_properties D
  have hFd : Differentiable ℝ (eField D) := hE.1.differentiable (by simp)
  have hV : Vpulse ν w j t = fun x => a • eField D (kk j • x - z) := Vpulse_eq ν w j t
  have hP : Ppulse ν w j t = fun x => (-a ^ 2) * potE D (kk j • x - z) := by
    funext x; simp only [Ppulse, ha, neg_mul]; rfl
  rw [(Vpulse_hasDerivAt ν w j t x).deriv, hV, hP, conv_affine _ hFd, lap_affine _
    (hE.1.of_le (WithTop.coe_le_coe.2 le_top)), grad_affine _ ((potE_spec D).1.differentiable
    (by simp)), (potE_spec D).2.2, hE.2.2.2.2.1, gForce_on_Ij w hj ht]
  simp only [bDot]
  rw [show kk j • x - z = y from rfl]
  simp only [← eFieldCLM_apply, map_sub, map_smul]
  set X := eFieldCLM y c'
  set Y := eFieldCLM y D
  set G := grad (potE D) y
  have hμ : muNu ν j = 4 * π ^ 2 * ν * kk j ^ 2 * δs j := rfl
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hμ, ha]
  field_simp
  ring

lemma muNu_nonneg {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) : 0 ≤ muNu ν j := by
  unfold muNu δs τstar; positivity

lemma Vpulse_grad_bound {ν : ℝ} (hν : 0 < ν) (w : Phase) {j : ℕ} (hj : 1 ≤ j) :
    (∫⁻ t in Ij j, ⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (Vpulse ν w j t) x)))
      ≤ ENNReal.ofReal Λ₀ := by
  have hδ := δs_pos j hj
  have hk := kk_pos' j
  set μ := muNu ν j
  set z := (w j).2
  unfold Ij
  rw [lintegral_Icc_affine (sj j) hδ]
  refine (lintegral_mono fun u => ?_).trans
    ((damped_response cf₀ μ (muNu_nonneg hν.le j) (w j)).2.2.2.trans (le_of_eq rfl))
  set D := dampedCoef cf₀ μ (w j) u
  have hFd : Differentiable ℝ (eField D) := (eigenspace_properties D).1.differentiable (by simp)
  have hu : (sj j + δs j * u - sj j) / δs j = u := by field_simp; ring
  rw [Vpulse_eq, hu, ENNReal.mul_iSup]
  refine iSup_le fun x => ?_
  rw [fderiv_affine_comp _ hFd, ← ENNReal.ofReal_mul hδ.le]
  have hak : 1 / (kk j * δs j) * kk j = 1 / δs j := by field_simp
  rw [hak]
  refine le_iSup_of_le (kk j • x) (ENNReal.ofReal_le_ofReal ?_)
  rw [dampedB_eq, fderiv_comp_sub]
  calc δs j * eucOp ((1 / δs j) • fderiv ℝ (eField D) (kk j • x - z))
      ≤ δs j * (|1 / δs j| * eucOp (fderiv ℝ (eField D) (kk j • x - z))) :=
        mul_le_mul_of_nonneg_left (eucOp_smul_le _ _) hδ.le
    _ = eucOp (fderiv ℝ (eField D) (kk j • x - z)) := by
        rw [abs_of_pos (by positivity)]; field_simp

lemma volume_real_cell2 : (volume : Measure (Pt 2)).real (cell 2) = 1 := by
  simp [Measure.real, cell, Real.volume_Icc_pi]

lemma l2V_le_of_bound (v : Pt 2 → Pt 2) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖v x‖ ≤ B) :
    l2V v ≤ 2 * B := by
  have hpt : ∀ x, ‖∑ k, v x k ^ 2‖ ≤ 2 * B ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Fin.sum_univ_two]
    have h0 : |v x 0| ≤ B := (norm_le_pi_norm (v x) 0).trans (hB x)
    have h1 : |v x 1| ≤ B := (norm_le_pi_norm (v x) 1).trans (hB x)
    have := sq_le_sq' (abs_le.1 h0).1 (abs_le.1 h0).2
    have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
    linarith
  have hl2 : l2sqV v ≤ 2 * B ^ 2 := by
    have hfin : (volume : Measure (Pt 2)) (cell 2) < ⊤ := by
      simp [cell, Real.volume_Icc_pi]
    have := norm_setIntegral_le_of_norm_le_const hfin (fun x _ => hpt x)
    rw [volume_real_cell2, mul_one] at this
    exact (le_abs_self _).trans (by simpa [l2sqV, Real.norm_eq_abs] using this)
  unfold l2V
  calc Real.sqrt (l2sqV v) ≤ Real.sqrt ((2 * B) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 2 * B := Real.sqrt_sq (by positivity)

lemma Vpulse_terminal_bound {ν : ℝ} (hν : 0 < ν) (w : Phase) {j : ℕ} (hj : 1 ≤ j) :
    l2V (Vpulse ν w j (sj j + δs j)) ≤
      (2 * (S₀ 0 / (M₀.factorial : ℝ)) * (4 * π ^ 2) ^ (M₀ + 1)) * Apulse ν j := by
  have hδ := δs_pos j hj
  have hk := kk_pos' j
  set μ := muNu ν j
  have hμ := muNu_nonneg hν.le j
  set K := S₀ 0 / (M₀.factorial : ℝ) * μ ^ (M₀ + 1)
  have hK0 : 0 ≤ K := by have := S₀_nonneg 0; positivity
  have hB : ∀ y, ‖dampedB cf₀ μ (w j) 1 y‖ ≤ K := by
    intro y
    have h := ((damped_response cf₀ μ hμ (w j)).2.2.1 0).2.2.2
    have h2 : ‖dampedB cf₀ μ (w j) 1 y‖ₑ ≤ cNormE 0 (dampedB cf₀ μ (w j) 1) := by
      refine le_iSup_of_le y ?_
      rw [Finset.sum_range_one, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        norm_iteratedFDeriv_zero]
    have := h2.trans h
    rw [← ofReal_norm_eq_enorm] at this
    exact (ENNReal.ofReal_le_ofReal_iff hK0).1 this
  have hV : Vpulse ν w j (sj j + δs j) = fun x =>
      (1 / (kk j * δs j)) • dampedB cf₀ μ (w j) 1 (kk j • x) := by
    funext x
    simp only [Vpulse, VpulseB, add_sub_cancel_left, div_self hδ.ne']
    rfl
  have ha : 0 ≤ 1 / (kk j * δs j) := by positivity
  refine (l2V_le_of_bound _ (mul_nonneg ha hK0) fun x => ?_).trans (le_of_eq ?_)
  · rw [hV, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (hB _) ha
  · simp only [K, μ, muNu, Apulse]
    field_simp
    ring

/-- **Lemma 5.2** (isolated pulses).  `V_j^ν` is periodic, divergence free, vanishes at `s_j`,
and solves the Navier–Stokes equation on `I_j` with force `g_ω` and a suitable periodic
pressure; moreover `∫_{I_j}‖∇V_j^ν‖_{L^∞,op} ≤ Λ` and
`r_j^ν = ‖V_j^ν(s_j + δ_j)‖₂ ≤ C_M A_j^ν`. -/
theorem isolated_pulse_properties : ∃ C : ℝ, ∀ ν : ℝ, 0 < ν → ∀ j : ℕ, 1 ≤ j → ∀ w : Phase,
    (∃ P : ℝ → Pt 2 → ℝ, (∀ t, IsPeriodic (P t)) ∧ ∀ t ∈ Ij j, ∀ x,
      deriv (fun t => Vpulse ν w j t x) t + conv (Vpulse ν w j t) (Vpulse ν w j t) x +
        grad (P t) x = ν • lap (Vpulse ν w j t) x + gForce w t x) ∧
    (∀ t, IsPeriodic (Vpulse ν w j t) ∧ ∀ x, divergence (Vpulse ν w j t) x = 0) ∧
    Vpulse ν w j (sj j) = 0 ∧
    (∫⁻ t in Ij j, ⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (Vpulse ν w j t) x)))
      ≤ ENNReal.ofReal Λ₀ ∧
    l2V (Vpulse ν w j (sj j + δs j)) ≤ C * Apulse ν j := by
  refine ⟨2 * (S₀ 0 / (M₀.factorial : ℝ)) * (4 * π ^ 2) ^ (M₀ + 1), fun ν hν j hj w =>
    ⟨⟨Ppulse ν w j, Ppulse_periodic ν w j, fun t ht x => Vpulse_equation ν w j hj t ht x⟩,
      fun t => ?_, ?_, Vpulse_grad_bound hν w hj, Vpulse_terminal_bound hν w hj⟩⟩
  · have h := trigDrift_props (fun t => dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j))
      ((contDiff_dampedCoef cf₀ (muNu ν j) (w j) 2).comp
        ((contDiff_id.sub contDiff_const).div_const _))
      (1 / (kk j * δs j)) (qq ^ j) (w j).2
    have hV : Vpulse ν w j t = fun x => (1 / (kk j * δs j)) •
        eField (dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j))
          (((qq ^ j : ℕ) : ℝ) • x - (w j).2) := by
      rw [Vpulse_eq, kk_eq_cast]
    rw [hV]
    exact ⟨h.1 t, h.2.2 t⟩
  · funext x
    simp only [Vpulse, VpulseB, sub_self, zero_div,
      (damped_response cf₀ _ (muNu_nonneg hν.le j) (w j)).2.1]
    simp

/-! ### Regularity of the pulses and the energy estimate -/

lemma Vpulse_fun_eq (ν : ℝ) (w : Phase) (j : ℕ) :
    Vpulse ν w j = fun t x => (1 / (kk j * δs j)) •
      eField (dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j))
        (((qq ^ j : ℕ) : ℝ) • x - (w j).2) := by
  funext t; rw [Vpulse_eq, kk_eq_cast]

lemma Vpulse_props (ν : ℝ) (w : Phase) (j : ℕ) :
    (∀ t, IsPeriodic (Vpulse ν w j t)) ∧
    ContDiff ℝ 2 (Function.uncurry (Vpulse ν w j)) ∧
    (∀ t x, divergence (Vpulse ν w j t) x = 0) := by
  have h := trigDrift_props (fun t => dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j))
    ((contDiff_dampedCoef cf₀ (muNu ν j) (w j) 2).comp
      ((contDiff_id.sub contDiff_const).div_const _))
    (1 / (kk j * δs j)) (qq ^ j) (w j).2
  rw [Vpulse_fun_eq]
  exact h

lemma Vpulse_slice_C2 (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) : ContDiff ℝ 2 (Vpulse ν w j t) := by
  have := (Vpulse_props ν w j).2.1.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2
    (fun x : Pt 2 => (t, x)))
  exact this

lemma Vpulse_hasDerivAt' (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) (x : Pt 2) :
    HasDerivAt (fun r => Vpulse ν w j r x)
      (fderiv ℝ (Function.uncurry (Vpulse ν w j)) (t, x) (1, 0)) t := by
  have hF := (Vpulse_props ν w j).2.1
  have hin : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × Pt 2)) ((1 : ℝ), (0 : Pt 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have := ((hF.differentiable (by norm_num)) (t, x)).hasFDerivAt.comp_hasDerivAt t hin
  exact this

lemma continuous_Vpulse_dt (ν : ℝ) (w : Phase) (j : ℕ) :
    Continuous fun p : ℝ × Pt 2 =>
      fderiv ℝ (Function.uncurry (Vpulse ν w j)) (p.1, p.2) (1, 0) := by
  have hF := (Vpulse_props ν w j).2.1
  exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma Ppulse_C1 (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) : ContDiff ℝ 1 (Ppulse ν w j t) := by
  have : Ppulse ν w j t = fun x => -(1 / (kk j * δs j)) ^ 2 *
      potE (dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j)) (kk j • x - (w j).2) := by
    funext x; rfl
  rw [this]
  exact contDiff_const.mul (((potE_spec _).1.of_le (by exact_mod_cast le_top)).comp
    ((contDiff_id.const_smul (kk j)).sub contDiff_const))


lemma eucOp_gradCLM_le (y : Pt 2) (v : Fin 4 → ℝ) :
    eucOp (gradCLM y v) ≤ 2 * aConst 1 * ‖v‖ := by
  have h := gSum_le v y
  unfold gSum at h
  exact (ENNReal.ofReal_le_ofReal_iff (by
    have := aConst_nonneg 1; positivity)).1 h

/-- The damped coefficient driving the pulse `V_j`. -/
def pulseCoef (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) : Fin 4 → ℝ :=
  dampedCoef cf₀ (muNu ν j) (w j) ((t - sj j) / δs j)

lemma continuous_pulseCoef (ν : ℝ) (w : Phase) (j : ℕ) : Continuous (pulseCoef ν w j) :=
  (contDiff_dampedCoef cf₀ (muNu ν j) (w j) 0).continuous.comp
    ((continuous_id.sub continuous_const).div_const _)

lemma fderiv_Vpulse (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) (t : ℝ) (x : Pt 2) :
    fderiv ℝ (Vpulse ν w j t) x =
      (1 / δs j) • gradCLM (kk j • x - (w j).2) (pulseCoef ν w j t) := by
  have hδ := δs_pos j hj
  have hk := kk_pos' j
  have hFd : Differentiable ℝ (eField (pulseCoef ν w j t)) :=
    (contDiff_eField _).differentiable (by simp)
  rw [Vpulse_eq, ← pulseCoef, fderiv_affine_comp _ hFd, fderiv_eField]
  congr 1
  field_simp

/-- `sup_x ‖∇V_j(t,x)‖_op`. -/
def gradSup (ν : ℝ) (w : Phase) (j : ℕ) (t : ℝ) : ℝ :=
  ⨆ x, eucOp (fderiv ℝ (Vpulse ν w j t) x)

lemma eucOp_fderiv_Vpulse_le (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) (t : ℝ) (x : Pt 2) :
    eucOp (fderiv ℝ (Vpulse ν w j t) x) ≤ 1 / δs j * (2 * aConst 1 * ‖pulseCoef ν w j t‖) := by
  have hδ := δs_pos j hj
  rw [fderiv_Vpulse ν w hj]
  refine (eucOp_smul_le _ _).trans ?_
  rw [abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (eucOp_gradCLM_le _ _) (by positivity)

lemma bddAbove_gradSup (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    BddAbove (range fun x => eucOp (fderiv ℝ (Vpulse ν w j t) x)) :=
  ⟨_, by rintro _ ⟨x, rfl⟩; exact eucOp_fderiv_Vpulse_le ν w hj t x⟩

lemma le_gradSup (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) (t : ℝ) (x : Pt 2) :
    eucOp (fderiv ℝ (Vpulse ν w j t) x) ≤ gradSup ν w j t :=
  le_ciSup (bddAbove_gradSup ν w hj t) x

lemma gradSup_nonneg (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) (t : ℝ) : 0 ≤ gradSup ν w j t :=
  (eucOp_nonneg _).trans (le_gradSup ν w hj t 0)

lemma gradSup_le_add (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) (t t' : ℝ) :
    gradSup ν w j t ≤ gradSup ν w j t' +
      1 / δs j * (2 * aConst 1 * ‖pulseCoef ν w j t - pulseCoef ν w j t'‖) := by
  have hδ := δs_pos j hj
  refine ciSup_le fun x => ?_
  have e : fderiv ℝ (Vpulse ν w j t) x = fderiv ℝ (Vpulse ν w j t') x +
      (1 / δs j) • gradCLM (kk j • x - (w j).2) (pulseCoef ν w j t - pulseCoef ν w j t') := by
    rw [fderiv_Vpulse ν w hj, fderiv_Vpulse ν w hj, map_sub, smul_sub]; abel
  rw [e]
  refine (eucOp_add_le _ _).trans (add_le_add (le_gradSup ν w hj t' x) ?_)
  refine (eucOp_smul_le _ _).trans ?_
  rw [abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (eucOp_gradCLM_le _ _) (by positivity)

lemma continuous_gradSup (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) :
    Continuous (gradSup ν w j) := by
  have hδ := δs_pos j hj
  set K := 1 / δs j * (2 * aConst 1)
  have hb : ∀ t t', |gradSup ν w j t - gradSup ν w j t'| ≤
      K * ‖pulseCoef ν w j t - pulseCoef ν w j t'‖ := by
    intro t t'
    have h1 := gradSup_le_add ν w hj t t'
    have h2 := gradSup_le_add ν w hj t' t
    rw [norm_sub_rev] at h2
    rw [abs_le]; constructor <;> nlinarith
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Tendsto (fun t' => K * ‖pulseCoef ν w j t' - pulseCoef ν w j t‖) (𝓝 t) (𝓝 0) := by
    have := (((continuous_pulseCoef ν w j).sub (continuous_const (y := pulseCoef ν w j t))).norm.tendsto t).const_mul K
    simpa using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t' => by
    rw [Real.norm_eq_abs]; exact hb t' t) hc

lemma ofReal_ciSup_le {ι : Type*} (f : ι → ℝ) :
    ENNReal.ofReal (⨆ i, f i) ≤ ⨆ i, ENNReal.ofReal (f i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne (⨆ i, ENNReal.ofReal (f i)) ⊤ with h | h
  · rw [h]; exact le_top
  rw [← ENNReal.ofReal_toReal h]
  refine ENNReal.ofReal_le_ofReal (ciSup_le fun i => ?_)
  rcases le_or_gt (f i) 0 with hi | hi
  · exact hi.trans ENNReal.toReal_nonneg
  · exact (ENNReal.ofReal_le_iff_le_toReal h).1 (le_iSup (fun i => ENNReal.ofReal (f i)) i)

lemma integral_gradSup_le (ν : ℝ) (hν : 0 < ν) (w : Phase) {j : ℕ} (hj : 1 ≤ j) (t : ℝ)
    (ht : t ∈ Ij j) : ∫ s in sj j..t, gradSup ν w j s ≤ Λ₀ := by
  have hc := continuous_gradSup ν w hj
  have hnn := gradSup_nonneg ν w hj
  have hΛ : 0 ≤ Λ₀ := by
    unfold Λ₀; have := S₀_nonneg 1; linarith
  have hint : IntegrableOn (gradSup ν w j) (Ij j) := hc.continuousOn.integrableOn_compact isCompact_Icc
  calc ∫ s in sj j..t, gradSup ν w j s = ∫ s in Ioc (sj j) t, gradSup ν w j s :=
        intervalIntegral.integral_of_le ht.1
    _ ≤ ∫ s in Ij j, gradSup ν w j s :=
        setIntegral_mono_set hint (Eventually.of_forall fun s => hnn s)
          (Eventually.of_forall (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)))
    _ ≤ Λ₀ := by
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
          hc.aestronglyMeasurable]
        refine ENNReal.toReal_le_of_le_ofReal hΛ ?_
        refine le_trans (lintegral_mono fun s => ?_) (Vpulse_grad_bound hν w hj)
        exact ofReal_ciSup_le _


section ops
variable {d : ℕ}

lemma divergence_sub_fun (f g : Pt d → Pt d) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x : Pt d) : divergence (fun y => f y - g y) x = divergence f x - divergence g x := by
  unfold divergence
  simp [pd_sub_fun f g hf hg, Finset.sum_sub_distrib]

lemma lap_sub_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Pt d → E)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Pt d) :
    lap (fun y => f y - g y) x = lap f x - lap g x := by
  unfold lap
  simp only [pd_sub_fun f g (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_sub_fun _ _ ((contDiff_pd_of_C2 f hf i).differentiable (by norm_num))
    ((contDiff_pd_of_C2 g hg i).differentiable (by norm_num))]

lemma conv_sub_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Pt d → Pt d)
    (f g : Pt d → E) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Pt d) :
    conv u (fun y => f y - g y) x = conv u f x - conv u g x := by
  unfold conv
  simp [pd_sub_fun f g hf hg, smul_sub, Finset.sum_sub_distrib]

lemma conv_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Pt d → Pt d)
    (h : Pt d → E) (x : Pt d) :
    conv (fun y => f y - g y) h x = conv f h x - conv g h x := by
  unfold conv
  simp [sub_smul, Finset.sum_sub_distrib]

lemma grad_sub_fun (p q : Pt d → ℝ) (hp : Differentiable ℝ p) (hq : Differentiable ℝ q)
    (x : Pt d) : grad (fun y => p y - q y) x = grad p x - grad q x := by
  funext i
  simp [grad, pd_sub_fun p q hp hq]

lemma conv_zero_right (u : Pt d → Pt d) (x : Pt d) : conv u (fun _ => (0 : Pt d)) x = 0 := by
  simp [conv, pd]

end ops

lemma eucOp_zero : eucOp (0 : Pt 2 →L[ℝ] Pt 2) ≤ 0 :=
  eucOp_le_of _ _ fun e _ => by simp [euclNorm]

lemma gForce_gap (w : Phase) {j : ℕ} (hj : 1 ≤ j) {s : ℝ}
    (hs : s ∈ Ioo (sj j + δs j) (sj (j + 1))) : gForce w s = 0 := by
  have hn : ∀ i, ¬ (1 ≤ i ∧ s ∈ Ij i) := by
    rintro i ⟨hi, hsi⟩
    rcases lt_trichotomy i j with h | rfl | h
    · have h1 := sj_lt_succ i hi
      have h2 := sj_mono (show i + 1 ≤ j by omega)
      linarith [hsi.2, hs.1, δs_pos j hj]
    · linarith [hsi.2, hs.1]
    · have h2 := sj_mono (show j + 1 ≤ i by omega)
      linarith [hsi.1, hs.2]
  funext x
  simp [gForce, hn]

lemma sj_succ_lt_one (j : ℕ) : sj (j + 1) < 1 :=
  (sj_bounds _).2.trans_lt accumulation_time.2

lemma Ij_subset_unit {j : ℕ} (hj : 1 ≤ j) : Ij j ⊆ Icc 0 1 := fun _ ht =>
  ⟨(sj_bounds j).1.trans ht.1, (ht.2.trans (sj_lt_succ j hj).le).trans (sj_succ_lt_one j).le⟩

/-- On the quiet interval `J_j` the force vanishes, so the kinetic energy does not increase. -/
lemma quiet_energy_le (ν : ℝ) (hν : 0 < ν) (w : Phase) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ) (hv : IsClassicalNS 1 ν 0 (gForce w) v p) (j : ℕ) (hj : 1 ≤ j) :
    ∀ t ∈ Icc (sj j + δs j) (sj (j + 1)), l2sqV (v t) ≤ l2sqV (v (sj j + δs j)) := by
  obtain ⟨β, hβ0, -, reg, regp⟩ := hv.regular
  have hδ := δs_pos j hj
  have hvd : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ x, HasDerivAt (fun r => v r x) (dt 1 v s x) s :=
    fun s hs x => (reg.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hb : sj j + δs j ≤ sj (j + 1) := (sj_lt_succ j hj).le
  have hJ : Icc (sj j + δs j) (sj (j + 1)) ⊆ Icc 0 1 := fun s hs =>
    ⟨(by linarith [(sj_bounds j).1] : (0 : ℝ) ≤ sj j + δs j).trans hs.1,
      hs.2.trans (sj_succ_lt_one j).le⟩
  have hJoo : ∀ s ∈ Ioo (sj j + δs j) (sj (j + 1)), s ∈ Ioo (0 : ℝ) 1 := fun s hs =>
    ⟨((hJ ⟨le_rfl, hb⟩).1).trans_lt hs.1, hs.2.trans_le (hJ ⟨hb, le_rfl⟩).2⟩
  have key2 := perturbation_energy hb ν hν.le v v (dt 1 v) (fun _ _ => 0) p (fun _ => 0)
    (reg.continuousOn.mono (prod_mono hJ subset_rfl))
    ((reg.holder_dt.continuousOn hβ0).mono (prod_mono hJ subset_rfl))
    (fun s hs x => hvd s (hJoo s hs) x)
    (fun s hs => by
      have hs1 := Ioo_subset_Icc_self (hJoo s hs)
      have hvs := reg.smooth_x s hs1
      exact ⟨hvs.of_le (by norm_num), hv.periodic_u s hs1, hv.div_free s hs1, hvs,
        hv.periodic_u s hs1, hv.div_free s hs1, regp.smooth_x s hs1, hv.periodic_p s hs1,
        contDiff_const, fun x => by simpa using eucOp_zero⟩)
    (fun s hs x => by
      have hs1 := Ioo_subset_Icc_self (hJoo s hs)
      have h1 := hv.eqn s hs1 x
      rw [gForce_gap w hj hs, Pi.zero_apply, add_zero] at h1
      rw [conv_zero_right, add_zero, h1])
    continuousOn_const
  intro t ht
  have h2 := key2 t ht
  simp only [intervalIntegral.integral_zero, mul_zero, Real.exp_zero, mul_one] at h2
  exact h2

/-- **Lemma 5.3** (single-stage stability).  With `E_j = ‖v(s_j)‖₂`,
`sup_{t ∈ I_j}‖v(t) - V_j^ν(t)‖₂ ≤ e^Λ E_j` and `E_{j+1} ≤ e^Λ E_j + r_j^ν`. -/
theorem single_stage_stability (ν : ℝ) (hν : 0 < ν) (w : Phase) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ) (hv : IsClassicalNS 1 ν 0 (gForce w) v p) (j : ℕ) (hj : 1 ≤ j) :
    (∀ t ∈ Ij j, l2V (v t - Vpulse ν w j t) ≤ Real.exp Λ₀ * l2V (v (sj j))) ∧
    l2V (v (sj (j + 1))) ≤ Real.exp Λ₀ * l2V (v (sj j)) + l2V (Vpulse ν w j (sj j + δs j)) := by
  obtain ⟨β, hβ0, -, reg, regp⟩ := hv.regular
  have hδ := δs_pos j hj
  have hI := Ij_subset_unit hj
  have hV0 : Vpulse ν w j (sj j) = 0 := by
    obtain ⟨C, hC⟩ := isolated_pulse_properties
    exact (hC ν hν j hj w).2.2.1
  have hΛ : 0 ≤ Λ₀ := by unfold Λ₀; have := S₀_nonneg 1; linarith
  set V := Vpulse ν w j with hVdef
  set F := Function.uncurry V with hF
  have hVc : Continuous fun q : ℝ × Pt 2 => V q.1 q.2 := (Vpulse_props ν w j).2.1.continuous
  have hnhds : ∀ {s : ℝ}, s ∈ Ioo (0 : ℝ) 1 → Icc (0 : ℝ) 1 ∈ 𝓝 s := fun hs =>
    Icc_mem_nhds hs.1 hs.2
  have hvd : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ x, HasDerivAt (fun r => v r x) (dt 1 v s x) s :=
    fun s hs x => (reg.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt (hnhds hs)
  -- Part 1: the energy estimate on the pulse interval
  have part1 : ∀ t ∈ Ij j, l2sqV (fun x => v t x - V t x) ≤
      l2sqV (v (sj j)) * Real.exp (2 * Λ₀) := by
    have hab : sj j ≤ sj j + δs j := by linarith
    have hIoo : ∀ s ∈ Ioo (sj j) (sj j + δs j), s ∈ Ioo (0 : ℝ) 1 := fun s hs =>
      ⟨((hI ⟨le_rfl, hab⟩).1).trans_lt hs.1, hs.2.trans_le (hI ⟨hab, le_rfl⟩).2⟩
    have key := perturbation_energy hab ν hν.le v (fun s x => v s x - V s x)
      (fun s x => dt 1 v s x - fderiv ℝ F (s, x) (1, 0)) V (fun s x => p s x - Ppulse ν w j s x)
      (gradSup ν w j)
      ((reg.continuousOn.mono (prod_mono hI subset_rfl)).sub hVc.continuousOn)
      (((reg.holder_dt.continuousOn hβ0).mono (prod_mono hI subset_rfl)).sub
        (continuous_Vpulse_dt ν w j).continuousOn)
      (fun s hs x => (hvd s (hIoo s hs) x).sub (Vpulse_hasDerivAt' ν w j s x))
      (fun s hs => by
        have hs1 := Ioo_subset_Icc_self (hIoo s hs)
        have hvs := reg.smooth_x s hs1
        refine ⟨hvs.of_le (by norm_num), hv.periodic_u s hs1, hv.div_free s hs1,
          hvs.sub (Vpulse_slice_C2 ν w j s), fun x n => ?_, fun x => ?_,
          (regp.smooth_x s hs1).sub (Ppulse_C1 ν w j s), fun x n => ?_,
          (Vpulse_slice_C2 ν w j s).of_le (by norm_num), fun x => le_gradSup ν w hj s x⟩
        · simp only [hv.periodic_u s hs1 x n]
          rw [show V s (x + intVec n) = V s x from (Vpulse_props ν w j).1 s x n]
        · rw [divergence_sub_fun _ _ (hvs.differentiable (by norm_num))
            ((Vpulse_slice_C2 ν w j s).differentiable (by norm_num)), hv.div_free s hs1,
            (Vpulse_props ν w j).2.2 s x, sub_zero]
        · simp only [hv.periodic_p s hs1 x n, Ppulse_periodic ν w j s x n])
      (fun s hs x => by
        have hs1 := Ioo_subset_Icc_self (hIoo s hs)
        have hsI : s ∈ Ij j := Ioo_subset_Icc_self hs
        have hvs := reg.smooth_x s hs1
        have hVs := Vpulse_slice_C2 ν w j s
        have h1 := hv.eqn s hs1 x
        have h2 := Vpulse_equation ν w j hj s hsI x
        rw [(Vpulse_hasDerivAt' ν w j s x).deriv] at h2
        rw [conv_sub_right _ _ _ (hvs.differentiable (by norm_num)) (hVs.differentiable
          (by norm_num)), conv_sub_left, grad_sub_fun _ _
          ((regp.smooth_x s hs1).differentiable (by norm_num))
          ((Ppulse_C1 ν w j s).differentiable (by norm_num)), lap_sub_fun _ _ hvs hVs, smul_sub]
        rw [show dt 1 v s x - fderiv ℝ F (s, x) (1, 0) + (conv (v s) (v s) x - conv (v s) (V s) x) +
            (conv (v s) (V s) x - conv (V s) (V s) x) + (grad (p s) x - grad (Ppulse ν w j s) x) =
            (dt 1 v s x + conv (v s) (v s) x + grad (p s) x) -
            (fderiv ℝ F (s, x) (1, 0) + conv (V s) (V s) x + grad (Ppulse ν w j s) x) by abel,
          h1, h2]
        abel)
      (continuous_gradSup ν w hj).continuousOn
    intro t ht
    have h := key t ht
    simp only [hV0, Pi.zero_apply, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (setIntegral_nonneg measurableSet_Icc
      fun x _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
    exact Real.exp_le_exp.2 (by linarith [integral_gradSup_le ν hν w hj t ht])
  have part1' : ∀ t ∈ Ij j, l2V (v t - V t) ≤ Real.exp Λ₀ * l2V (v (sj j)) := by
    intro t ht
    unfold l2V
    have h := Real.sqrt_le_sqrt (part1 t ht)
    rw [Real.sqrt_mul (show 0 ≤ l2sqV (v (sj j)) from setIntegral_nonneg measurableSet_Icc
      fun x _ => Finset.sum_nonneg fun _ _ => sq_nonneg _), show 2 * Λ₀ = Λ₀ + Λ₀ by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le, mul_comm] at h
    exact h
  refine ⟨part1', ?_⟩
  -- Part 2: no forcing on the quiet interval
  have h2 := quiet_energy_le ν hν w v p hv j hj (sj (j + 1)) ⟨(sj_lt_succ j hj).le, le_rfl⟩
  have hvb : Continuous (v (sj j + δs j)) := (reg.smooth_x _ (hI ⟨by linarith, le_rfl⟩)).continuous
  have htri := sqrt_l2sqV_add_le (fun x => v (sj j + δs j) x - V (sj j + δs j) x)
    (V (sj j + δs j)) (hvb.sub (Vpulse_slice_C2 ν w j _).continuous)
    (Vpulse_slice_C2 ν w j _).continuous
  simp only [sub_add_cancel] at htri
  have hp1 := part1' (sj j + δs j) ⟨by linarith, le_rfl⟩
  unfold l2V at hp1 ⊢
  calc Real.sqrt (l2sqV (v (sj (j + 1)))) ≤ Real.sqrt (l2sqV (v (sj j + δs j))) :=
        Real.sqrt_le_sqrt h2
    _ ≤ Real.sqrt (l2sqV fun x => v (sj j + δs j) x - V (sj j + δs j) x) +
        Real.sqrt (l2sqV (V (sj j + δs j))) := htri
    _ ≤ _ := by gcongr; exact hp1

lemma Apulse_pos (ν : ℝ) (hν : 0 < ν) (j : ℕ) (hj : 1 ≤ j) : 0 < Apulse ν j := by
  unfold Apulse kk δs τstar
  have : (0:ℝ) < j := by exact_mod_cast hj
  have := qq_ge
  positivity

lemma Apulse_shift (ν : ℝ) (hν : 0 < ν) (i a : ℕ) (hi : 1 ≤ i) :
    Apulse ν i * ((qq : ℝ) ^ (2 * M₀ + 1)) ^ a ≤ ((1 : ℝ) + a) ^ (3 * M₀) * Apulse ν (i + a) := by
  unfold Apulse kk δs
  have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hτ : (0:ℝ) < τstar := by unfold τstar; norm_num
  have key : (τstar / (i:ℝ) ^ 3) ^ M₀ ≤ ((1:ℝ) + a) ^ (3 * M₀) * (τstar / ((i + a : ℕ) : ℝ) ^ 3) ^ M₀ := by
    rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [← mul_div_assoc, le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 : ((i + a : ℕ) : ℝ) ≤ (1 + a) * i := by push_cast; nlinarith
    have h2 : ((i + a : ℕ) : ℝ) ^ 3 ≤ ((1 + a) * i) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    rw [mul_pow] at h2
    nlinarith
  have hq : (0:ℝ) < qq := by have := qq_ge; positivity
  calc ν ^ (M₀ + 1) * ((qq:ℝ) ^ i) ^ (2 * M₀ + 1) * (τstar / (i:ℝ) ^ 3) ^ M₀ *
        ((qq : ℝ) ^ (2 * M₀ + 1)) ^ a
      = ν ^ (M₀ + 1) * ((qq:ℝ) ^ (i + a)) ^ (2 * M₀ + 1) * (τstar / (i:ℝ) ^ 3) ^ M₀ := by
        rw [← pow_mul, ← pow_mul, ← pow_mul,
          show (i + a) * (2 * M₀ + 1) = i * (2 * M₀ + 1) + (2 * M₀ + 1) * a by ring, pow_add]
        ring
    _ ≤ ν ^ (M₀ + 1) * ((qq:ℝ) ^ (i + a)) ^ (2 * M₀ + 1) *
        (((1 : ℝ) + a) ^ (3 * M₀) * (τstar / ((i + a : ℕ) : ℝ) ^ 3) ^ M₀) := by gcongr
    _ = _ := by ring


lemma Λ₀_nonneg : 0 ≤ Λ₀ := by unfold Λ₀; have := S₀_nonneg 1; linarith

/-- The geometric ratio `e^Λ q^{-(2M+1)}`. -/
def resetRatio : ℝ := Real.exp Λ₀ / (qq : ℝ) ^ (2 * M₀ + 1)

lemma resetRatio_pos : 0 < resetRatio := by
  unfold resetRatio; have := qq_ge; positivity

lemma resetRatio_lt_one : resetRatio < 1 := by
  unfold resetRatio
  have hq : (qq : ℝ) = 3 := by norm_num [qq]
  rw [div_lt_one (by rw [hq]; positivity), hq]
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hM : Λ₀ / Real.log 3 < (M₀ : ℝ) := by
    unfold M₀; push_cast
    linarith [Nat.le_ceil (Λ₀ / Real.log 3)]
  have h1 : Λ₀ < ((2 * M₀ + 1 : ℕ) : ℝ) * Real.log 3 := by
    rw [div_lt_iff₀ hl] at hM; push_cast
    nlinarith
  calc Real.exp Λ₀ < Real.exp (((2 * M₀ + 1 : ℕ) : ℝ) * Real.log 3) := Real.exp_lt_exp.2 h1
    _ = 3 ^ (2 * M₀ + 1) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

lemma summable_reset :
    Summable fun a : ℕ => ((1 : ℝ) + a) ^ (3 * M₀) * resetRatio ^ a := by
  have hr := resetRatio_pos
  have h := summable_pow_mul_geometric_of_norm_lt_one (3 * M₀)
    (show ‖resetRatio‖ < 1 by rw [Real.norm_of_nonneg hr.le]; exact resetRatio_lt_one)
  have h' := ((summable_nat_add_iff 1).2 h).mul_left resetRatio⁻¹
  refine h'.congr fun a => ?_
  push_cast
  rw [pow_succ]; field_simp; ring


lemma reset_term_le (ν : ℝ) (hν : 0 < ν) (j a : ℕ) (ha : a < j) :
    Real.exp Λ₀ ^ a * Apulse ν (j - a) ≤ ((1 : ℝ) + a) ^ (3 * M₀) * resetRatio ^ a * Apulse ν j := by
  have h := Apulse_shift ν hν (j - a) a (by omega)
  rw [Nat.sub_add_cancel ha.le] at h
  have hQ : (0:ℝ) < (qq : ℝ) ^ (2 * M₀ + 1) := by have := qq_ge; positivity
  have e : Real.exp Λ₀ ^ a = resetRatio ^ a * ((qq : ℝ) ^ (2 * M₀ + 1)) ^ a := by
    unfold resetRatio; rw [div_pow, div_mul_cancel₀ _ (pow_pos hQ a).ne']
  rw [e]
  have hr := resetRatio_pos
  calc resetRatio ^ a * ((qq : ℝ) ^ (2 * M₀ + 1)) ^ a * Apulse ν (j - a)
      = resetRatio ^ a * (Apulse ν (j - a) * ((qq : ℝ) ^ (2 * M₀ + 1)) ^ a) := by ring
    _ ≤ resetRatio ^ a * (((1 : ℝ) + a) ^ (3 * M₀) * Apulse ν j) := by gcongr
    _ = _ := by ring

/-- **Lemma 5.4** (global reset).  `E_{j+1}^ν ≤ C_M A_j^ν` for every `ν > 0`, `j ≥ 1`, `ω`. -/
theorem global_reset : ∃ C : ℝ, ∀ ν : ℝ, 0 < ν → ∀ (w : Phase) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ), IsClassicalNS 1 ν 0 (gForce w) v p → ∀ j : ℕ, 1 ≤ j →
    l2V (v (sj (j + 1))) ≤ C * Apulse ν j := by
  obtain ⟨C1, hC1⟩ := isolated_pulse_properties
  set C1' := max C1 0 with hC1'
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  set S := ∑' a : ℕ, ((1 : ℝ) + a) ^ (3 * M₀) * resetRatio ^ a with hS
  refine ⟨C1' * S, fun ν hν w v p hv => ?_⟩
  have hr : ∀ j, 1 ≤ j → l2V (Vpulse ν w j (sj j + δs j)) ≤ C1' * Apulse ν j := fun j hj =>
    (hC1 ν hν j hj w).2.2.2.2.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Apulse_pos ν hν j hj).le)
  have hE1 : l2V (v (sj 1)) = 0 := by
    rw [show sj 1 = 0 by simp [sj], hv.init]; simp [l2V, l2sqV]
  have hiter : ∀ j, l2V (v (sj (j + 1))) ≤
      C1' * ∑ a ∈ Finset.range j, Real.exp Λ₀ ^ a * Apulse ν (j - a) := by
    intro j
    induction j with
    | zero => simp [hE1]
    | succ j ih =>
      have hs := (single_stage_stability ν hν w v p hv (j + 1) (by omega)).2
      rw [Finset.sum_range_succ']
      have e : ∀ a ∈ Finset.range j, Real.exp Λ₀ ^ (a + 1) * Apulse ν (j + 1 - (a + 1)) =
          Real.exp Λ₀ * (Real.exp Λ₀ ^ a * Apulse ν (j - a)) := fun a _ => by
        rw [Nat.add_sub_add_right, pow_succ]; ring
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      have := hr (j + 1) (by omega)
      have hexp := (Real.exp_pos Λ₀).le
      calc l2V (v (sj (j + 1 + 1)))
          ≤ Real.exp Λ₀ * l2V (v (sj (j + 1))) + C1' * Apulse ν (j + 1) := by linarith
        _ ≤ Real.exp Λ₀ * (C1' * ∑ a ∈ Finset.range j, Real.exp Λ₀ ^ a * Apulse ν (j - a)) +
            C1' * Apulse ν (j + 1) := by gcongr
        _ = _ := by simp; ring
  intro j hj
  refine (hiter j).trans ?_
  have hsum : ∑ a ∈ Finset.range j, Real.exp Λ₀ ^ a * Apulse ν (j - a) ≤ S * Apulse ν j := by
    calc ∑ a ∈ Finset.range j, Real.exp Λ₀ ^ a * Apulse ν (j - a)
        ≤ ∑ a ∈ Finset.range j, ((1 : ℝ) + a) ^ (3 * M₀) * resetRatio ^ a * Apulse ν j :=
          Finset.sum_le_sum fun a ha => reset_term_le ν hν j a (Finset.mem_range.1 ha)
      _ = (∑ a ∈ Finset.range j, ((1 : ℝ) + a) ^ (3 * M₀) * resetRatio ^ a) * Apulse ν j :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ S * Apulse ν j := by
          gcongr
          · exact (Apulse_pos ν hν j hj).le
          · exact summable_reset.sum_le_tsum _ fun a _ => by
              have := resetRatio_pos; positivity
  calc C1' * ∑ a ∈ Finset.range j, Real.exp Λ₀ ^ a * Apulse ν (j - a) ≤ C1' * (S * Apulse ν j) :=
        mul_le_mul_of_nonneg_left hsum hC1'0
    _ = _ := by ring

open Classical in
/-- The comparison drift `v̄_ω^ν`: `V_j^ν` on `I_j` and `0` elsewhere (Definition 5.5). -/
def vbar (ν : ℝ) (w : Phase) (t : ℝ) (x : Pt 2) : Pt 2 :=
  ∑' j : ℕ, if 1 ≤ j ∧ t ∈ Ij j then Vpulse ν w j t x else 0

/-- `θ̄` is the comparison scalar on `[0,T_N]` (Definition 5.5): it starts from `θ₀` and is
obtained by successively solving the advection–diffusion equation with drift `V_j^{ν_N}` on
`I_j` and the heat equation on `J_j`, `1 ≤ j ≤ N`, matching values at the endpoints. -/
def IsComparisonScalar (N : ℕ) (w : Phase) (θ₀ : Pt 2 → ℝ) (θb : ℝ → Pt 2 → ℝ) : Prop :=
  θb 0 = θ₀ ∧ ∀ j, 1 ≤ j → j ≤ N →
    IsClassicalScalar (δs j) (nuN N) (fun t => Vpulse (nuN N) w j (sj j + t)) (θb (sj j))
      (fun t => θb (sj j + t)) ∧
    IsClassicalScalar (ηs j) (nuN N) (fun _ _ => 0) (θb (sj j + δs j))
      (fun t => θb (sj j + δs j + t))

/-- On the pulse stage `I_j`, in local time, the isolated pulse is a rescaled eigenfield. -/
lemma vpulse_stage_eq (ν : ℝ) (w : Phase) (j : ℕ) :
    (fun t x => Vpulse ν w j (sj j + t) x) = fun t x => (1 / (kk j * δs j)) •
      eField (dampedCoef cf₀ (muNu ν j) (w j) (t / δs j)) (((qq ^ j : ℕ) : ℝ) • x - (w j).2) := by
  funext t x
  simp only [Vpulse, VpulseB, dampedB_eq, add_sub_cancel_left, kk, Nat.cast_pow]

lemma vpulse_stage_props (ν : ℝ) (w : Phase) (j : ℕ) :
    (∀ t, IsPeriodic (Vpulse ν w j (sj j + t))) ∧
    ContDiff ℝ 2 (Function.uncurry fun t => Vpulse ν w j (sj j + t)) ∧
    (∀ t x, divergence (Vpulse ν w j (sj j + t)) x = 0) := by
  have e := vpulse_stage_eq ν w j
  have h := trigDrift_props (fun t => dampedCoef cf₀ (muNu ν j) (w j) (t / δs j))
    ((contDiff_dampedCoef cf₀ (muNu ν j) (w j) 2).comp (contDiff_id.div_const _))
    (1 / (kk j * δs j)) (qq ^ j) (w j).2
  have e' : (fun t => Vpulse ν w j (sj j + t)) = fun t x => (1 / (kk j * δs j)) •
      eField (dampedCoef cf₀ (muNu ν j) (w j) (t / δs j)) (((qq ^ j : ℕ) : ℝ) • x - (w j).2) :=
    e
  have hV : ∀ t, Vpulse ν w j (sj j + t) = fun x => (1 / (kk j * δs j)) •
      eField (dampedCoef cf₀ (muNu ν j) (w j) (t / δs j)) (((qq ^ j : ℕ) : ℝ) • x - (w j).2) :=
    fun t => congrFun e' t
  exact ⟨fun t => by rw [hV t]; exact h.1 t, by rw [e']; exact h.2.1,
    fun t x => by rw [hV t]; exact h.2.2 t x⟩

/-- **Lemma 5.6** (comparison scalar).  The comparison scalar exists and is unique on
`[0,T_N]`, and it satisfies the maximum principle and the energy identity there. -/
theorem comparison_scalar_identities (hSc : ExternalScalar) (N : ℕ) (hN : 1 ≤ N) (w : Phase)
    (θ₀ : Pt 2 → ℝ) (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀p : IsPeriodic θ₀) :
    (∃ θb, IsComparisonScalar N w θ₀ θb) ∧
    (∀ θb θb', IsComparisonScalar N w θ₀ θb → IsComparisonScalar N w θ₀ θb' →
      ∀ t ∈ Icc 0 (TN N), θb t = θb' t) ∧
    ∀ θb, IsComparisonScalar N w θ₀ θb →
      (∀ M, (∀ x, |θ₀ x| ≤ M) → ∀ t ∈ Icc 0 (TN N), ∀ x, |θb t x| ≤ M) ∧
      ∀ t ∈ Icc 0 (TN N), l2sq (θb t) / 2 + dissipation (nuN N) θb t = l2sq θ₀ / 2 := by
  have hν := viscosity_properties.2.2.1 N hN
  have hD := fun j => vpulse_stage_props (nuN N) w j
  have hC1 : ∀ j t, ContDiff ℝ 1 (Vpulse (nuN N) w j (sj j + t)) := fun j t =>
    ((hD j).2.1.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  refine ⟨?_, fun θb θb' h h' => staged_unique hν.le h h', fun θb h =>
    ⟨fun M hM => staged_abs_le hν.le h hM, staged_energy (fun j _ _ =>
      ⟨fun t _ => (hD j).1 t, fun t _ => hC1 j t, fun t _ => (hD j).2.2 t⟩) h⟩⟩
  exact staged_exists hSc N hν (fun j t => Vpulse (nuN N) w j (sj j + t))
    (fun j hj _ => ⟨fun t _ => (hD j).1 t,
      parabolicC01_of_contDiff (δs_pos j hj).le (by norm_num) (by norm_num) _ (hD j).2.1 (hD j).1,
      fun t _ => (hD j).2.2 t⟩) θ₀ hθ₀ hθ₀p

end AnomDiss
