module

public import RequestProject.Shears

/-!
# Lemma 2.5: the negative moment bound

For every integer `q ≥ 3` there are `σ ∈ (0,1)` and `L ≥ 1` with
`sup_{|e|=1} 𝔼|Q_L ⋯ Q_1 e|^{-σ} ≤ 1/(128 q^σ)`.

The proof follows the paper: with `A = DF⁻¹(Z)ᵀ` and `𝒥` the rotation,
`|Ae|²|A𝒥⁻¹e|² = 1 + φ(Z,e)²` for unit `e`, where `φ(Z,e) = ⟨Ae, A𝒥⁻¹e⟩`, so that
`𝔼_ι log|Qe| = ¼ log(1 + φ²) ≥ 0`.  The quantity `φ(·,e)` cannot vanish at both fixed points
`(0,0)` and `(1/2,0)` of `F`, which gives a uniform positive drift; a second-order Taylor
bound and conditioning on the preceding matrices finish the argument.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix

noncomputable section

namespace AnomDiss

/-- `φ(Z,e) = ⟨A(Z)e, A(Z)𝒥⁻¹e⟩`. -/
def phiQ (Z e : Pt 2) : ℝ := dot (matA Z *ᵥ e) (matA Z *ᵥ (matJinv *ᵥ e))

/-- `g(e) = ∫_{𝕋²} log(1 + φ(Z,e)²) dZ`, four times the drift `𝔼 log|Qe|` for unit `e`. -/
def gQ (e : Pt 2) : ℝ := ∫ Z in cell 2, Real.log (1 + phiQ Z e ^ 2)

/-! ### Linear algebra -/

lemma hasFDerivAt_mapFinv (x : Pt 2) :
    HasFDerivAt mapFinv
      (matCLM (!![1, -Real.cos (2 * π * shearVinv (shearH (shearV x)) 1); 0, 1] *
        (!![1, 0; -Real.cos (2 * π * shearH (shearV x) 0), 1] *
        (!![1, Real.cos (2 * π * shearV x 1); 0, 1] *
        !![1, 0; Real.cos (2 * π * x 0), 1])))) x := by
  have h := (hasFDerivAt_shearHinv _).comp x ((hasFDerivAt_shearVinv _).comp x
    ((hasFDerivAt_shearH _).comp x (hasFDerivAt_shearV x)))
  simp only [matCLM_mul] at h
  exact h

lemma det_matA (Z : Pt 2) : (matA Z).det = 1 := by
  rw [matA, Matrix.det_transpose, jac_eq_of_hasFDerivAt (hasFDerivAt_mapFinv Z),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fin_two_of]

/-- `DF⁻¹(0,0) = C₀⁻¹`. -/
lemma jac_mapFinv_zero : jac mapFinv ![0, 0] = !![3, 1; -1, 0] := by
  have hH0 : shearH ![0, 0] = ![0, 0] := by simp [shearH]
  have hV0 : shearV ![0, 0] = ![0, 0] := by simp [shearV]
  have hVi0 : shearVinv ![0, 0] = ![0, 0] := by simp [shearVinv]
  rw [jac_eq_of_hasFDerivAt (hasFDerivAt_mapFinv _), hV0, hH0, hVi0]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `DF⁻¹(1/2,0) = C₁⁻¹`. -/
lemma jac_mapFinv_half : jac mapFinv ![1 / 2, 0] = !![1, -1; -1, 2] := by
  have hπ1 : 2 * π * (1 / 2) = π := by ring
  have hπ2 : 2 * π * 2⁻¹ = π := by ring
  have hc : Real.cos (2 * π * (1 / 2)) = -1 := by rw [hπ1, Real.cos_pi]
  have hH1 : shearH ![1 / 2, 0] = ![1 / 2, 0] := by simp [shearH]
  have hV1 : shearV ![1 / 2, 0] = ![1 / 2, 0] := by simp [shearV, hπ2]
  have hVi1 : shearVinv ![1 / 2, 0] = ![1 / 2, 0] := by simp [shearVinv, hπ2]
  rw [jac_eq_of_hasFDerivAt (hasFDerivAt_mapFinv _), hV1, hH1, hVi1]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, hc]

lemma continuous_matA : Continuous matA := continuous_jac_mapFinv.matrix_transpose

lemma matA_periodic (Z : Pt 2) (n : Fin 2 → ℤ) : matA (Z + intVec n) = matA Z := by
  simp [matA, jac_mapFinv_periodic]

lemma matA_frob_bdd : ∃ N : ℝ, 1 ≤ N ∧ ∀ Z, ∑ i, ∑ j, matA Z i j ^ 2 ≤ N := by
  obtain ⟨C, hC⟩ := periodic_bdd (fun Z => matEntries (matA Z))
    (continuous_pi fun i => continuous_pi fun j => continuous_matA.matrix_elem i j)
    (fun Z n => by simp [matA_periodic])
  refine ⟨max 1 (4 * C ^ 2), le_max_left _ _, fun Z => ?_⟩
  have hb : ∀ i j, matA Z i j ^ 2 ≤ C ^ 2 := by
    intro i j
    have h1 : ‖matA Z i j‖ ≤ C := by
      have := hC Z
      exact ((norm_le_pi_norm (matEntries (matA Z) i) j).trans
        (norm_le_pi_norm (matEntries (matA Z)) i)).trans this
    have h0 : 0 ≤ ‖matA Z i j‖ := norm_nonneg _
    rw [Real.norm_eq_abs] at h1 h0
    nlinarith [sq_abs (matA Z i j), abs_nonneg (matA Z i j)]
  refine le_trans ?_ (le_max_right _ _)
  simp only [Fin.sum_univ_two]
  linarith [hb 0 0, hb 0 1, hb 1 0, hb 1 1]

lemma euclNorm_sq (v : Pt 2) : euclNorm v ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  unfold euclNorm
  rw [Real.sq_sqrt (by positivity), Fin.sum_univ_two]

lemma euclNorm_nonneg' (v : Pt 2) : 0 ≤ euclNorm v := Real.sqrt_nonneg _

lemma euclNorm_continuous : Continuous (euclNorm : Pt 2 → ℝ) := by
  unfold euclNorm; fun_prop

lemma euclNorm_smul' (c : ℝ) (v : Pt 2) : euclNorm (c • v) = |c| * euclNorm v := by
  unfold euclNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  simp [mul_pow]; ring

lemma euclNorm_mulVec_sq_le (A : Matrix (Fin 2) (Fin 2) ℝ) (e : Pt 2) :
    euclNorm (A *ᵥ e) ^ 2 ≤ (∑ i, ∑ j, A i j ^ 2) * euclNorm e ^ 2 := by
  rw [euclNorm_sq, euclNorm_sq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith [sq_nonneg (A 0 0 * e 1 - A 0 1 * e 0), sq_nonneg (A 1 0 * e 1 - A 1 1 * e 0)]

lemma euclNorm_sq_le_mulVec (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1) (e : Pt 2) :
    euclNorm e ^ 2 ≤ (∑ i, ∑ j, A i j ^ 2) * euclNorm (A *ᵥ e) ^ 2 := by
  rw [euclNorm_sq, euclNorm_sq]
  rw [Matrix.det_fin_two] at hA
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  set u0 := A 0 0 * e 0 + A 0 1 * e 1
  set u1 := A 1 0 * e 0 + A 1 1 * e 1
  have h0 : e 0 = A 1 1 * u0 - A 0 1 * u1 := by
    simp only [u0, u1]; linear_combination (-e 0) * hA
  have h1 : e 1 = -A 1 0 * u0 + A 0 0 * u1 := by
    simp only [u0, u1]; linear_combination (-e 1) * hA
  rw [h0, h1]
  nlinarith [sq_nonneg (A 1 1 * u1 + A 0 1 * u0), sq_nonneg (A 1 0 * u1 + A 0 0 * u0)]

lemma lagrange_matA (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1) (e : Pt 2) :
    euclNorm (A *ᵥ e) ^ 2 * euclNorm (A *ᵥ (matJinv *ᵥ e)) ^ 2 =
      euclNorm e ^ 4 + dot (A *ᵥ e) (A *ᵥ (matJinv *ᵥ e)) ^ 2 := by
  have h4 : euclNorm e ^ 4 = (euclNorm e ^ 2) ^ 2 := by ring
  rw [h4, euclNorm_sq, euclNorm_sq, euclNorm_sq]
  rw [Matrix.det_fin_two] at hA
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, dot, matJinv]
  simp
  linear_combination (A 0 0 * A 1 1 - A 0 1 * A 1 0 + 1) * (e 0 ^ 2 + e 1 ^ 2) ^ 2 * hA

lemma euclNorm_matJ (v : Pt 2) : euclNorm (matJ *ᵥ v) = euclNorm v := by
  unfold euclNorm; congr 1
  simp [matJ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

lemma euclNorm_matJinv (v : Pt 2) : euclNorm (matJinv *ᵥ v) = euclNorm v := by
  unfold euclNorm; congr 1
  simp [matJinv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

lemma matQ_false_mulVec (Z e : Pt 2) : matQ (false, Z) *ᵥ e = matA Z *ᵥ e := by
  simp [matQ]

lemma euclNorm_matQ_true (Z e : Pt 2) :
    euclNorm (matQ (true, Z) *ᵥ e) = euclNorm (matA Z *ᵥ (matJinv *ᵥ e)) := by
  simp only [matQ, if_true, ← Matrix.mulVec_mulVec]
  exact euclNorm_matJ _

/-! ### The drift is positive -/

lemma phiQ_fixed_ne_zero (e : Pt 2) (he : e ≠ 0) :
    phiQ ![0, 0] e ≠ 0 ∨ phiQ ![1 / 2, 0] e ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h0, h1⟩ := h
  simp only [phiQ, matA, jac_mapFinv_zero, jac_mapFinv_half, dot, matJinv, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h0 h1
  simp at h0 h1
  apply he
  have hab : e 0 * e 1 = 0 := by nlinarith
  have hsq : e 0 ^ 2 = e 1 ^ 2 := by nlinarith
  have ha : e 0 = 0 := by
    rcases mul_eq_zero.1 hab with h | h
    · exact h
    · rw [h] at hsq; nlinarith
  have hb : e 1 = 0 := by rw [ha] at hsq; nlinarith
  ext i; fin_cases i <;> simp [ha, hb]

lemma continuous_phiQ : Continuous fun p : Pt 2 × Pt 2 => phiQ p.1 p.2 := by
  have hA : ∀ i j, Continuous fun p : Pt 2 × Pt 2 => matA p.1 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_matA.comp continuous_fst))
  have he : ∀ i, Continuous fun p : Pt 2 × Pt 2 => p.2 i := fun i =>
    (continuous_apply i).comp continuous_snd
  simp only [phiQ, dot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, matJinv]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have := hA 0 0; have := hA 0 1; have := hA 1 0; have := hA 1 1
  have := he 0; have := he 1
  fun_prop

lemma gQ_continuous : Continuous gQ := by
  have h : Continuous (Function.uncurry fun (e Z : Pt 2) => Real.log (1 + phiQ Z e ^ 2)) := by
    refine Continuous.log ?_ (fun p => by positivity)
    exact continuous_const.add ((continuous_phiQ.comp continuous_swap).pow 2)
  exact continuous_parametric_integral_of_continuous h isCompact_Icc

lemma integral_cell_pos_of_continuous (f : Pt 2 → ℝ) (hf : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (c : Pt 2) (hc : ∀ i, c i ∈ Ioo (0 : ℝ) 1) (hpos : 0 < f c) :
    0 < ∫ z in cell 2, f z := by
  have hint : Integrable f (volume.restrict (cell 2)) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_pos_iff_support_of_nonneg h0 hint]
  set U : Set (Pt 2) := Function.support f ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) 1)
  have hU : IsOpen U := (isOpen_ne_fun hf continuous_const).inter
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
  have hcU : c ∈ U := ⟨hpos.ne', fun i _ => hc i⟩
  have hUsub : U ⊆ Function.support f ∩ cell 2 := by
    intro x hx
    refine ⟨hx.1, fun i => (hx.2 i (mem_univ _)).1.le, fun i => (hx.2 i (mem_univ _)).2.le⟩
  calc (0 : ℝ≥0∞) < volume U := hU.measure_pos _ ⟨c, hcU⟩
    _ ≤ volume (Function.support f ∩ cell 2) := measure_mono hUsub
    _ ≤ volume.restrict (cell 2) (Function.support f) := Measure.le_restrict_apply _ _

lemma integral_cell_sub (h : Pt 2 → ℝ) (hc : Continuous h) (hp : IsPeriodic h) (x : Pt 2) :
    ∫ z in cell 2, h z = ∫ z in cell 2, h (x - z) := by
  have := congrArg (fun μ : Measure ℝ => ∫ y, y ∂μ) (map_cell_sub_left h hc hp x)
  rw [integral_map (show AEMeasurable (fun z => h (x - z)) _ from
      (hc.comp (continuous_const.sub continuous_id)).aemeasurable)
      measurable_id'.aestronglyMeasurable,
    integral_map hc.aemeasurable measurable_id'.aestronglyMeasurable] at this
  exact this.symm

lemma gQ_pos (e : Pt 2) (he : e ≠ 0) : 0 < gQ e := by
  set h : Pt 2 → ℝ := fun Z => Real.log (1 + phiQ Z e ^ 2) with hh
  have hc : Continuous h := by
    refine Continuous.log ?_ (fun p => by positivity)
    exact continuous_const.add
      ((continuous_phiQ.comp (continuous_id.prodMk continuous_const)).pow 2)
  have hp : IsPeriodic h := fun Z n => by simp [hh, phiQ, matA_periodic]
  have hpos : ∀ Z, phiQ Z e ≠ 0 → 0 < h Z := fun Z hZ => by
    simp only [hh]
    refine Real.log_pos ?_
    have := pow_pos (abs_pos.2 hZ) 2
    rw [sq_abs] at this
    linarith
  have h0 : ∀ Z, 0 ≤ h Z := fun Z => Real.log_nonneg (by nlinarith [sq_nonneg (phiQ Z e)])
  obtain ⟨Zs, hZs⟩ : ∃ Zs, phiQ Zs e ≠ 0 := by
    rcases phiQ_fixed_ne_zero e he with h' | h'
    · exact ⟨_, h'⟩
    · exact ⟨_, h'⟩
  set c : Pt 2 := ![1 / 2, 1 / 2]
  have e1 : gQ e = ∫ z in cell 2, h (Zs + c - z) := integral_cell_sub h hc hp (Zs + c)
  rw [e1]
  refine integral_cell_pos_of_continuous _ (hc.comp (continuous_const.sub continuous_id))
    (fun z => h0 _) c (fun i => by fin_cases i <;> norm_num [c]) ?_
  simp only [add_sub_cancel_right]
  exact hpos _ hZs

lemma gQ_lower : ∃ d > 0, ∀ e : Pt 2, euclNorm e = 1 → d ≤ gQ e := by
  set S : Set (Pt 2) := {e | euclNorm e = 1}
  have hS : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq euclNorm_continuous
      continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Pt 2)) (r := 1)).subset ?_
    intro e he
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have : e i ^ 2 ≤ ∑ j, e j ^ 2 :=
      Finset.single_le_sum (f := fun j => e j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h1 : ∑ j, e j ^ 2 = 1 := by
      have := he; simp only [S, mem_setOf_eq, euclNorm] at this
      rw [Real.sqrt_eq_one] at this; exact this
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (e i), abs_nonneg (e i)]
  have hne : S.Nonempty := ⟨![1, 0], by simp [S, euclNorm, Fin.sum_univ_two]⟩
  obtain ⟨e0, he0, hmin⟩ := hS.exists_isMinOn hne gQ_continuous.continuousOn
  have he0' : e0 ≠ 0 := by
    rintro rfl; simp [S, euclNorm] at he0
  exact ⟨gQ e0, gQ_pos e0 he0', fun e he => hmin he⟩

/-! ### One step -/

lemma log_norm_bound (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det = 1) (N : ℝ)
    (hN : ∑ i, ∑ j, A i j ^ 2 ≤ N) (e : Pt 2) (he : euclNorm e = 1) :
    0 < euclNorm (A *ᵥ e) ∧ |Real.log (euclNorm (A *ᵥ e))| ≤ Real.log N / 2 := by
  have h1 := euclNorm_mulVec_sq_le A e
  have h2 := euclNorm_sq_le_mulVec A hA e
  rw [he] at h1 h2
  set x := euclNorm (A *ᵥ e)
  have hx0 : 0 ≤ x := euclNorm_nonneg' _
  have hF0 : 0 ≤ ∑ i, ∑ j, A i j ^ 2 := by positivity
  have hxN : x ^ 2 ≤ N := by nlinarith
  have hNx : 1 ≤ N * x ^ 2 := by nlinarith
  have hx : 0 < x := by
    rcases hx0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hNx; simp at hNx; linarith
  have hN0 : 0 < N := by nlinarith
  refine ⟨hx, ?_⟩
  have hlog : Real.log x = Real.log (x ^ 2) / 2 := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog, abs_le]
  have hup : Real.log (x ^ 2) ≤ Real.log N := Real.log_le_log (by positivity) hxN
  have hlo : -Real.log N ≤ Real.log (x ^ 2) := by
    have := Real.log_le_log one_pos hNx
    rw [Real.log_one, Real.log_mul hN0.ne' (by positivity)] at this
    linarith
  constructor <;> linarith

lemma pointwise_taylor (x y φ σ B : ℝ) (hx : 0 < x) (hy : 0 < y) (hxB : |Real.log x| ≤ B)
    (hyB : |Real.log y| ≤ B) (hσ : 0 < σ) (hσB : σ * B ≤ 1) (hxy : x ^ 2 * y ^ 2 = 1 + φ ^ 2) :
    (x ^ (-σ) + y ^ (-σ)) / 2 ≤ 1 - σ / 4 * Real.log (1 + φ ^ 2) + σ ^ 2 * B ^ 2 := by
  have taylor : ∀ u, |Real.log u| ≤ B → 0 < u →
      u ^ (-σ) ≤ 1 - σ * Real.log u + σ ^ 2 * B ^ 2 := by
    intro u hu hu0
    rw [Real.rpow_def_of_pos hu0]
    set t := Real.log u * (-σ)
    have ht : |t| ≤ σ * B := by
      simp only [t, abs_mul, abs_neg, abs_of_pos hσ]; nlinarith [abs_nonneg (Real.log u)]
    have ht1 : |t| ≤ 1 := ht.trans hσB
    have h := Real.abs_exp_sub_one_sub_id_le ht1
    have ht2 : t ^ 2 ≤ σ ^ 2 * B ^ 2 := by
      have := sq_le_sq' (abs_le.1 ht).1 (abs_le.1 ht).2
      nlinarith
    have := (abs_le.1 h).2
    simp only [t] at this ht2 ⊢
    nlinarith
  have hl : Real.log (1 + φ ^ 2) = 2 * Real.log x + 2 * Real.log y := by
    rw [← hxy, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have := taylor x hxB hx
  have := taylor y hyB hy
  rw [hl]
  linarith

lemma single_step_bound (N : ℝ) (hNb : ∀ Z, ∑ i, ∑ j, matA Z i j ^ 2 ≤ N)
    (σ : ℝ) (hσ : 0 < σ) (hσB : σ * (Real.log N / 2) ≤ 1) (e : Pt 2) (he : euclNorm e = 1) :
    ∫⁻ w, ENNReal.ofReal (euclNorm (matQ w *ᵥ e) ^ (-σ)) ∂stepMeasure ≤
      ENNReal.ofReal (1 - σ / 4 * gQ e + σ ^ 2 * (Real.log N / 2) ^ 2) := by
  set B := Real.log N / 2 with hB
  set f : Bool × Pt 2 → ℝ≥0∞ := fun w => ENNReal.ofReal (euclNorm (matQ w *ᵥ e) ^ (-σ)) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ _)
    refine Continuous.measurable ?_
    unfold euclNorm
    have := continuous_matQ_joint
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hfm' : ∀ ι, Measurable fun Z => f (ι, Z) := fun ι => hfm.comp measurable_prodMk_left
  set h : Pt 2 → ℝ := fun Z => (1 + σ ^ 2 * B ^ 2) - σ / 4 * Real.log (1 + phiQ Z e ^ 2) with hh
  have hpt : ∀ Z, (euclNorm (matQ (true, Z) *ᵥ e) ^ (-σ) +
      euclNorm (matQ (false, Z) *ᵥ e) ^ (-σ)) / 2 ≤ h Z := by
    intro Z
    rw [euclNorm_matQ_true, matQ_false_mulVec]
    have he' : euclNorm (matJinv *ᵥ e) = 1 := by rw [euclNorm_matJinv, he]
    obtain ⟨hx, hxB⟩ := log_norm_bound (matA Z) (det_matA Z) N (hNb Z) e he
    obtain ⟨hy, hyB⟩ := log_norm_bound (matA Z) (det_matA Z) N (hNb Z) _ he'
    have hl := lagrange_matA (matA Z) (det_matA Z) e
    rw [he, one_pow] at hl
    have := pointwise_taylor _ _ (phiQ Z e) σ B hx hy hxB hyB hσ hσB hl
    simp only [hh]; linarith
  have hlogc : Continuous fun Z => Real.log (1 + phiQ Z e ^ 2) := by
    refine Continuous.log ?_ (fun p => by positivity)
    exact continuous_const.add
      ((continuous_phiQ.comp (continuous_id.prodMk continuous_const)).pow 2)
  have hlogint : Integrable (fun Z => Real.log (1 + phiQ Z e ^ 2)) uniformTorus :=
    hlogc.continuousOn.integrableOn_compact isCompact_Icc
  have hint : Integrable h uniformTorus :=
    (integrable_const _).sub (hlogint.const_mul _)
  have hrp : ∀ ι Z, 0 ≤ euclNorm (matQ (ι, Z) *ᵥ e) ^ (-σ) := fun ι Z =>
    Real.rpow_nonneg (euclNorm_nonneg' _) _
  have hh0 : ∀ Z, 0 ≤ h Z := fun Z => le_trans
    (div_nonneg (add_nonneg (hrp true Z) (hrp false Z)) two_pos.le) (hpt Z)
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]; simp
  calc ∫⁻ w, f w ∂stepMeasure
      = ∫⁻ ι, ∫⁻ Z, f (ι, Z) ∂uniformTorus ∂uniformBool := by
        rw [stepMeasure, lintegral_prod _ hfm.aemeasurable]
    _ = 2⁻¹ * ∫⁻ Z, f (true, Z) ∂uniformTorus + 2⁻¹ * ∫⁻ Z, f (false, Z) ∂uniformTorus := by
        rw [lintegral_fintype]; simp [uniformBool, mul_comm]
    _ = ∫⁻ Z, (2⁻¹ * f (true, Z) + 2⁻¹ * f (false, Z)) ∂uniformTorus := by
        rw [lintegral_add_left ((hfm' true).const_mul _), lintegral_const_mul _ (hfm' true),
          lintegral_const_mul _ (hfm' false)]
    _ ≤ ∫⁻ Z, ENNReal.ofReal (h Z) ∂uniformTorus := by
        refine lintegral_mono fun Z => ?_
        simp only [hf]
        rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (hrp true Z))
            (mul_nonneg (by norm_num) (hrp false Z))]
        refine ENNReal.ofReal_le_ofReal ?_
        linarith [hpt Z]
    _ = ENNReal.ofReal (∫ Z, h Z ∂uniformTorus) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hh0)).symm
    _ = ENNReal.ofReal (1 - σ / 4 * gQ e + σ ^ 2 * B ^ 2) := by
        congr 1
        simp only [hh]
        rw [integral_sub (integrable_const _) (hlogint.const_mul _), integral_const,
          integral_const_mul]
        simp only [probReal_univ, one_smul]
        unfold gQ uniformTorus
        ring

lemma euclNorm_eq_zero_iff' (v : Pt 2) : euclNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h2 := euclNorm_sq v
    rw [h] at h2
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    ext i; fin_cases i <;> simp [h0, h1]
  · rintro rfl; simp [euclNorm]

lemma single_step_homog (σ r : ℝ) (hσ : 0 < σ)
    (h : ∀ e : Pt 2, euclNorm e = 1 →
      ∫⁻ w, ENNReal.ofReal (euclNorm (matQ w *ᵥ e) ^ (-σ)) ∂stepMeasure ≤ ENNReal.ofReal r)
    (v : Pt 2) :
    ∫⁻ w, ENNReal.ofReal (euclNorm (matQ w *ᵥ v) ^ (-σ)) ∂stepMeasure ≤
      ENNReal.ofReal r * ENNReal.ofReal (euclNorm v ^ (-σ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [Matrix.mulVec_zero, euclNorm, Real.zero_rpow (neg_ne_zero.2 hσ.ne')]
  set s := euclNorm v with hsdef
  have hs : 0 < s := lt_of_le_of_ne (euclNorm_nonneg' v)
    (fun h0 => hv ((euclNorm_eq_zero_iff' v).1 h0.symm))
  set e := s⁻¹ • v with hedef
  have he : euclNorm e = 1 := by
    rw [hedef, euclNorm_smul', abs_inv, abs_of_pos hs, inv_mul_cancel₀ hs.ne']
  have hv' : v = s • e := by simp [hedef, smul_smul, mul_inv_cancel₀ hs.ne']
  have key : ∀ w, ENNReal.ofReal (euclNorm (matQ w *ᵥ v) ^ (-σ)) =
      ENNReal.ofReal (s ^ (-σ)) * ENNReal.ofReal (euclNorm (matQ w *ᵥ e) ^ (-σ)) := by
    intro w
    conv_lhs => rw [hv']
    rw [Matrix.mulVec_smul, euclNorm_smul', abs_of_pos hs,
      Real.mul_rpow hs.le (euclNorm_nonneg' _), ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
  simp_rw [key]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm]
  gcongr
  exact h e he

/-! ### Iteration -/

lemma prodQ_cons {L : ℕ} (a : Bool × Pt 2) (t : Fin L → Bool × Pt 2) :
    prodQ (Fin.cons a t : Fin (L + 1) → Bool × Pt 2) = prodQ t * matQ a := by
  simp [prodQ, List.ofFn_succ, List.prod_append]

lemma measurable_negpow (σ : ℝ) (L : ℕ) (v : Pt 2) :
    Measurable fun w : Fin L → Bool × Pt 2 =>
      ENNReal.ofReal (euclNorm (prodQ w *ᵥ v) ^ (-σ)) := by
  refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ _)
  refine Continuous.measurable ?_
  unfold euclNorm
  have := continuous_prodQ L
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

lemma iterate_bound (σ r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ v : Pt 2, ∫⁻ w, ENNReal.ofReal (euclNorm (matQ w *ᵥ v) ^ (-σ)) ∂stepMeasure ≤
      ENNReal.ofReal r * ENNReal.ofReal (euclNorm v ^ (-σ))) (L : ℕ) (v : Pt 2) :
    ∫⁻ w, ENNReal.ofReal (euclNorm (prodQ w *ᵥ v) ^ (-σ))
        ∂(Measure.pi fun _ : Fin L => stepMeasure) ≤
      ENNReal.ofReal (r ^ L) * ENNReal.ofReal (euclNorm v ^ (-σ)) := by
  induction L generalizing v with
  | zero =>
    have : ∀ w : Fin 0 → Bool × Pt 2, prodQ w = 1 := fun w => by simp [prodQ]
    simp [this]
  | succ L ih =>
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (L + 1) => stepMeasure) 0).symm
    rw [← hmp.lintegral_comp (measurable_negpow σ (L + 1) v)]
    rw [lintegral_prod _ (Measurable.aemeasurable ?_)]
    swap
    · exact (measurable_negpow σ (L + 1) v).comp (MeasurableEquiv.measurable _)
    have hcons : ∀ (a : Bool × Pt 2) (t : Fin L → Bool × Pt 2),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L + 1) => Bool × Pt 2) 0).symm (a, t) =
          Fin.cons a t := by
      intro a t
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    calc ∫⁻ a, ∫⁻ t, ENNReal.ofReal (euclNorm (prodQ ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (L + 1) => Bool × Pt 2) 0).symm (a, t)) *ᵥ v) ^ (-σ))
            ∂(Measure.pi fun _ : Fin L => stepMeasure) ∂stepMeasure
        = ∫⁻ a, ∫⁻ t, ENNReal.ofReal (euclNorm (prodQ t *ᵥ (matQ a *ᵥ v)) ^ (-σ))
            ∂(Measure.pi fun _ : Fin L => stepMeasure) ∂stepMeasure := by
          simp only [hcons, prodQ_cons, Matrix.mulVec_mulVec]
      _ ≤ ∫⁻ a, ENNReal.ofReal (r ^ L) * ENNReal.ofReal (euclNorm (matQ a *ᵥ v) ^ (-σ))
            ∂stepMeasure := lintegral_mono fun a => ih _
      _ = ENNReal.ofReal (r ^ L) * ∫⁻ a, ENNReal.ofReal (euclNorm (matQ a *ᵥ v) ^ (-σ))
            ∂stepMeasure := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (r ^ L) * (ENNReal.ofReal r * ENNReal.ofReal (euclNorm v ^ (-σ))) :=
          mul_le_mul_right (hstep v) _
      _ = ENNReal.ofReal (r ^ (L + 1)) * ENNReal.ofReal (euclNorm v ^ (-σ)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr _), pow_succ]

/-- **Lemma 2.5.**  For every integer `q ≥ 3` there are `σ ∈ (0,1)` and `L ≥ 1` such that
`sup_{|e|=1} 𝔼|Q_L ⋯ Q_1 e|^{-σ} ≤ 1/(128 q^σ)`. -/
theorem lemma_negative (q : ℕ) (hq : 3 ≤ q) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ L : ℕ, 1 ≤ L ∧ NegMomentBound q σ L := by
  obtain ⟨N, hN1, hNb⟩ := matA_frob_bdd
  obtain ⟨d, hd, hdg⟩ := gQ_lower
  set B := Real.log N / 2 with hB
  have hB0 : 0 ≤ B := by have := Real.log_nonneg hN1; rw [hB]; linarith
  set σ := min (1 / 2) (min (1 / (B + 1)) (d / (8 * (B ^ 2 + 1)))) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 / 2 := min_le_left _ _
  have hσ2 : σ ≤ 1 / (B + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hσ3 : σ ≤ d / (8 * (B ^ 2 + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hσB : σ * B ≤ 1 := by
    have h1 : σ * (B + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hσ2 (by linarith : (0 : ℝ) ≤ B + 1)
      rwa [div_mul_cancel₀ _ (by linarith)] at this
    nlinarith
  have hσB2 : σ * B ^ 2 ≤ d / 8 := by
    have h1 : σ * (8 * (B ^ 2 + 1)) ≤ d := by
      have := mul_le_mul_of_nonneg_right hσ3 (by positivity : (0 : ℝ) ≤ 8 * (B ^ 2 + 1))
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    nlinarith
  set r := max (1 - σ * d / 8) 0 with hr
  have hr0 : 0 ≤ r := le_max_right _ _
  have hr1 : r < 1 := max_lt (by nlinarith) one_pos
  have hunit : ∀ e : Pt 2, euclNorm e = 1 →
      ∫⁻ w, ENNReal.ofReal (euclNorm (matQ w *ᵥ e) ^ (-σ)) ∂stepMeasure ≤ ENNReal.ofReal r := by
    intro e he
    refine (single_step_bound N hNb σ hσ0 hσB e he).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : σ * d ≤ σ * gQ e := mul_le_mul_of_nonneg_left (hdg e he) hσ0.le
    have h2 : σ * (σ * B ^ 2) ≤ σ * (d / 8) := mul_le_mul_of_nonneg_left hσB2 hσ0.le
    refine le_trans ?_ (le_max_left _ _)
    rw [← hB]
    nlinarith
  have hstep := single_step_homog σ r hσ0 hunit
  have hqpos : (0 : ℝ) < 1 / (128 * (q : ℝ) ^ σ) := by
    have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hqpos hr1
  refine ⟨σ, hσ0, by linarith, n + 1, by omega, fun e he => ?_⟩
  have hit := iterate_bound σ r hr0 hstep (n + 1) e
  rw [he, Real.one_rpow, ENNReal.ofReal_one, mul_one] at hit
  have hmeas : Measurable fun w : Fin (n + 1) → Bool × Pt 2 => euclNorm (prodQ w *ᵥ e) ^ (-σ) := by
    refine Measurable.pow_const ?_ _
    refine Continuous.measurable ?_
    unfold euclNorm
    have := continuous_prodQ (n + 1)
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => euclNorm (prodQ w *ᵥ e) ^ (-σ))
    (Eventually.of_forall fun w => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    hmeas.aestronglyMeasurable]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hit).trans ?_
  calc r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le (by omega)
    _ ≤ _ := hn.le

end AnomDiss
