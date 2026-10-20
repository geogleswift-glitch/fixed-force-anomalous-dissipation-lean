module

public import RequestProject.Shears
public import RequestProject.TorusFourier

/-!
# Auxiliary results for the semiclassical observable lemma (Lemma 3.3)

* a Fourier representation `f(η) = ∫ F(z) e^{2πi z·η} dz` of a smooth compactly supported
  function, with `∫ (1 + |z|²)|F(z)| dz < ∞`;
* the polarized Parseval identity on `𝕋²`;
* translation invariance of the cell integral for periodic functions;
* a second-order Taylor estimate.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- Fourier representation of a smooth compactly supported function on `ℝ²`. -/
lemma fourier_rep_smooth (f : Pt 2 → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ F : Pt 2 → ℂ, Continuous F ∧ Integrable F ∧ Integrable (fun z => ‖z‖ ^ 2 * ‖F z‖) ∧
      ∀ η, (f η : ℂ) = ∫ z, F z * expChar z η := by
  set g : EuclideanSpace ℝ (Fin 2) → ℂ := fun η => (f (WithLp.ofLp η) : ℂ)
  have hgs : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp (hf.comp (EuclideanSpace.equiv (Fin 2) ℝ).contDiff)
  have hgc : HasCompactSupport g := by
    have := hfc.comp_homeomorph (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
    exact this.comp_left (g := Complex.ofReal) (by simp)
  set s := hgc.toSchwartzMap hgs
  have hinv : FourierTransformInv.fourierInv (FourierTransform.fourier s) = s :=
    FourierTransform.fourierInv_fourier_eq s
  have hpt : ∀ η, g η = ∫ v, Real.fourierChar (inner ℝ v η) • (FourierTransform.fourier s) v := by
    intro η
    have := congrArg (fun t : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ => t η) hinv
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at this
    rw [this]; rfl
  set Fs := FourierTransform.fourier s
  have hint := Fs.integrable (μ := volume)
  have hmom := Fs.integrable_pow_mul volume 2
  have hmp := PiLp.volume_preserving_toLp (Fin 2)
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding
  have hFc : Continuous fun z : Pt 2 => Fs (WithLp.toLp 2 z) :=
    Fs.continuous.comp (PiLp.continuous_toLp 2 _)
  refine ⟨fun z => Fs (WithLp.toLp 2 z), hFc, ?_, ?_, ?_⟩
  · exact (hmp.integrable_comp_emb hemb).mpr hint
  · have h2 := (hmp.integrable_comp_emb hemb).mpr hmom
    refine h2.mono' ((continuous_norm.pow 2).mul hFc.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp, norm_mul, norm_pow, norm_norm]
    gcongr
    refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun i => ?_
    exact PiLp.norm_apply_le (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2)) i
  · intro η
    have := hpt (WithLp.toLp 2 η)
    simp only [g] at this
    rw [this, ← hmp.integral_comp hemb]
    congr 1; funext z
    show _ = Fs (WithLp.toLp 2 z) * _
    rw [Circle.smul_def, Real.fourierChar_apply, expChar, mul_comm (Fs _)]
    congr 2
    simp only [PiLp.inner_apply, dot, RCLike.inner_apply, conj_trivial]
    simp only [Fin.sum_univ_two]
    push_cast
    ring

section TorusPolar

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- Parseval's identity for inner products on `𝕋²`. -/
theorem parseval_inner_cell (u v : Pt 2 → ℂ) (hu : Continuous u) (hup : IsPeriodic u)
    (hv : Continuous v) (hvp : IsPeriodic v) :
    HasSum (fun ℓ => starRingEnd ℂ (fc u ℓ) * fc v ℓ)
      (∫ x in cell 2, starRingEnd ℂ (u x) * v x) := by
  set F : UnitAddTorus (Fin 2) → ℂ := torusLift u with hF
  set G : UnitAddTorus (Fin 2) → ℂ := torusLift v with hG
  have hFm : Measurable F := measurable_torusLift_complex u hu
  have hGm : Measurable G := measurable_torusLift_complex v hv
  obtain ⟨C, hC⟩ := torusLift_bdd_complex u hu
  obtain ⟨D, hD⟩ := torusLift_bdd_complex v hv
  have hmF : MemLp F 2 volume := MemLp.of_bound hFm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [hF] using hC x)
  have hmG : MemLp G 2 volume := MemLp.of_bound hGm.aestronglyMeasurable D
    (Filter.Eventually.of_forall fun x => by simpa [hG] using hD x)
  have hs := UnitAddTorus.hasSum_prod_mFourierCoeff (hmF.toLp F) (hmG.toLp G)
  have e1 : ∀ n, UnitAddTorus.mFourierCoeff (hmF.toLp F) n = UnitAddTorus.mFourierCoeff F n :=
    fun n => integral_congr_ae (by filter_upwards [hmF.coeFn_toLp] with t ht; rw [ht])
  have e1' : ∀ n, UnitAddTorus.mFourierCoeff (hmG.toLp G) n = UnitAddTorus.mFourierCoeff G n :=
    fun n => integral_congr_ae (by filter_upwards [hmG.coeFn_toLp] with t ht; rw [ht])
  have e2 : ∫ t, starRingEnd ℂ (hmF.toLp F t) * hmG.toLp G t =
      ∫ t, starRingEnd ℂ (F t) * G t :=
    integral_congr_ae (by
      filter_upwards [hmF.coeFn_toLp, hmG.coeFn_toLp] with t ht ht'; rw [ht, ht'])
  have e3 : ∀ (w : Pt 2 → ℂ) (hw : Continuous w) (hwp : IsPeriodic w) n,
      UnitAddTorus.mFourierCoeff (torusLift w) n = fc w n := by
    intro w hw hwp n
    rw [UnitAddTorus.mFourierCoeff]
    calc
      (∫ t, (UnitAddTorus.mFourier (-n)) t • torusLift w t) =
          ∫ y in cell 2, (UnitAddTorus.mFourier (-n)) (torusProj y) •
            torusLift w (torusProj y) :=
        integral_torus_eq_cell (fun t => (UnitAddTorus.mFourier (-n)) t • torusLift w t)
          (((UnitAddTorus.mFourier (-n)).continuous.measurable).smul
            (measurable_torusLift_complex w hw)).aestronglyMeasurable
      _ = fc w n := by
        rw [fc]
        refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
        simp only [torusLift_proj w hwp, mFourier_torusProj, smul_eq_mul]
        have : intVec (-n) = -intVec n := by funext i; simp [intVec]
        rw [this, mul_comm]
  have e4 : ∫ t, starRingEnd ℂ (F t) * G t = ∫ x in cell 2, starRingEnd ℂ (u x) * v x := by
    rw [integral_torus_eq_cell (fun t => starRingEnd ℂ (F t) * G t)
      (((Complex.continuous_conj.measurable.comp hFm).mul hGm).aestronglyMeasurable)]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp [hF, hG, torusLift_proj u hup, torusLift_proj v hvp]
  have e3u : ∀ n, UnitAddTorus.mFourierCoeff F n = fc u n := e3 u hu hup
  have e3v : ∀ n, UnitAddTorus.mFourierCoeff G n = fc v n := e3 v hv hvp
  simp only [e1, e1', e2, e4, e3u, e3v] at hs
  exact hs

/-- Translation invariance of the cell integral of a continuous periodic function. -/
lemma integral_cell_translate (h : Pt 2 → ℂ) (hc : Continuous h) (hp : IsPeriodic h) (a : Pt 2) :
    ∫ y in cell 2, h (y + a) = ∫ y in cell 2, h y := by
  have hmap := map_cell_comp_of_torus h hc hp (fun z => z + a)
    (fun (u : UnitAddTorus (Fin 2)) i => u i + torusProj a i)
    (measurePreserving_pi (fun _ => (volume : Measure UnitAddCircle))
      (fun _ => (volume : Measure UnitAddCircle))
      fun i => measurePreserving_add_right volume (torusProj a i))
    (fun z => by funext i; simp [torusProj])
  have hc' : Continuous fun z : Pt 2 => h (z + a) := hc.comp (continuous_id.add continuous_const)
  have h1 := integral_map (μ := (volume : Measure (Pt 2)).restrict (cell 2))
    (f := fun x : ℂ => x) hc'.aemeasurable aestronglyMeasurable_id
  have h2 := integral_map (μ := (volume : Measure (Pt 2)).restrict (cell 2))
    (f := fun x : ℂ => x) hc.aemeasurable aestronglyMeasurable_id
  simp only at h1 h2 hmap
  rw [← h1, ← h2, hmap]

end TorusPolar

lemma fc_translate (G : Pt 2 → ℂ) (hc : Continuous G) (hp : IsPeriodic G) (a : Pt 2)
    (n : Fin 2 → ℤ) : fc (fun y => G (y + a)) n = expChar (intVec n) a * fc G n := by
  have hH := integral_cell_translate (fun y => G y * expChar (-intVec n) y)
    (hc.mul (continuous_expChar _))
    (fun x m => by
      have : -intVec n = intVec (-n) := by funext i; simp [intVec]
      simp only [this, hp x m, isPeriodic_expChar (-n) x m]) a
  have he : ∀ y, expChar (-intVec n) (y + a) * expChar (intVec n) a = expChar (-intVec n) y := by
    intro y
    rw [expChar_add_right, mul_assoc, expChar_mul, neg_add_cancel]
    simp [expChar, dot]
  rw [fc, fc, ← hH, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  rw [← he y]; ring

/-- `∑ₙ e(n·a)|Ĉ(n)|² = ∫ conj(G) G(·+a)`. -/
lemma hasSum_char_sq (G : Pt 2 → ℂ) (hc : Continuous G) (hp : IsPeriodic G) (a : Pt 2) :
    HasSum (fun n => expChar (intVec n) a * ((‖fc G n‖ ^ 2 : ℝ) : ℂ))
      (∫ y in cell 2, starRingEnd ℂ (G y) * G (y + a)) := by
  have hc' : Continuous fun y => G (y + a) := hc.comp (continuous_id.add continuous_const)
  have := parseval_inner_cell G (fun y => G (y + a)) hc hp hc' (fun x m => by
    simp only [add_right_comm x, hp (x + a) m])
  refine this.congr_fun fun n => ?_
  rw [fc_translate G hc hp a n]
  push_cast
  rw [← Complex.mul_conj']
  ring

/-- Second-order Taylor estimate: `|Ψ(y+h) - Ψ(y) - DΨ(y)h| ≤ K|h|²` when `‖D²Ψ‖ ≤ K`. -/
lemma taylor2_bound (Ψ : Pt 2 → Pt 2) (hΨ : ContDiff ℝ 2 Ψ) (K : ℝ)
    (hK : ∀ y, ‖iteratedFDeriv ℝ 2 Ψ y‖ ≤ K) (y h : Pt 2) :
    ‖Ψ (y + h) - Ψ y - fderiv ℝ Ψ y h‖ ≤ K * ‖h‖ ^ 2 := by
  have hd1 : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hK2 : ∀ z, ‖fderiv ℝ (fderiv ℝ Ψ) z‖ ≤ K := by
    intro z
    have := hK z
    rwa [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] at *
  have hlip : ∀ z, ‖fderiv ℝ Ψ z - fderiv ℝ Ψ y‖ ≤ K * ‖z - y‖ := fun z =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd2 z) (fun z _ => hK2 z)
      (Set.mem_univ y) (Set.mem_univ z)
  set g : Pt 2 → Pt 2 := fun x => Ψ x - fderiv ℝ Ψ y x
  have hg : ∀ x, HasFDerivAt g (fderiv ℝ Ψ x - fderiv ℝ Ψ y) x := fun x =>
    (hd1 x).hasFDerivAt.sub (fderiv ℝ Ψ y).hasFDerivAt
  have hseg : ∀ x ∈ segment ℝ y (y + h), ‖fderiv ℝ Ψ x - fderiv ℝ Ψ y‖ ≤ K * ‖h‖ := by
    intro x hx
    refine (hlip x).trans ?_
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK y)
    gcongr
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    have : a • y + b • (y + h) - y = b • h := by
      rw [smul_add, ← add_assoc, ← add_smul, hab, one_smul]; abel
    rw [this, norm_smul, Real.norm_of_nonneg hb]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have := (convex_segment y (y + h)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hg x).hasFDerivWithinAt) hseg (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  simp only [g, map_add, add_sub_cancel_left] at this
  calc ‖Ψ (y + h) - Ψ y - fderiv ℝ Ψ y h‖
      = ‖Ψ (y + h) - (fderiv ℝ Ψ y y + fderiv ℝ Ψ y h) - (Ψ y - fderiv ℝ Ψ y y)‖ := by
        congr 1; abel
    _ ≤ K * ‖h‖ * ‖h‖ := this
    _ = K * ‖h‖ ^ 2 := by ring

/-- `|e^{2πiu} - e^{2πiv}| ≤ 2π|u - v|`. -/
lemma norm_exp2pi_sub_le (u v : ℝ) :
    ‖Complex.exp (2 * π * Complex.I * (u : ℂ)) - Complex.exp (2 * π * Complex.I * (v : ℂ))‖ ≤
      2 * π * |u - v| := by
  have h1 : Complex.exp (2 * π * Complex.I * (u : ℂ)) - Complex.exp (2 * π * Complex.I * (v : ℂ)) =
      Complex.exp (2 * π * Complex.I * (v : ℂ)) *
        (Complex.exp (Complex.I * ((2 * π * (u - v) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2; push_cast; ring
  rw [h1, norm_mul]
  have h2 : ‖Complex.exp (2 * π * Complex.I * (v : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [h2, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]

/-- For a Euclidean unit vector `e`, `|e·w| ≤ 2‖w‖` (sup norm). -/
lemma abs_dot_le_of_unit (e w : Pt 2) (he : euclNorm e = 1) : |dot e w| ≤ 2 * ‖w‖ := by
  have hei : ∀ i, |e i| ≤ 1 := by
    intro i
    have : e i ^ 2 ≤ ∑ j, e j ^ 2 :=
      Finset.single_le_sum (f := fun j => e j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hs : ∑ j, e j ^ 2 = 1 := by
      have := he; unfold euclNorm at this
      rw [Real.sqrt_eq_one] at this; exact this
    rw [hs] at this
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  unfold dot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Fin.sum_univ_two]
  have h0 := norm_le_pi_norm w 0
  have h1 := norm_le_pi_norm w 1
  rw [Real.norm_eq_abs] at h0 h1
  rw [abs_mul, abs_mul]
  have := hei 0; have := hei 1
  nlinarith [abs_nonneg (w 0), abs_nonneg (w 1), abs_nonneg (e 0), abs_nonneg (e 1)]

lemma expChar_rescale (z e : Pt 2) (n : Fin 2 → ℤ) (ρ : ℝ) (hρ : ρ ≠ 0) :
    expChar z (ρ⁻¹ • (ρ • e + intVec n)) = expChar z e * expChar (intVec n) (ρ⁻¹ • z) := by
  unfold expChar
  rw [← Complex.exp_add]
  congr 1
  simp only [dot, Fin.sum_univ_two, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  push_cast
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  field_simp
  ring

lemma dot_transpose_jac (Ψ : Pt 2 → Pt 2) (y z e : Pt 2) :
    dot z ((jac Ψ y)ᵀ *ᵥ e) = dot e (fderiv ℝ Ψ y z) := by
  rw [fderiv_eq_matCLM_jac, matCLM_apply]
  simp only [dot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

end AnomDiss
