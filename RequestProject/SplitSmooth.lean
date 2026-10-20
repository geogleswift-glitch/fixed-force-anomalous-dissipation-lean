module

public import RequestProject.SplitFlow
public import RequestProject.FlowC2

/-!
# Spatial regularity of the splitting fields

The fields `x ↦ eField (c(s)) (x - z)` are sums of two shear terms `sc α β (x k) • v`; we compute
their first two spatial derivatives explicitly and deduce the `C2Field` hypotheses, uniformly
in the coefficients.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- The coordinate projection `x ↦ x k` on `ℝ²`. -/
abbrev prj (k : Fin 2) : Pt 2 →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k

lemma norm_prj_le (k : Fin 2) : ‖prj k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_le_pi_norm x k

/-- A shear term `x ↦ sc α β ((x - z) k) • v`. -/
def shT (α β : ℝ) (k : Fin 2) (v z : Pt 2) (x : Pt 2) : Pt 2 := sc α β ((x - z) k) • v

/-- Its derivative. -/
def shT1 (α β : ℝ) (k : Fin 2) (v z : Pt 2) (x : Pt 2) : Pt 2 →L[ℝ] Pt 2 :=
  (prj k).smulRight (sc (-(2 * π * β)) (2 * π * α) ((x - z) k) • v)

/-- Its second derivative. -/
def shT2 (α β : ℝ) (k : Fin 2) (v z : Pt 2) (x : Pt 2) : Pt 2 →L[ℝ] Pt 2 →L[ℝ] Pt 2 :=
  (prj k).smulRight ((prj k).smulRight
    (sc (-(2 * π * (2 * π * α))) (2 * π * (-(2 * π * β))) ((x - z) k) • v))

lemma hasFDerivAt_coord_sub (k : Fin 2) (z x : Pt 2) :
    HasFDerivAt (fun y : Pt 2 => (y - z) k) (prj k) x := by
  have := ((prj k).hasFDerivAt (x := x)).sub_const ((prj k) z)
  simpa only [prj, ContinuousLinearMap.proj_apply, Pi.sub_apply] using this

lemma hasFDerivAt_shT (α β : ℝ) (k : Fin 2) (v z x : Pt 2) :
    HasFDerivAt (shT α β k v z) (shT1 α β k v z x) x := by
  have hg : HasDerivAt (fun t => sc α β t • v) (sc (-(2 * π * β)) (2 * π * α) ((x - z) k) • v)
      ((x - z) k) := (hasDerivAt_sc α β _).smul_const v
  have := hg.hasFDerivAt.comp x (hasFDerivAt_coord_sub k z x)
  refine this.congr_fderiv ?_
  ext h i
  simp [shT1]

lemma hasFDerivAt_shT1 (α β : ℝ) (k : Fin 2) (v z x : Pt 2) :
    HasFDerivAt (shT1 α β k v z) (shT2 α β k v z x) x := by
  set R := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2) (prj k)
  have hg : HasDerivAt (fun t => R (sc (-(2 * π * β)) (2 * π * α) t • v))
      (R (sc (-(2 * π * (2 * π * α))) (2 * π * (-(2 * π * β))) ((x - z) k) • v)) ((x - z) k) :=
    R.hasFDerivAt.comp_hasDerivAt _ ((hasDerivAt_sc _ _ _).smul_const v)
  have := hg.hasFDerivAt.comp x (hasFDerivAt_coord_sub k z x)
  refine this.congr_fderiv ?_
  ext h w i
  simp [shT2, R]
  left; ring

lemma fderiv_shT (α β : ℝ) (k : Fin 2) (v z : Pt 2) :
    fderiv ℝ (shT α β k v z) = shT1 α β k v z :=
  funext fun x => (hasFDerivAt_shT α β k v z x).fderiv

lemma fderiv_shT1 (α β : ℝ) (k : Fin 2) (v z : Pt 2) :
    fderiv ℝ (shT1 α β k v z) = shT2 α β k v z :=
  funext fun x => (hasFDerivAt_shT1 α β k v z x).fderiv

lemma contDiff_shT (α β : ℝ) (k : Fin 2) (v z : Pt 2) : ContDiff ℝ ∞ (shT α β k v z) := by
  unfold shT
  have h1 : ContDiff ℝ ∞ fun x : Pt 2 => (x - z) k := by
    have : (fun x : Pt 2 => (x - z) k) = fun x => prj k x - prj k z := by funext x; simp
    rw [this]; exact (prj k).contDiff.sub contDiff_const
  exact ((contDiff_sc α β).comp h1).smul contDiff_const

lemma norm_smulRight_smulRight_le (k : Fin 2) (w : Pt 2) :
    ‖(prj k).smulRight ((prj k).smulRight w)‖ ≤ ‖w‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply]
  have h := norm_prj_le k
  have := norm_nonneg w
  have := norm_nonneg (prj k)
  nlinarith [mul_le_mul h h (norm_nonneg _) zero_le_one]

lemma norm_shT2_le (α β : ℝ) (k : Fin 2) {v : Pt 2} (hv : ‖v‖ ≤ 1) (z x : Pt 2) :
    ‖shT2 α β k v z x‖ ≤ 4 * π ^ 2 * (|α| + |β|) := by
  refine (norm_smulRight_smulRight_le k _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h := abs_sc_le (-(2 * π * (2 * π * α))) (2 * π * (-(2 * π * β))) ((x - z) k)
  have e : |-(2 * π * (2 * π * α))| + |2 * π * (-(2 * π * β))| = 4 * π ^ 2 * (|α| + |β|) := by
    simp only [abs_neg, abs_mul, abs_two, abs_of_pos Real.pi_pos]
    ring
  rw [e] at h
  calc |sc _ _ ((x - z) k)| * ‖v‖ ≤ (4 * π ^ 2 * (|α| + |β|)) * 1 := by
        gcongr
    _ = _ := mul_one _

lemma norm_shT2_sub_le (α β : ℝ) (k : Fin 2) {v : Pt 2} (hv : ‖v‖ ≤ 1) (z a b : Pt 2) :
    ‖shT2 α β k v z b - shT2 α β k v z a‖ ≤ 8 * π ^ 3 * (|α| + |β|) * ‖b - a‖ := by
  set R := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2) (prj k)
  set R2 := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2 →L[ℝ] Pt 2) (prj k)
  set α2 := -(2 * π * (2 * π * α))
  set β2 := 2 * π * (-(2 * π * β))
  have e : shT2 α β k v z b - shT2 α β k v z a =
      (prj k).smulRight ((prj k).smulRight ((sc α2 β2 ((b - z) k) - sc α2 β2 ((a - z) k)) • v)) := by
    have : ∀ y, shT2 α β k v z y = R2 (R (sc α2 β2 ((y - z) k) • v)) := fun y => rfl
    rw [this, this]
    ext h w i
    simp [R, R2, sub_smul]
    ring
  rw [e]
  refine (norm_smulRight_smulRight_le k _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h := abs_sc_sub_le α2 β2 ((b - z) k) ((a - z) k)
  have e2 : |α2| + |β2| = 4 * π ^ 2 * (|α| + |β|) := by
    simp only [α2, β2, abs_neg, abs_mul, abs_two, abs_of_pos Real.pi_pos]
    ring
  have hk : |(b - z) k - (a - z) k| ≤ ‖b - a‖ := by
    have : (b - z) k - (a - z) k = (b - a) k := by simp
    rw [this, ← Real.norm_eq_abs]; exact norm_le_pi_norm (b - a) k
  rw [e2] at h
  have h0 : 0 ≤ |α| + |β| := by positivity
  calc |sc α2 β2 ((b - z) k) - sc α2 β2 ((a - z) k)| * ‖v‖
      ≤ (2 * π * (4 * π ^ 2 * (|α| + |β|)) * ‖b - a‖) * 1 := by
        gcongr
        exact h.trans (by gcongr)
    _ = _ := by ring

/-- The unit vectors of `ℝ²` used by the eigenfields. -/
def ev0 : Pt 2 := ![1, 0]
def ev1 : Pt 2 := ![0, 1]

lemma norm_ev0 : ‖ev0‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  fin_cases i <;> simp [ev0]

lemma norm_ev1 : ‖ev1‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  fin_cases i <;> simp [ev1]

lemma eField_sub_eq (c : Fin 4 → ℝ) (z x : Pt 2) :
    eField c (x - z) = shT (c 0) (c 1) 1 ev0 z x + shT (c 2) (c 3) 0 ev1 z x := by
  rw [eField_eq]
  ext k; fin_cases k <;> simp [pair2, shT, ev0, ev1]

/-- The translated eigenfield with time-dependent coefficients. -/
def eFieldAt (c : ℝ → Fin 4 → ℝ) (z : Pt 2) (s : ℝ) (x : Pt 2) : Pt 2 := eField (c s) (x - z)

lemma eFieldAt_eq (c : ℝ → Fin 4 → ℝ) (z : Pt 2) (s : ℝ) :
    eFieldAt c z s = fun x => shT (c s 0) (c s 1) 1 ev0 z x + shT (c s 2) (c s 3) 0 ev1 z x :=
  funext fun x => eField_sub_eq (c s) z x

lemma fderiv_eFieldAt (c : ℝ → Fin 4 → ℝ) (z : Pt 2) (s : ℝ) :
    fderiv ℝ (eFieldAt c z s) =
      fun x => shT1 (c s 0) (c s 1) 1 ev0 z x + shT1 (c s 2) (c s 3) 0 ev1 z x := by
  rw [eFieldAt_eq]
  exact funext fun x => ((hasFDerivAt_shT _ _ _ _ _ x).add (hasFDerivAt_shT _ _ _ _ _ x)).fderiv

lemma fderiv_fderiv_eFieldAt (c : ℝ → Fin 4 → ℝ) (z : Pt 2) (s : ℝ) :
    fderiv ℝ (fderiv ℝ (eFieldAt c z s)) =
      fun x => shT2 (c s 0) (c s 1) 1 ev0 z x + shT2 (c s 2) (c s 3) 0 ev1 z x := by
  rw [fderiv_eFieldAt]
  exact funext fun x => ((hasFDerivAt_shT1 _ _ _ _ _ x).add (hasFDerivAt_shT1 _ _ _ _ _ x)).fderiv

lemma continuous_sc_param {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    Continuous fun s => sc (f s) (g s) t := by
  unfold sc; fun_prop

/-- The translated eigenfields with continuous bounded coefficients satisfy the second-order
regularity hypotheses. -/
theorem eFieldAt_C2 {c : ℝ → Fin 4 → ℝ} (hc : Continuous c) {A : ℝ} (hA : ∀ s, ‖c s‖ ≤ A)
    (z : Pt 2) : C2Field (eFieldAt c z) (16 * π ^ 2 * A) (32 * π ^ 3 * A) where
  diff s := by
    rw [eFieldAt_eq]
    exact contDiff_infty.1 ((contDiff_shT _ _ _ _ _).add (contDiff_shT _ _ _ _ _)) 2
  d2 s x := by
    rw [fderiv_fderiv_eFieldAt]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_shT2_le (c s 0) (c s 1) 1 norm_ev0 z x
    have h2 := norm_shT2_le (c s 2) (c s 3) 0 norm_ev1 z x
    have := coef_abs_le (c s) 0; have := coef_abs_le (c s) 1
    have := coef_abs_le (c s) 2; have := coef_abs_le (c s) 3
    have := hA s
    have hπ : 0 ≤ π ^ 2 := by positivity
    nlinarith
  nonneg3 := by
    have := (norm_nonneg (c 0)).trans (hA 0)
    positivity
  lip2 s a b := by
    rw [fderiv_fderiv_eFieldAt]
    have e : shT2 (c s 0) (c s 1) 1 ev0 z b + shT2 (c s 2) (c s 3) 0 ev1 z b -
        (shT2 (c s 0) (c s 1) 1 ev0 z a + shT2 (c s 2) (c s 3) 0 ev1 z a) =
        (shT2 (c s 0) (c s 1) 1 ev0 z b - shT2 (c s 0) (c s 1) 1 ev0 z a) +
        (shT2 (c s 2) (c s 3) 0 ev1 z b - shT2 (c s 2) (c s 3) 0 ev1 z a) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_shT2_sub_le (c s 0) (c s 1) 1 norm_ev0 z a b
    have h2 := norm_shT2_sub_le (c s 2) (c s 3) 0 norm_ev1 z a b
    have := coef_abs_le (c s) 0; have := coef_abs_le (c s) 1
    have := coef_abs_le (c s) 2; have := coef_abs_le (c s) 3
    have := hA s
    have hπ : 0 ≤ π ^ 3 := by positivity
    have hn := norm_nonneg (b - a)
    have : (|c s 0| + |c s 1|) + (|c s 2| + |c s 3|) ≤ 4 * A := by linarith
    calc ‖shT2 (c s 0) (c s 1) 1 ev0 z b - shT2 (c s 0) (c s 1) 1 ev0 z a‖ +
          ‖shT2 (c s 2) (c s 3) 0 ev1 z b - shT2 (c s 2) (c s 3) 0 ev1 z a‖
        ≤ 8 * π ^ 3 * ((|c s 0| + |c s 1|) + (|c s 2| + |c s 3|)) * ‖b - a‖ := by
          nlinarith
      _ ≤ 8 * π ^ 3 * (4 * A) * ‖b - a‖ := by gcongr
      _ = 32 * π ^ 3 * A * ‖b - a‖ := by ring
  c1 x := by
    simp only [fderiv_eFieldAt, shT1]
    set R1 := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2) (prj 1)
    set R0 := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2) (prj 0)
    have h1 : Continuous fun s => sc (-(2 * π * c s 1)) (2 * π * c s 0) ((x - z) 1) := by
      unfold sc; fun_prop
    have h2 : Continuous fun s => sc (-(2 * π * c s 3)) (2 * π * c s 2) ((x - z) 0) := by
      unfold sc; fun_prop
    exact (R1.continuous.comp (h1.smul continuous_const)).add
      (R0.continuous.comp (h2.smul continuous_const))
  c2 x := by
    letI : ContinuousAdd (Pt 2 →L[ℝ] Pt 2 →L[ℝ] Pt 2) :=
      (inferInstance : IsTopologicalAddGroup (Pt 2 →L[ℝ] Pt 2 →L[ℝ] Pt 2)).toContinuousAdd
    simp only [fderiv_fderiv_eFieldAt, shT2]
    set R1 := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2) (prj 1)
    set R0 := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2) (prj 0)
    set Q1 := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2 →L[ℝ] Pt 2) (prj 1)
    set Q0 := ContinuousLinearMap.smulRightL ℝ (Pt 2) (Pt 2 →L[ℝ] Pt 2) (prj 0)
    have h1 : Continuous fun s => sc (-(2 * π * (2 * π * c s 0))) (2 * π * -(2 * π * c s 1))
        ((x - z) 1) := by
      unfold sc; fun_prop
    have h2 : Continuous fun s => sc (-(2 * π * (2 * π * c s 2))) (2 * π * -(2 * π * c s 3))
        ((x - z) 0) := by
      unfold sc; fun_prop
    exact ((Q1.continuous.comp R1.continuous).comp (h1.fun_smul continuous_const)).fun_add
      ((Q0.continuous.comp R0.continuous).comp (h2.fun_smul continuous_const))

end AnomDiss
