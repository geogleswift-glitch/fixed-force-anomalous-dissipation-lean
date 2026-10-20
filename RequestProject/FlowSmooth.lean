module

public import RequestProject.FlowC2

/-!
# Smooth fields: basic properties

A time-dependent vector field `V` is a *smooth field with bounds `B`* if `(t, x) ↦ V t x` is
`C^∞` and `‖D^k_x V(t, x)‖ ≤ B k` for all `k`, `t`, `x`.  Such fields satisfy the standing
hypotheses `GoodField` and `C2Field` of the flow theory.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A jointly smooth time-dependent field with uniformly bounded spatial derivatives. -/
structure SmoothField (V : ℝ → E → E) (B : ℕ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry V)
  bound : ∀ k t x, ‖iteratedFDeriv ℝ k (V t) x‖ ≤ B k

lemma natCast_le_inf (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

lemma natCast_lt_inf (n : ℕ) : (n : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top n

namespace SmoothField

variable {V : ℝ → E → E} {B : ℕ → ℝ}

omit [CompleteSpace E] in
lemma B_nonneg (hV : SmoothField V B) (k : ℕ) : 0 ≤ B k :=
  (norm_nonneg _).trans (hV.bound k 0 0)

omit [CompleteSpace E] in
lemma contDiff_slice (hV : SmoothField V B) (t : ℝ) : ContDiff ℝ ∞ (V t) :=
  hV.smooth.comp (contDiff_const.prodMk contDiff_id)

omit [CompleteSpace E] in
lemma norm_le (hV : SmoothField V B) (t : ℝ) (x : E) : ‖V t x‖ ≤ B 0 := by
  simpa using hV.bound 0 t x

omit [CompleteSpace E] in
lemma norm_fderiv_le (hV : SmoothField V B) (t : ℝ) (x : E) : ‖fderiv ℝ (V t) x‖ ≤ B 1 := by
  simpa [norm_iteratedFDeriv_one] using hV.bound 1 t x

omit [CompleteSpace E] in
lemma norm_fderiv_fderiv_le (hV : SmoothField V B) (t : ℝ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (V t)) x‖ ≤ B 2 := by
  have := hV.bound 2 t x
  rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this

omit [CompleteSpace E] in
lemma norm_fderiv2_sub_le (f : E → E) (a b : E) :
    ‖fderiv ℝ (fderiv ℝ f) b - fderiv ℝ (fderiv ℝ f) a‖ ≤
      ‖iteratedFDeriv ℝ 2 f b - iteratedFDeriv ℝ 2 f a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have := (iteratedFDeriv ℝ 2 f b - iteratedFDeriv ℝ 2 f a).le_opNorm ![u, v]
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_two_apply, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at this
  simpa [mul_assoc] using this

omit [CompleteSpace E] in
lemma lip_iteratedFDeriv2 (hV : SmoothField V B) (t : ℝ) (a b : E) :
    ‖iteratedFDeriv ℝ 2 (V t) b - iteratedFDeriv ℝ 2 (V t) a‖ ≤ B 3 * ‖b - a‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ 2 (V t)) :=
    (hV.contDiff_slice t).differentiable_iteratedFDeriv (by exact_mod_cast natCast_lt_inf 2)
  have hL := lipschitzWith_of_nnnorm_fderiv_le (C := NNReal.mk (B 3) (hV.B_nonneg 3)) hd fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk, norm_fderiv_iteratedFDeriv]
    exact hV.bound 3 t x
  have := hL.dist_le_mul b a
  rwa [dist_eq_norm, dist_eq_norm] at this

omit [CompleteSpace E] in
/-- Joint smoothness of the spatial derivative. -/
lemma contDiff_fderiv_joint (hV : SmoothField V B) :
    ContDiff ℝ ∞ fun p : ℝ × E => fderiv ℝ (V p.1) p.2 := by
  have h : ContDiff ℝ ∞ (Function.uncurry fun (p : ℝ × E) (y : E) => V p.1 y) :=
    hV.smooth.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by simp)

omit [CompleteSpace E] in
lemma contDiff_fderiv_fderiv_joint (hV : SmoothField V B) :
    ContDiff ℝ ∞ fun p : ℝ × E => fderiv ℝ (fderiv ℝ (V p.1)) p.2 := by
  have h : ContDiff ℝ ∞ (Function.uncurry fun (p : ℝ × E) (y : E) => fderiv ℝ (V p.1) y) :=
    hV.contDiff_fderiv_joint.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by simp)

omit [CompleteSpace E] in
lemma toGood (hV : SmoothField V B) :
    GoodField V ⟨B 0, hV.B_nonneg 0⟩ ⟨B 1, hV.B_nonneg 1⟩ where
  cont x := hV.smooth.continuous.comp (continuous_id.prodMk continuous_const)
  bound t x := hV.norm_le t x
  lip t := lipschitzWith_of_nnnorm_fderiv_le ((hV.contDiff_slice t).differentiable (by norm_num))
    fun x => by
      change ‖fderiv ℝ (V t) x‖₊ ≤ NNReal.mk (B 1) (hV.B_nonneg 1)
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
      exact hV.norm_fderiv_le t x

omit [CompleteSpace E] in
lemma toC2 (hV : SmoothField V B) : C2Field V (B 2) (B 3) where
  diff t := (hV.contDiff_slice t).of_le (by exact_mod_cast natCast_le_inf 2)
  d2 t x := hV.norm_fderiv_fderiv_le t x
  nonneg3 := hV.B_nonneg 3
  lip2 t a b := (norm_fderiv2_sub_le (V t) a b).trans
    (hV.lip_iteratedFDeriv2 t a b)
  c1 x := (hV.contDiff_fderiv_joint.comp (contDiff_id.prodMk contDiff_const)).continuous
  c2 x := (hV.contDiff_fderiv_fderiv_joint.comp (contDiff_id.prodMk contDiff_const)).continuous

omit [CompleteSpace E] in
lemma rev (hV : SmoothField V B) (c : ℝ) : SmoothField (GoodField.revField V c) B where
  smooth := by
    have : Function.uncurry (GoodField.revField V c) =
        fun p : ℝ × E => -Function.uncurry V (c - p.1, p.2) := by
      funext p; rfl
    rw [this]
    exact (hV.smooth.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)).neg
  bound k t x := by
    have : GoodField.revField V c t = -V (c - t) := rfl
    rw [this, iteratedFDeriv_neg_apply, norm_neg]
    exact hV.bound k _ x

end SmoothField

end AnomDiss
