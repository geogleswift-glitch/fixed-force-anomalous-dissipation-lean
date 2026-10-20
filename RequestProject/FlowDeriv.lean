module

public import RequestProject.FlowTools

/-!
# Differentiable dependence of flows on the initial point

For a time-dependent field `V` which is bounded and Lipschitz (`GoodField`) and `C³` in space
with bounded second and third derivatives (`C2Field`), the flow maps `gflow V t₀ t` are `C²`,
with `‖D Φ - I‖ ≤ K|t - t₀| e^{K|t-t₀|}` and `‖D² Φ‖ ≤ K₂ |t - t₀| e^{3K|t-t₀|}`.

The derivative is the solution `J` of the variational equation `J' = DV(Φ) J`, `J(t₀) = I`, and
the second derivative is the solution `H` of `H' = DV(Φ) H + D²V(Φ)[J·] J`, `H(t₀) = 0`;
differentiability is proved by Grönwall estimates on quadratic remainders.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Spatial `C³` regularity of a time-dependent field with bounded second and third derivatives,
and continuity in time of the first two derivatives. -/
structure C2Field (V : ℝ → E → E) (K2 K3 : ℝ) : Prop where
  diff : ∀ t, ContDiff ℝ 2 (V t)
  d2 : ∀ t x, ‖fderiv ℝ (fderiv ℝ (V t)) x‖ ≤ K2
  nonneg3 : 0 ≤ K3
  lip2 : ∀ t a b, ‖fderiv ℝ (fderiv ℝ (V t)) b - fderiv ℝ (fderiv ℝ (V t)) a‖ ≤ K3 * ‖b - a‖
  c1 : ∀ x, Continuous fun t => fderiv ℝ (V t) x
  c2 : ∀ x, Continuous fun t => fderiv ℝ (fderiv ℝ (V t)) x

namespace C2Field

variable {V : ℝ → E → E} {K2 K3 : ℝ}

omit [CompleteSpace E] in
lemma K2_nonneg (hV2 : C2Field V K2 K3) : 0 ≤ K2 :=
  (norm_nonneg (fderiv ℝ (fderiv ℝ (V 0)) 0)).trans (hV2.d2 0 0)

omit [CompleteSpace E] in
lemma K3_nonneg (hV2 : C2Field V K2 K3) : 0 ≤ K3 := hV2.nonneg3

omit [CompleteSpace E] in
lemma differentiable0 (hV2 : C2Field V K2 K3) (t : ℝ) : Differentiable ℝ (V t) :=
  (hV2.diff t).differentiable (by norm_num)

omit [CompleteSpace E] in
lemma differentiable1 (hV2 : C2Field V K2 K3) (t : ℝ) : Differentiable ℝ (fderiv ℝ (V t)) :=
  ((hV2.diff t).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)


omit [CompleteSpace E] in
lemma lip1 (hV2 : C2Field V K2 K3) (t : ℝ) (a b : E) :
    ‖fderiv ℝ (V t) b - fderiv ℝ (V t) a‖ ≤ K2 * ‖b - a‖ :=
  norm_sub_le_of_fderiv_le (hV2.differentiable1 t) (hV2.d2 t) a b

omit [CompleteSpace E] in
lemma lipW1 (hV2 : C2Field V K2 K3) (t : ℝ) :
    LipschitzWith (Real.toNNReal K2) (fderiv ℝ (V t)) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hV2.K2_nonneg, norm_sub_rev,
      norm_sub_rev a]
    exact hV2.lip1 t a b

omit [CompleteSpace E] in
lemma lipW2 (hV2 : C2Field V K2 K3) (t : ℝ) :
    LipschitzWith (Real.toNNReal K3) (fderiv ℝ (fderiv ℝ (V t))) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm (fderiv ℝ (fderiv ℝ (V t)) a), dist_eq_norm a,
      Real.coe_toNNReal _ hV2.K3_nonneg, norm_sub_rev, norm_sub_rev a]
    exact hV2.lip2 t a b

omit [CompleteSpace E] in
lemma taylor0 (hV2 : C2Field V K2 K3) (t : ℝ) (a b : E) :
    ‖V t b - V t a - fderiv ℝ (V t) a (b - a)‖ ≤ K2 * ‖b - a‖ ^ 2 :=
  norm_taylor1_le hV2.K2_nonneg (hV2.differentiable0 t) (hV2.lip1 t) a b

omit [CompleteSpace E] in
lemma taylor1 (hV2 : C2Field V K2 K3) (t : ℝ) (a b : E) :
    ‖fderiv ℝ (V t) b - fderiv ℝ (V t) a - fderiv ℝ (fderiv ℝ (V t)) a (b - a)‖ ≤
      K3 * ‖b - a‖ ^ 2 :=
  norm_taylor1_le hV2.K3_nonneg (hV2.differentiable1 t) (hV2.lip2 t) a b

end C2Field

omit [CompleteSpace E] in
/-- Postcomposition with `A` has norm at most `‖A‖`. -/
lemma norm_compL_apply_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : F →L[ℝ] G) :
    ‖ContinuousLinearMap.compL ℝ E F G A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun J => by
    simpa using A.opNorm_comp_le J

section Forward

variable {V : ℝ → E → E} {M K : ℝ≥0} {K2 K3 : ℝ}

omit [CompleteSpace E] in
lemma GoodField.norm_fderiv_le (hV : GoodField V M K) (t : ℝ) (x : E) :
    ‖fderiv ℝ (V t) x‖ ≤ K :=
  norm_fderiv_le_of_lipschitz ℝ (hV.lip t)

lemma continuous_A (hV : GoodField V M K) (hV2 : C2Field V K2 K3) (t₀ : ℝ) (x : E) :
    Continuous fun s => fderiv ℝ (V s) (gflow V t₀ s x) :=
  continuous_comp_of_lip hV2.c1 hV2.lipW1 (hV.continuous_gflow_time t₀ x)

lemma continuous_A2 (hV : GoodField V M K) (hV2 : C2Field V K2 K3) (t₀ : ℝ) (x : E) :
    Continuous fun s => fderiv ℝ (fderiv ℝ (V s)) (gflow V t₀ s x) :=
  continuous_comp_of_lip hV2.c2 hV2.lipW2 (hV.continuous_gflow_time t₀ x)

/-- Solutions of the variational equation. -/
def IsVarSol (V : ℝ → E → E) (t₀ t₁ : ℝ) (x : E) (J : ℝ → E →L[ℝ] E) : Prop :=
  J t₀ = ContinuousLinearMap.id ℝ E ∧
    ∀ s ∈ Icc t₀ t₁, HasDerivAt J ((fderiv ℝ (V s) (gflow V t₀ s x)).comp (J s)) s

lemma exists_varSol (hV : GoodField V M K) (hV2 : C2Field V K2 K3) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (x : E) : ∃ J, IsVarSol V t₀ t₁ x J := by
  have hcA := continuous_A hV hV2 t₀ x
  obtain ⟨J, hJ0, hJ⟩ := exists_affODE_on (F := E →L[ℝ] E)
    (W := fun s Jm => (fderiv ℝ (V s) (gflow V t₀ s x)).comp Jm) h01 K.2 le_rfl
    (fun Jm => (hcA.clm_comp continuous_const).continuousOn)
    (fun s _ y z => by
      rw [← ContinuousLinearMap.comp_sub]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by gcongr; exact hV.norm_fderiv_le s _))
    (fun s _ y => by
      rw [add_zero]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by gcongr; exact hV.norm_fderiv_le s _))
    (ContinuousLinearMap.id ℝ E)
  exact ⟨J, hJ0, hJ⟩

variable {t₀ t₁ : ℝ} {x : E} {J : ℝ → E →L[ℝ] E}

omit [CompleteSpace E] in
lemma IsVarSol.norm_le (hV : GoodField V M K) (hJ : IsVarSol V t₀ t₁ x J) {s : ℝ}
    (hs : s ∈ Icc t₀ t₁) : ‖J s‖ ≤ Real.exp (K * (s - t₀)) := by
  have key := norm_le_of_hasDerivAt_le (f := J) (a := t₀) (b := s) (K := K) (ε := 0) (δ := 1)
    hs.1 K.2 le_rfl (fun r hr => hJ.2 r ⟨hr.1, hr.2.trans hs.2⟩) (fun r _ => by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [add_zero]
      gcongr
      exact hV.norm_fderiv_le r _) (by rw [hJ.1]; exact ContinuousLinearMap.norm_id_le)
  simpa using key

omit [CompleteSpace E] in
lemma IsVarSol.norm_sub_id_le (hV : GoodField V M K) (hJ : IsVarSol V t₀ t₁ x J) {s : ℝ}
    (hs : s ∈ Icc t₀ t₁) :
    ‖J s - ContinuousLinearMap.id ℝ E‖ ≤ K * (s - t₀) * Real.exp (K * (s - t₀)) := by
  have key := norm_le_of_hasDerivAt_le (f := fun r => J r - ContinuousLinearMap.id ℝ E)
    (a := t₀) (b := s) (K := K) (ε := K) (δ := 0)
    hs.1 K.2 K.2 (fun r hr => (hJ.2 r ⟨hr.1, hr.2.trans hs.2⟩).sub_const _) (fun r _ => by
      set A := fderiv ℝ (V r) (gflow V t₀ r x)
      have e : A.comp (J r) = A.comp (J r - ContinuousLinearMap.id ℝ E) + A := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, sub_add_cancel]
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have hA : ‖A‖ ≤ K := hV.norm_fderiv_le r _
      have := ContinuousLinearMap.opNorm_comp_le A (J r - ContinuousLinearMap.id ℝ E)
      have h0 := norm_nonneg (J r - ContinuousLinearMap.id ℝ E)
      nlinarith) (by simp [hJ.1])
  simpa [mul_comm, mul_assoc, mul_left_comm] using key

/-- The quadratic remainder estimate for the flow. -/
lemma IsVarSol.remainder (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hJ : IsVarSol V t₀ t₁ x J) (y : E) {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    ‖gflow V t₀ s y - gflow V t₀ s x - J s (y - x)‖ ≤
      K2 * (s - t₀) * Real.exp (3 * K * (s - t₀)) * ‖y - x‖ ^ 2 := by
  have hK2 := hV2.K2_nonneg
  set ε : ℝ := K2 * Real.exp (2 * K * (s - t₀)) * ‖y - x‖ ^ 2 with hε
  have key := norm_le_of_hasDerivAt_le
    (f := fun r => gflow V t₀ r y - gflow V t₀ r x - J r (y - x))
    (f' := fun r => V r (gflow V t₀ r y) - V r (gflow V t₀ r x) -
      ((fderiv ℝ (V r) (gflow V t₀ r x)).comp (J r) (y - x) + J r 0))
    (a := t₀) (b := s) (K := K) (ε := ε) (δ := 0) hs.1 K.2 (by positivity)
    (fun r hr => ((hV.hasDerivAt_gflow t₀ r y).sub (hV.hasDerivAt_gflow t₀ r x)).sub
      ((hJ.2 r ⟨hr.1, hr.2.trans hs.2⟩).clm_apply (hasDerivAt_const r (y - x))))
    (fun r hr => by
      beta_reduce
      set A := fderiv ℝ (V r) (gflow V t₀ r x)
      set d := gflow V t₀ r y - gflow V t₀ r x
      have e : V r (gflow V t₀ r y) - V r (gflow V t₀ r x) - (A.comp (J r) (y - x) + J r 0) =
          A (gflow V t₀ r y - gflow V t₀ r x - J r (y - x)) +
            (V r (gflow V t₀ r y) - V r (gflow V t₀ r x) - A d) := by
        simp only [map_zero, add_zero, ContinuousLinearMap.comp_apply, map_sub, d]; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact ((A.le_opNorm _)).trans (by gcongr; exact hV.norm_fderiv_le r _)
      · have h1 := hV2.taylor0 r (gflow V t₀ r x) (gflow V t₀ r y)
        have h2 : ‖d‖ ≤ ‖y - x‖ * Real.exp (K * (r - t₀)) := by
          have := hV.dist_gflow_le_of_le hr.1 y x
          rwa [dist_eq_norm, dist_eq_norm] at this
        refine h1.trans ?_
        rw [hε]
        have h3 : ‖d‖ ^ 2 ≤ (‖y - x‖ * Real.exp (K * (r - t₀))) ^ 2 := by
          gcongr
        have h4 : (‖y - x‖ * Real.exp (K * (r - t₀))) ^ 2 =
            Real.exp (2 * K * (r - t₀)) * ‖y - x‖ ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
        have h5 : Real.exp (2 * K * (r - t₀)) ≤ Real.exp (2 * K * (s - t₀)) := by
          gcongr; exact hr.2
        calc K2 * ‖d‖ ^ 2 ≤ K2 * (Real.exp (2 * K * (r - t₀)) * ‖y - x‖ ^ 2) := by
              rw [← h4]; gcongr
          _ ≤ K2 * (Real.exp (2 * K * (s - t₀)) * ‖y - x‖ ^ 2) := by gcongr
          _ = _ := by ring)
    (by simp [hV.gflow_self, hJ.1])
  refine key.trans (le_of_eq ?_)
  rw [hε]
  have : Real.exp (3 * K * (s - t₀)) = Real.exp (2 * K * (s - t₀)) * Real.exp (K * (s - t₀)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

/-- Lipschitz dependence of the variational solution on the initial point. -/
lemma IsVarSol.lipschitz (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hJ : IsVarSol V t₀ t₁ x J) {y : E} {J' : ℝ → E →L[ℝ] E} (hJ' : IsVarSol V t₀ t₁ y J')
    {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    ‖J' s - J s‖ ≤ K2 * (s - t₀) * Real.exp (3 * K * (s - t₀)) * ‖y - x‖ := by
  have hK2 := hV2.K2_nonneg
  set ε : ℝ := K2 * Real.exp (2 * K * (s - t₀)) * ‖y - x‖ with hε
  have key := norm_le_of_hasDerivAt_le (f := fun r => J' r - J r)
    (a := t₀) (b := s) (K := K) (ε := ε) (δ := 0) hs.1 K.2 (by positivity)
    (fun r hr => (hJ'.2 r ⟨hr.1, hr.2.trans hs.2⟩).sub (hJ.2 r ⟨hr.1, hr.2.trans hs.2⟩))
    (fun r hr => by
      set A := fderiv ℝ (V r) (gflow V t₀ r x)
      set A' := fderiv ℝ (V r) (gflow V t₀ r y)
      have e : A'.comp (J' r) - A.comp (J r) = A.comp (J' r - J r) + (A' - A).comp (J' r) := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
      rw [e]
      have hr' : r ∈ Icc t₀ t₁ := ⟨hr.1, hr.2.trans hs.2⟩
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; exact hV.norm_fderiv_le r _)
      · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        have h1 := hV2.lip1 r (gflow V t₀ r x) (gflow V t₀ r y)
        have h2 : ‖gflow V t₀ r y - gflow V t₀ r x‖ ≤ ‖y - x‖ * Real.exp (K * (r - t₀)) := by
          have := hV.dist_gflow_le_of_le hr.1 y x
          rwa [dist_eq_norm, dist_eq_norm] at this
        have h3 := hJ'.norm_le hV hr'
        have h5 : Real.exp (K * (r - t₀)) * Real.exp (K * (r - t₀)) ≤
            Real.exp (2 * K * (s - t₀)) := by
          rw [← Real.exp_add]; gcongr; nlinarith [mul_nonneg (NNReal.coe_nonneg K) (sub_nonneg.2 hr.2)]
        calc ‖A' - A‖ * ‖J' r‖
            ≤ (K2 * (‖y - x‖ * Real.exp (K * (r - t₀)))) * Real.exp (K * (r - t₀)) := by
              gcongr
              exact h1.trans (by gcongr)
          _ = K2 * ‖y - x‖ * (Real.exp (K * (r - t₀)) * Real.exp (K * (r - t₀))) := by ring
          _ ≤ K2 * ‖y - x‖ * Real.exp (2 * K * (s - t₀)) := by gcongr
          _ = ε := by rw [hε]; ring)
    (by simp [hJ.1, hJ'.1])
  refine key.trans (le_of_eq ?_)
  rw [hε]
  have : Real.exp (3 * K * (s - t₀)) = Real.exp (2 * K * (s - t₀)) * Real.exp (K * (s - t₀)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

/-- The flow is differentiable, with derivative given by the variational solution. -/
lemma IsVarSol.hasFDerivAt (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hJ : IsVarSol V t₀ t₁ x J) {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    HasFDerivAt (gflow V t₀ s) (J s) x :=
  hasFDerivAt_of_sq_bound fun y => hJ.remainder hV hV2 y hs

omit [CompleteSpace E] in
lemma IsVarSol.continuousOn (hJ : IsVarSol V t₀ t₁ x J) : ContinuousOn J (Icc t₀ t₁) :=
  fun s hs => (hJ.2 s hs).continuousAt.continuousWithinAt

omit [CompleteSpace E] in
/-- Precomposition with `J` has norm at most `‖J‖`. -/
lemma norm_compL_flip_apply_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (J : E →L[ℝ] F) :
    ‖(ContinuousLinearMap.compL ℝ E F G).flip J‖ ≤ ‖J‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg J) fun B => by
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, mul_comm]
    exact B.opNorm_comp_le J

/-- The inhomogeneous term `h ↦ D²V(Φ)[J h] ∘ J` of the second variational equation. -/
def varG (V : ℝ → E → E) (t₀ : ℝ) (x : E) (J : ℝ → E →L[ℝ] E) (s : ℝ) :
    E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E E E).flip (J s)).comp
    ((fderiv ℝ (fderiv ℝ (V s)) (gflow V t₀ s x)).comp (J s))

omit [CompleteSpace E] in
lemma varG_apply (V : ℝ → E → E) (t₀ : ℝ) (x : E) (J : ℝ → E →L[ℝ] E) (s : ℝ) (h : E) :
    varG V t₀ x J s h = (fderiv ℝ (fderiv ℝ (V s)) (gflow V t₀ s x) (J s h)).comp (J s) := rfl

/-- Solutions of the second variational equation. -/
def IsVarSol2 (V : ℝ → E → E) (t₀ t₁ : ℝ) (x : E) (J : ℝ → E →L[ℝ] E)
    (H : ℝ → E →L[ℝ] E →L[ℝ] E) : Prop :=
  H t₀ = 0 ∧ ∀ s ∈ Icc t₀ t₁, HasDerivAt H
    ((ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (V s) (gflow V t₀ s x))).comp (H s) +
      varG V t₀ x J s) s

omit [CompleteSpace E] in
lemma norm_varG_le (hV : GoodField V M K) (hV2 : C2Field V K2 K3) (hJ : IsVarSol V t₀ t₁ x J)
    {s : ℝ} (hs : s ∈ Icc t₀ t₁) : ‖varG V t₀ x J s‖ ≤ K2 * Real.exp (2 * K * (s - t₀)) := by
  unfold varG
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 := norm_compL_flip_apply_le (G := E) (J s)
  have h2 := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (fderiv ℝ (V s)) (gflow V t₀ s x)) (J s)
  have h3 := hJ.norm_le hV hs
  have h4 := hV2.d2 s (gflow V t₀ s x)
  have he : Real.exp (2 * K * (s - t₀)) = Real.exp (K * (s - t₀)) * Real.exp (K * (s - t₀)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  have := hV2.K2_nonneg
  calc ‖(ContinuousLinearMap.compL ℝ E E E).flip (J s)‖ *
        ‖(fderiv ℝ (fderiv ℝ (V s)) (gflow V t₀ s x)).comp (J s)‖
      ≤ Real.exp (K * (s - t₀)) * (K2 * Real.exp (K * (s - t₀))) := by
        gcongr
        · exact h1.trans h3
        · exact h2.trans (by gcongr)
    _ = _ := by ring

lemma exists_varSol2 (hV : GoodField V M K) (hV2 : C2Field V K2 K3) (h01 : t₀ ≤ t₁)
    (hJ : IsVarSol V t₀ t₁ x J) : ∃ H, IsVarSol2 V t₀ t₁ x J H := by
  have hcA := continuous_A hV hV2 t₀ x
  have hcA2 := continuous_A2 hV hV2 t₀ x
  have hc1 : Continuous fun s =>
      ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (V s) (gflow V t₀ s x)) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp hcA
  have hc2 : ContinuousOn (varG V t₀ x J) (Icc t₀ t₁) := by
    have h1 : ContinuousOn (fun s => (ContinuousLinearMap.compL ℝ E E E).flip (J s))
        (Icc t₀ t₁) :=
      (ContinuousLinearMap.compL ℝ E E E).flip.continuous.comp_continuousOn hJ.continuousOn
    have h2 : ContinuousOn (fun s => (fderiv ℝ (fderiv ℝ (V s)) (gflow V t₀ s x)).comp (J s))
        (Icc t₀ t₁) := hcA2.continuousOn.clm_comp hJ.continuousOn
    exact h1.clm_comp h2
  have hb1 : ∀ s, ‖ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (V s) (gflow V t₀ s x))‖ ≤ K :=
    fun s => (norm_compL_apply_le _).trans (hV.norm_fderiv_le s _)
  have hK2 := hV2.K2_nonneg
  have hb2 : ∀ s ∈ Icc t₀ t₁, ‖varG V t₀ x J s‖ ≤ K2 * Real.exp (2 * K * (t₁ - t₀)) :=
    fun s hs => (norm_varG_le hV hV2 hJ hs).trans (by gcongr; exact hs.2)
  obtain ⟨H, hH0, hH⟩ := exists_affODE_on (F := E →L[ℝ] E →L[ℝ] E)
    (W := fun s Hm => (ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (V s) (gflow V t₀ s x))).comp Hm
      + varG V t₀ x J s) h01 K.2 (mul_nonneg hK2 (Real.exp_pos _).le)
    (fun Hm => (hc1.clm_comp continuous_const).continuousOn.add hc2)
    (fun s _ y z => by
      rw [add_sub_add_right_eq_sub, ← ContinuousLinearMap.comp_sub]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hb1 s))
    (fun s hs y => by
      refine (norm_add_le (E := E →L[ℝ] E →L[ℝ] E) _ _).trans (add_le_add ?_ (hb2 s hs))
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hb1 s)) 0
  exact ⟨H, hH0, hH⟩

variable {H : ℝ → E →L[ℝ] E →L[ℝ] E}

omit [CompleteSpace E] in
lemma IsVarSol2.norm_le (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hJ : IsVarSol V t₀ t₁ x J) (hH : IsVarSol2 V t₀ t₁ x J H) {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    ‖H s‖ ≤ K2 * (s - t₀) * Real.exp (3 * K * (s - t₀)) := by
  have hK2 := hV2.K2_nonneg
  have key := norm_le_of_hasDerivAt_le (F := E →L[ℝ] E →L[ℝ] E) (f := H) (a := t₀) (b := s)
    (K := K) (ε := K2 * Real.exp (2 * K * (s - t₀))) (δ := 0) hs.1 K.2 (by positivity)
    (fun r hr => hH.2 r ⟨hr.1, hr.2.trans hs.2⟩) (fun r hr => by
      have hr' : r ∈ Icc t₀ t₁ := ⟨hr.1, hr.2.trans hs.2⟩
      refine (norm_add_le (E := E →L[ℝ] E →L[ℝ] E) _ _).trans (add_le_add ?_ ?_)
      · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact (norm_compL_apply_le _).trans (hV.norm_fderiv_le r _)
      · refine (norm_varG_le hV hV2 hJ hr').trans ?_
        gcongr; exact hr.2) (by rw [hH.1]; exact (norm_zero (E := E →L[ℝ] E →L[ℝ] E)).le)
  refine key.trans (le_of_eq ?_)
  have : Real.exp (3 * K * (s - t₀)) = Real.exp (2 * K * (s - t₀)) * Real.exp (K * (s - t₀)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

/-- The quadratic remainder estimate for the variational solution. -/
lemma IsVarSol2.remainder (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hJ : IsVarSol V t₀ t₁ x J) (hH : IsVarSol2 V t₀ t₁ x J H) {y : E}
    {J' : ℝ → E →L[ℝ] E} (hJ' : IsVarSol V t₀ t₁ y J') {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    ‖J' s - J s - H s (y - x)‖ ≤ (s - t₀) * Real.exp (K * (s - t₀)) *
      ((K3 * Real.exp (K * (s - t₀)) ^ 3 + 2 * K2 * (K2 * (s - t₀) *
        Real.exp (3 * K * (s - t₀))) * Real.exp (K * (s - t₀))) * ‖y - x‖ ^ 2) := by
  have hK2 := hV2.K2_nonneg
  have hK3 := hV2.K3_nonneg
  set es := Real.exp (K * (s - t₀)) with hes
  set cs := K2 * (s - t₀) * Real.exp (3 * K * (s - t₀)) with hcs
  have hs0 : 0 ≤ s - t₀ := sub_nonneg.2 hs.1
  have hcs0 : 0 ≤ cs := by positivity
  set ε := (K3 * es ^ 3 + 2 * K2 * cs * es) * ‖y - x‖ ^ 2 with hε
  have key := norm_le_of_hasDerivAt_le (F := E →L[ℝ] E)
    (f := fun r => J' r - J r - H r (y - x))
    (f' := fun r => (fderiv ℝ (V r) (gflow V t₀ r y)).comp (J' r) -
      (fderiv ℝ (V r) (gflow V t₀ r x)).comp (J r) -
      (((ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (V r) (gflow V t₀ r x))).comp (H r) +
        varG V t₀ x J r) (y - x) + H r 0))
    (a := t₀) (b := s) (K := K) (ε := ε) (δ := 0) hs.1 K.2 (by positivity)
    (fun r hr => ((hJ'.2 r ⟨hr.1, hr.2.trans hs.2⟩).sub (hJ.2 r ⟨hr.1, hr.2.trans hs.2⟩)).sub
      ((hH.2 r ⟨hr.1, hr.2.trans hs.2⟩).clm_apply (hasDerivAt_const r (y - x))))
    (fun r hr => by
      beta_reduce
      have hr' : r ∈ Icc t₀ t₁ := ⟨hr.1, hr.2.trans hs.2⟩
      set A := fderiv ℝ (V r) (gflow V t₀ r x)
      set A' := fderiv ℝ (V r) (gflow V t₀ r y)
      set B := fderiv ℝ (fderiv ℝ (V r)) (gflow V t₀ r x)
      set δ := gflow V t₀ r y - gflow V t₀ r x
      set u := J r (y - x)
      have e : A'.comp (J' r) - A.comp (J r) -
          (((ContinuousLinearMap.compL ℝ E E E A).comp (H r) + varG V t₀ x J r) (y - x) +
            H r 0) = A.comp (J' r - J r - H r (y - x)) +
          ((A' - A - B δ).comp (J' r) + (B (δ - u)).comp (J' r) + (B u).comp (J' r - J r)) := by
        ext v
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, varG_apply, map_zero,
          add_zero, map_sub, u]
        abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; exact hV.norm_fderiv_le r _)
      have her : Real.exp (K * (r - t₀)) ≤ es := by
        rw [hes]; gcongr; exact hr.2
      have hcr : K2 * (r - t₀) * Real.exp (3 * K * (r - t₀)) ≤ cs := by
        rw [hcs]; have := sub_nonneg.2 hr.1; gcongr
        · exact hr.2
        · exact hr.2
      have hδ : ‖δ‖ ≤ es * ‖y - x‖ := by
        have := hV.dist_gflow_le_of_le hr.1 y x
        rw [dist_eq_norm, dist_eq_norm] at this
        exact this.trans (by rw [mul_comm]; gcongr)
      have hJ'n : ‖J' r‖ ≤ es := (hJ'.norm_le hV hr').trans her
      have hJn : ‖J r‖ ≤ es := (hJ.norm_le hV hr').trans her
      have hu : ‖u‖ ≤ es * ‖y - x‖ := ((J r).le_opNorm _).trans (by gcongr)
      have hrem : ‖δ - u‖ ≤ cs * ‖y - x‖ ^ 2 :=
        (hJ.remainder hV hV2 y hr').trans (by gcongr)
      have hlip : ‖J' r - J r‖ ≤ cs * ‖y - x‖ :=
        (hJ.lipschitz hV hV2 hJ' hr').trans (by gcongr)
      have hT : ‖A' - A - B δ‖ ≤ K3 * ‖δ‖ ^ 2 := hV2.taylor1 r _ _
      have hB : ‖B‖ ≤ K2 := hV2.d2 r _
      have es0 : 0 ≤ es := (Real.exp_pos _).le
      have h1 : ‖(A' - A - B δ).comp (J' r)‖ ≤ K3 * es ^ 3 * ‖y - x‖ ^ 2 := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        calc ‖A' - A - B δ‖ * ‖J' r‖ ≤ (K3 * (es * ‖y - x‖) ^ 2) * es := by
              gcongr
              exact hT.trans (by gcongr)
          _ = K3 * es ^ 3 * ‖y - x‖ ^ 2 := by ring
      have h2 : ‖(B (δ - u)).comp (J' r)‖ ≤ K2 * cs * es * ‖y - x‖ ^ 2 := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        calc ‖B (δ - u)‖ * ‖J' r‖ ≤ (K2 * (cs * ‖y - x‖ ^ 2)) * es := by
              gcongr
              exact (B.le_opNorm _).trans (by gcongr)
          _ = K2 * cs * es * ‖y - x‖ ^ 2 := by ring
      have h3 : ‖(B u).comp (J' r - J r)‖ ≤ K2 * cs * es * ‖y - x‖ ^ 2 := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        calc ‖B u‖ * ‖J' r - J r‖ ≤ (K2 * (es * ‖y - x‖)) * (cs * ‖y - x‖) := by
              gcongr
              exact (B.le_opNorm _).trans (by gcongr)
          _ = K2 * cs * es * ‖y - x‖ ^ 2 := by ring
      calc ‖(A' - A - B δ).comp (J' r) + (B (δ - u)).comp (J' r) + (B u).comp (J' r - J r)‖
          ≤ ‖(A' - A - B δ).comp (J' r)‖ + ‖(B (δ - u)).comp (J' r)‖ +
              ‖(B u).comp (J' r - J r)‖ := norm_add₃_le
        _ ≤ K3 * es ^ 3 * ‖y - x‖ ^ 2 + K2 * cs * es * ‖y - x‖ ^ 2 +
              K2 * cs * es * ‖y - x‖ ^ 2 := add_le_add (add_le_add h1 h2) h3
        _ = ε := by rw [hε]; ring)
    (by simp [hJ.1, hJ'.1, hH.1])
  refine key.trans (le_of_eq ?_)
  rw [hε]; ring

set_option maxHeartbeats 1000000 in
/-- Lipschitz dependence of the second variational solution on the initial point. -/
lemma IsVarSol2.lipschitz (hV : GoodField V M K) (hV2 : C2Field V K2 K3)
    (hJ : IsVarSol V t₀ t₁ x J) (hH : IsVarSol2 V t₀ t₁ x J H) {y : E}
    {J' : ℝ → E →L[ℝ] E} (hJ' : IsVarSol V t₀ t₁ y J') {H' : ℝ → E →L[ℝ] E →L[ℝ] E}
    (hH' : IsVarSol2 V t₀ t₁ y J' H') {s : ℝ} (hs : s ∈ Icc t₀ t₁) :
    ‖H' s - H s‖ ≤ (s - t₀) * Real.exp (K * (s - t₀)) *
      ((3 * K2 * (K2 * (s - t₀) * Real.exp (3 * K * (s - t₀))) * Real.exp (K * (s - t₀)) +
        K3 * Real.exp (K * (s - t₀)) ^ 3) * ‖y - x‖) := by
  have hK2 := hV2.K2_nonneg
  have hK3 := hV2.K3_nonneg
  set es := Real.exp (K * (s - t₀)) with hes
  set cs := K2 * (s - t₀) * Real.exp (3 * K * (s - t₀)) with hcs
  have hs0 : 0 ≤ s - t₀ := sub_nonneg.2 hs.1
  have hcs0 : 0 ≤ cs := by positivity
  have es0 : 0 ≤ es := (Real.exp_pos _).le
  set ε := (3 * K2 * cs * es + K3 * es ^ 3) * ‖y - x‖ with hε
  have key := norm_le_of_hasDerivAt_le (F := E →L[ℝ] E →L[ℝ] E)
    (f := fun r => H' r - H r)
    (f' := fun r => ((ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (V r) (gflow V t₀ r y))).comp
        (H' r) + varG V t₀ y J' r) -
      ((ContinuousLinearMap.compL ℝ E E E (fderiv ℝ (V r) (gflow V t₀ r x))).comp (H r) +
        varG V t₀ x J r))
    (a := t₀) (b := s) (K := K) (ε := ε) (δ := 0) hs.1 K.2 (by positivity)
    (fun r hr => HasDerivAt.sub (F := E →L[ℝ] E →L[ℝ] E) (hH'.2 r ⟨hr.1, hr.2.trans hs.2⟩)
      (hH.2 r ⟨hr.1, hr.2.trans hs.2⟩))
    (fun r hr => by
      beta_reduce
      have hr' : r ∈ Icc t₀ t₁ := ⟨hr.1, hr.2.trans hs.2⟩
      set A := fderiv ℝ (V r) (gflow V t₀ r x)
      set A' := fderiv ℝ (V r) (gflow V t₀ r y)
      set B := fderiv ℝ (fderiv ℝ (V r)) (gflow V t₀ r x)
      set B' := fderiv ℝ (fderiv ℝ (V r)) (gflow V t₀ r y)
      have e : (ContinuousLinearMap.compL ℝ E E E A').comp (H' r) + varG V t₀ y J' r -
          ((ContinuousLinearMap.compL ℝ E E E A).comp (H r) + varG V t₀ x J r) =
          (ContinuousLinearMap.compL ℝ E E E A).comp (H' r - H r) + (((ContinuousLinearMap.compL ℝ E E E) (A' - A)).comp (H' r) +
            ((((ContinuousLinearMap.compL ℝ E E E).flip) (J' r - J r)).comp (B'.comp (J' r)) + (((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp ((B' - B).comp (J' r)) +
              (((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp (B.comp (J' r - J r)))) := by
        simp only [varG, map_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
        abel
      rw [e]
      have her : Real.exp (K * (r - t₀)) ≤ es := by
        rw [hes]; gcongr; exact hr.2
      have hcr : K2 * (r - t₀) * Real.exp (3 * K * (r - t₀)) ≤ cs := by
        rw [hcs]; have := sub_nonneg.2 hr.1; gcongr
        · exact hr.2
        · exact hr.2
      have hδ : ‖gflow V t₀ r y - gflow V t₀ r x‖ ≤ es * ‖y - x‖ := by
        have := hV.dist_gflow_le_of_le hr.1 y x
        rw [dist_eq_norm, dist_eq_norm] at this
        exact this.trans (by rw [mul_comm]; gcongr)
      have hJ'n : ‖J' r‖ ≤ es := (hJ'.norm_le hV hr').trans her
      have hJn : ‖J r‖ ≤ es := (hJ.norm_le hV hr').trans her
      have hlip : ‖J' r - J r‖ ≤ cs * ‖y - x‖ :=
        (hJ.lipschitz hV hV2 hJ' hr').trans (by gcongr)
      have hH'n : ‖H' r‖ ≤ cs := (hH'.norm_le hV hV2 hJ' hr').trans hcr
      have hAA : ‖A' - A‖ ≤ K2 * (es * ‖y - x‖) :=
        (hV2.lip1 r _ _).trans (by gcongr)
      have hBB : ‖B' - B‖ ≤ K3 * (es * ‖y - x‖) :=
        (hV2.lip2 r _ _).trans (by gcongr)
      have hB : ‖B‖ ≤ K2 := hV2.d2 r _
      have hB' : ‖B'‖ ≤ K2 := hV2.d2 r _
      refine (norm_add_le (E := E →L[ℝ] E →L[ℝ] E) _ _).trans (add_le_add ?_ ?_)
      · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact (norm_compL_apply_le _).trans (hV.norm_fderiv_le r _)
      have h1 : ‖((ContinuousLinearMap.compL ℝ E E E) (A' - A)).comp (H' r)‖ ≤ K2 * cs * es * ‖y - x‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        calc ‖(ContinuousLinearMap.compL ℝ E E E) (A' - A)‖ * ‖H' r‖ ≤ (K2 * (es * ‖y - x‖)) * cs := by
              gcongr
              exact (norm_compL_apply_le _).trans hAA
          _ = K2 * cs * es * ‖y - x‖ := by ring
      have h2 : ‖(((ContinuousLinearMap.compL ℝ E E E).flip) (J' r - J r)).comp (B'.comp (J' r))‖ ≤ K2 * cs * es * ‖y - x‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        calc ‖((ContinuousLinearMap.compL ℝ E E E).flip) (J' r - J r)‖ * ‖B'.comp (J' r)‖ ≤ (cs * ‖y - x‖) * (K2 * es) := by
              gcongr
              · exact (norm_compL_flip_apply_le (F := E) (G := E) _).trans hlip
              · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
          _ = K2 * cs * es * ‖y - x‖ := by ring
      have h3 : ‖(((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp ((B' - B).comp (J' r))‖ ≤ K3 * es ^ 3 * ‖y - x‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        calc ‖((ContinuousLinearMap.compL ℝ E E E).flip) (J r)‖ * ‖(B' - B).comp (J' r)‖ ≤ es * ((K3 * (es * ‖y - x‖)) * es) := by
              gcongr
              · exact (norm_compL_flip_apply_le (F := E) (G := E) _).trans hJn
              · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr)
          _ = K3 * es ^ 3 * ‖y - x‖ := by ring
      have h4 : ‖(((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp (B.comp (J' r - J r))‖ ≤ K2 * cs * es * ‖y - x‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        calc ‖((ContinuousLinearMap.compL ℝ E E E).flip) (J r)‖ * ‖B.comp (J' r - J r)‖ ≤ es * (K2 * (cs * ‖y - x‖)) := by
              refine mul_le_mul ((norm_compL_flip_apply_le (F := E) (G := E) _).trans hJn) ?_
                (norm_nonneg (B.comp (J' r - J r))) es0
              exact (ContinuousLinearMap.opNorm_comp_le B (J' r - J r)).trans
                (mul_le_mul hB hlip (norm_nonneg (J' r - J r)) hK2)
          _ = K2 * cs * es * ‖y - x‖ := by ring
      calc ‖((ContinuousLinearMap.compL ℝ E E E) (A' - A)).comp (H' r) + ((((ContinuousLinearMap.compL ℝ E E E).flip) (J' r - J r)).comp (B'.comp (J' r)) +
              (((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp ((B' - B).comp (J' r)) + (((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp (B.comp (J' r - J r)))‖
          ≤ ‖((ContinuousLinearMap.compL ℝ E E E) (A' - A)).comp (H' r)‖ + (‖(((ContinuousLinearMap.compL ℝ E E E).flip) (J' r - J r)).comp (B'.comp (J' r))‖ +
              ‖(((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp ((B' - B).comp (J' r))‖ +
              ‖(((ContinuousLinearMap.compL ℝ E E E).flip) (J r)).comp (B.comp (J' r - J r))‖) :=
            (norm_add_le (E := E →L[ℝ] E →L[ℝ] E) _ _).trans
              (add_le_add le_rfl (norm_add₃_le (E := E →L[ℝ] E →L[ℝ] E)))
        _ ≤ K2 * cs * es * ‖y - x‖ + (K2 * cs * es * ‖y - x‖ + K3 * es ^ 3 * ‖y - x‖ +
              K2 * cs * es * ‖y - x‖) := add_le_add h1 (add_le_add (add_le_add h2 h3) h4)
        _ = ε := by rw [hε]; ring)
    (by show ‖H' t₀ - H t₀‖ ≤ 0
        rw [hH.1, hH'.1, sub_zero]; exact (norm_zero (E := E →L[ℝ] E →L[ℝ] E)).le)
  refine key.trans (le_of_eq ?_)
  rw [hε]; ring

end Forward

end AnomDiss
