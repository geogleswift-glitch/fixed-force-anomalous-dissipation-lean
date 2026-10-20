module

public import RequestProject.DampedSmooth

/-!
# Liouville's theorem in the plane

Flows of divergence-free smooth fields on `ℝ²` preserve area: `det DΦ = 1`.  The field
`B_{μ,ω}` is divergence free.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- Zero divergence of a linear map of `ℝ²`. -/
def TraceFree (A : Pt 2 →L[ℝ] Pt 2) : Prop :=
  A (Pi.single 0 1) 0 + A (Pi.single 1 1) 1 = 0

lemma clm_apply_pt2 (A : Pt 2 →L[ℝ] Pt 2) (v : Pt 2) :
    A v = v 0 • A (Pi.single 0 1) + v 1 • A (Pi.single 1 1) := by
  have hv : v = v 0 • (Pi.single 0 1 : Pt 2) + v 1 • (Pi.single 1 1 : Pt 2) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

/-- The determinant of the Jacobian, in terms of the columns of the derivative. -/
lemma det_jac_eq (Φ : Pt 2 → Pt 2) (x : Pt 2) :
    (jac Φ x).det = fderiv ℝ Φ x (Pi.single 0 1) 0 * fderiv ℝ Φ x (Pi.single 1 1) 1 -
      fderiv ℝ Φ x (Pi.single 1 1) 0 * fderiv ℝ Φ x (Pi.single 0 1) 1 := by
  rw [Matrix.det_fin_two]
  simp [jac]

variable {V : ℝ → Pt 2 → Pt 2} {B : ℕ → ℝ}

/-- **Liouville** (forward times). -/
theorem det_jac_gflow_fwd (hV : SmoothField V B)
    (hdiv : ∀ s y, TraceFree (fderiv ℝ (V s) y)) {t₀ t : ℝ} (h01 : t₀ ≤ t) (x : Pt 2) :
    (jac (gflow V t₀ t) x).det = 1 := by
  obtain ⟨J, hJ⟩ := exists_varSol hV.toGood hV.toC2 h01 x
  have hD : fderiv ℝ (gflow V t₀ t) x = J t :=
    (hJ.hasFDerivAt hV.toGood hV.toC2 ⟨h01, le_rfl⟩).fderiv
  rw [det_jac_eq, hD]
  set e0 : Pt 2 := Pi.single 0 1
  set e1 : Pt 2 := Pi.single 1 1
  set d : ℝ → ℝ := fun s => J s e0 0 * J s e1 1 - J s e1 0 * J s e0 1 with hd
  have hcomp : ∀ s ∈ Icc t₀ t, ∀ (v : Pt 2) (i : Fin 2),
      HasDerivAt (fun s => J s v i) ((fderiv ℝ (V s) (gflow V t₀ s x)).comp (J s) v i) s := by
    intro s hs v i
    have h := hJ.2 s hs
    have h2 := ((ContinuousLinearMap.apply ℝ (Pt 2) v).hasFDerivAt.comp_hasDerivAt s h)
    exact (hasDerivAt_pi.1 h2) i |>.congr_deriv (by simp)
  have hder : ∀ s ∈ Icc t₀ t, HasDerivWithinAt d 0 (Icc t₀ t) s := by
    intro s hs
    set A := fderiv ℝ (V s) (gflow V t₀ s x)
    have h00 := hcomp s hs e0 0
    have h11 := hcomp s hs e1 1
    have h10 := hcomp s hs e1 0
    have h01' := hcomp s hs e0 1
    have := ((h00.mul h11).sub (h10.mul h01')).hasDerivWithinAt (s := Icc t₀ t)
    convert this using 1
    simp only [ContinuousLinearMap.comp_apply]
    rw [clm_apply_pt2 A (J s e0), clm_apply_pt2 A (J s e1)]
    have htr := hdiv s (gflow V t₀ s x)
    unfold TraceFree at htr
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(J s e0 0 * J s e1 1 - J s e1 0 * J s e0 1)) * htr
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := d) (C := 0) hder
    (fun _ _ => by simp) t ⟨h01, le_rfl⟩
  have hd0 : d t₀ = 1 := by simp [hd, hJ.1, e0, e1]
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, hd0] at key
  exact key

lemma traceFree_neg {A : Pt 2 →L[ℝ] Pt 2} (h : TraceFree A) : TraceFree (-A) := by
  unfold TraceFree at *
  simp only [ContinuousLinearMap.neg_apply, Pi.neg_apply]
  linarith

/-- **Liouville's theorem**: flows of divergence-free smooth fields preserve area. -/
theorem det_jac_gflow (hV : SmoothField V B) (hdiv : ∀ s y, TraceFree (fderiv ℝ (V s) y))
    (t₀ t : ℝ) (x : Pt 2) : (jac (gflow V t₀ t) x).det = 1 := by
  rcases le_total t₀ t with h | h
  · exact det_jac_gflow_fwd hV hdiv h x
  · have he : gflow V t₀ t = gflow (GoodField.revField V (2 * t₀)) t₀ (2 * t₀ - t) :=
      funext fun y => hV.toGood.gflow_rev t₀ t y
    rw [he]
    refine det_jac_gflow_fwd (hV.rev (2 * t₀)) (fun s y => ?_) (by linarith) x
    have : fderiv ℝ (GoodField.revField V (2 * t₀) s) y = -fderiv ℝ (V (2 * t₀ - s)) y :=
      fderiv_neg (f := V (2 * t₀ - s))
    rw [this]
    exact traceFree_neg (hdiv _ _)

/-- A coordinate of `f` which is constant along a direction has zero derivative there. -/
lemma fderiv_coord_eq_zero {f : Pt 2 → Pt 2} {y : Pt 2} (hf : DifferentiableAt ℝ f y) (v : Pt 2)
    (i : Fin 2) (hc : ∀ t : ℝ, f (y + t • v) i = f y i) : fderiv ℝ f y v i = 0 := by
  have hline : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hf' : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => f (y + t • v)) (fderiv ℝ f y v) 0 :=
    hf'.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => f (y + t • v) i) (fderiv ℝ f y v i) 0 :=
    (hasDerivAt_pi.1 h1) i
  have h3 : HasDerivAt (fun t : ℝ => f (y + t • v) i) 0 0 := by
    have : (fun t : ℝ => f (y + t • v) i) = fun _ => f y i := funext hc
    rw [this]; exact hasDerivAt_const _ _
  exact h2.unique h3

variable {L M : ℕ} {S : ℕ → ℝ}

/-- `B_{μ,ω}` is divergence free. -/
theorem dampedB_traceFree (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L)
    (s : ℝ) (y : Pt 2) : TraceFree (fderiv ℝ (dampedB cf μ w s) y) := by
  have hd : DifferentiableAt ℝ (dampedB cf μ w s) y :=
    ((dampedB_smooth cf hμ w).contDiff_slice s).differentiable (by simp) y
  unfold TraceFree
  rw [fderiv_coord_eq_zero hd _ 0 fun t => ?_, fderiv_coord_eq_zero hd _ 1 fun t => ?_, add_zero]
  · simp [dampedB_eq, eField, eBasis, Fin.sum_univ_four]
  · simp [dampedB_eq, eField, eBasis, Fin.sum_univ_four]

end AnomDiss
