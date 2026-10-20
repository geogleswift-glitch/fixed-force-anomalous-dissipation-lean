module

public import RequestProject.FlowBasic

/-!
# Dependence of flow maps on the initial time

For a field which is Lipschitz in time, `Φ_{r → s}(z) = z + (s - r) V(s, z) + O((s - r)²)`
uniformly in `z`.  Consequently, along a differentiable curve `y`, the map
`r ↦ Φ_{r → s}(y r)` has derivative `y'(s) - V(s, y(s))` at `r = s`, and for the backward maps
`Y_r = Φ_{r → t₀}` the chain rule gives the transport equation `∂ᵣ (g ∘ Y_r) = -V · ∇(g ∘ Y_r)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real Asymptotics
open scoped NNReal

noncomputable section

namespace AnomDiss

namespace GoodField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {V : ℝ → E → E} {M K : ℝ≥0}

/-- Second-order expansion of a flow map in the initial time, uniformly in space. -/
lemma norm_gflow_sub_sub_smul_le (hV : GoodField V M K) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) (r s : ℝ) (z : E) :
    ‖gflow V r s z - z - (s - r) • V s z‖ ≤ (Lt + K * M) * (s - r) ^ 2 := by
  have hLt0 : 0 ≤ Lt := by
    have := hLt (r + 1) r z
    have h0 : (0:ℝ) ≤ Lt * |r + 1 - r| := (norm_nonneg _).trans this
    simpa using h0
  set H : ℝ → E := fun u => gflow V r u z - z - (u - r) • V s z with hH
  have hd : ∀ u, HasDerivAt H (V u (gflow V r u z) - V s z) u := by
    intro u
    have h1 := ((hasDerivAt_id u).sub_const r).smul_const (V s z)
    have := ((hV.hasDerivAt_gflow r u z).sub_const z).fun_sub h1
    simpa using this
  have hbd : ∀ u ∈ uIcc r s, ‖V u (gflow V r u z) - V s z‖ ≤ (Lt + K * M) * |s - r| := by
    intro u hu
    have hu1 : |u - s| ≤ |s - r| := by
      rcases le_total r s with h | h
      · rw [uIcc_of_le h] at hu
        rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonneg (by linarith)]; linarith [hu.1]
      · rw [uIcc_of_ge h] at hu
        rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonpos (by linarith)]; linarith [hu.2]
    have hu2 : |u - r| ≤ |s - r| := by
      rcases le_total r s with h | h
      · rw [uIcc_of_le h] at hu
        rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonneg (by linarith)]; linarith [hu.2]
      · rw [uIcc_of_ge h] at hu
        rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith)]; linarith [hu.1]
    have e1 := hLt u s (gflow V r u z)
    have e2 := (hV.lip s).dist_le_mul (gflow V r u z) z
    have e3 := hV.norm_gflow_sub_le r u z
    rw [dist_eq_norm, dist_eq_norm] at e2
    calc ‖V u (gflow V r u z) - V s z‖
        = ‖(V u (gflow V r u z) - V s (gflow V r u z)) + (V s (gflow V r u z) - V s z)‖ := by
          congr 1; abel
      _ ≤ Lt * |u - s| + K * (M * |u - r|) := by
          refine (norm_add_le _ _).trans (add_le_add e1 (e2.trans ?_))
          gcongr
      _ ≤ Lt * |s - r| + K * (M * |s - r|) := by gcongr
      _ = (Lt + K * M) * |s - r| := by ring
  have key := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) hbd left_mem_uIcc right_mem_uIcc
  have eH : H s - H r = gflow V r s z - z - (s - r) • V s z := by
    simp only [hH, hV.gflow_self, sub_self, zero_smul, sub_zero]
  rw [eH, Real.norm_eq_abs] at key
  calc _ ≤ (Lt + K * M) * |s - r| * |s - r| := key
    _ = _ := by rw [mul_assoc, ← sq, sq_abs]

/-- Derivative of `r ↦ Φ_{r → s}(y r)` at `r = s`. -/
lemma hasDerivAt_gflow_initial (hV : GoodField V M K) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) {y : ℝ → E} {y' : E} {s : ℝ}
    (hy : HasDerivAt y y' s) :
    HasDerivAt (fun r => gflow V r s (y r)) (y' - V s (y s)) s := by
  rw [hasDerivAt_iff_isLittleO]
  have e : ∀ r, gflow V r s (y r) - gflow V s s (y s) - (r - s) • (y' - V s (y s)) =
      (gflow V r s (y r) - y r - (s - r) • V s (y r)) +
        (s - r) • (V s (y r) - V s (y s)) + (y r - y s - (r - s) • y') := by
    intro r
    rw [hV.gflow_self]
    simp only [smul_sub, sub_smul]
    abel
  simp only [e]
  refine (IsLittleO.add (IsLittleO.add ?_ ?_) (hasDerivAt_iff_isLittleO.1 hy))
  · -- the quadratic remainder
    have h1 : (fun r => gflow V r s (y r) - y r - (s - r) • V s (y r)) =O[𝓝 s]
        fun r => ‖r - s‖ ^ 2 := by
      refine IsBigO.of_bound (Lt + K * M) (Eventually.of_forall fun r => ?_)
      refine (hV.norm_gflow_sub_sub_smul_le hLt r s (y r)).trans (le_of_eq ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs,
        ← sq_abs (s - r), abs_sub_comm, sq_abs]
    exact h1.trans_isLittleO (isLittleO_pow_sub_sub s one_lt_two)
  · -- continuity of the field along the curve
    have h1 : (fun r : ℝ => s - r) =O[𝓝 s] fun r => r - s :=
      IsBigO.of_bound 1 (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, one_mul])
    have h2 : (fun r => V s (y r) - V s (y s)) =o[𝓝 s] fun _ => (1 : ℝ) := by
      rw [isLittleO_one_iff]
      have hc : ContinuousAt (fun r => V s (y r)) s :=
        (hV.lip s).continuous.continuousAt.comp hy.continuousAt
      have := (ContinuousAt.tendsto hc).sub_const (V s (y s))
      simpa using this
    have := h1.smul_isLittleO h2
    simpa using this

/-- Transport equation for the backward maps `Y_r = Φ_{r → t₀}` along a curve. -/
lemma hasDerivAt_comp_gflow_back (hV : GoodField V M K) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → F} (t₀ : ℝ) {y : ℝ → E} {y' : E} {s : ℝ}
    (hg : DifferentiableAt ℝ (g ∘ gflow V s t₀) (y s)) (hy : HasDerivAt y y' s) :
    HasDerivAt (fun r => g (gflow V r t₀ (y r)))
      (fderiv ℝ (g ∘ gflow V s t₀) (y s) (y' - V s (y s))) s := by
  have e : (fun r => g (gflow V r t₀ (y r))) = (g ∘ gflow V s t₀) ∘ fun r => gflow V r s (y r) := by
    funext r
    simp only [Function.comp_apply, hV.gflow_gflow]
  rw [e]
  have h := hV.hasDerivAt_gflow_initial hLt hy
  have hs : gflow V s s (y s) = y s := hV.gflow_self s (y s)
  rw [← hs] at hg
  have := hg.hasFDerivAt.comp_hasDerivAt s h
  rwa [hs] at this

end GoodField

end AnomDiss
