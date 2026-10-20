module

public import RequestProject.FlowSmooth
public import Mathlib

/-!
# The augmented (variational) field

For a smooth field `V` on a finite-dimensional space `E`, the pair `(φ, Dφ)` of a flow and its
derivative is a solution of the field `W(s, (x, J)) = (V(s, x), DV(s, x) ∘ χ(J))` on
`E × (E →L E)`, where `χ` is a smooth truncation equal to the identity on a large ball.  `W` is
again a smooth field.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff NNReal

noncomputable section

namespace AnomDiss

section Trunc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A smooth bump on `F`, equal to `1` on the closed ball of radius `R`. -/
def truncBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : F) := ⟨R, R + 1, hR, by linarith⟩

/-- The smooth truncation `χ_R(J) = φ_R(J) • J`. -/
def truncMap (R : ℝ) (hR : 0 < R) (J : F) : F := (truncBump (F := F) R hR) J • J

lemma contDiff_truncMap (R : ℝ) (hR : 0 < R) : ContDiff ℝ ∞ (truncMap (F := F) R hR) :=
  (truncBump R hR).contDiff.smul contDiff_id

lemma truncMap_eq (R : ℝ) (hR : 0 < R) {J : F} (hJ : ‖J‖ ≤ R) : truncMap R hR J = J := by
  have : J ∈ Metric.closedBall (0 : F) (truncBump (F := F) R hR).rIn := by
    simpa [truncBump] using hJ
  simp [truncMap, (truncBump R hR).one_of_mem_closedBall this]

lemma hasCompactSupport_truncMap (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (truncMap (F := F) R hR) :=
  (truncBump R hR).hasCompactSupport.smul_right

lemma truncMap_bounds (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ∃ C, ∀ J : F, ‖iteratedFDeriv ℝ j (truncMap R hR) J‖ ≤ C :=
  ((contDiff_truncMap R hR).continuous_iteratedFDeriv
    (by exact_mod_cast natCast_le_inf j)).bounded_above_of_compact_support
    ((hasCompactSupport_truncMap R hR).iteratedFDeriv j)

end Trunc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_comp_clm_le' {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (g : G →L[ℝ] E) (hg : ‖g‖ ≤ 1) (x : G) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv ℝ i (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ := by
  rw [g.iteratedFDeriv_comp_right hf x hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (g x)‖ * ∏ _ : Fin i, ‖g‖ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hg
    _ = _ := mul_one _

lemma norm_iteratedFDeriv_comp_clm_le {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) (g : G →L[ℝ] E)
    (hg : ‖g‖ ≤ 1) (x : G) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ := by
  rw [g.iteratedFDeriv_comp_right hf x (by exact_mod_cast natCast_le_inf i)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (g x)‖ * ∏ _ : Fin i, ‖g‖ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hg
    _ = _ := mul_one _

/-- The augmented field `W(s, (x, J)) = (V(s, x), DV(s, x) ∘ χ(J))`. -/
def augField (V : ℝ → E → E) (χ : (E →L[ℝ] E) → (E →L[ℝ] E)) (s : ℝ)
    (z : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (V s z.1, (fderiv ℝ (V s) z.1).comp (χ z.2))

/-- Bounds for the augmented field in terms of those of `V` and `χ`. -/
def augBound (B Bχ : ℕ → ℝ) (j : ℕ) : ℝ :=
  B j + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B (i + 1) * Bχ (j - i)

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem SmoothField.aug {V : ℝ → E → E} {B : ℕ → ℝ} (hV : SmoothField V B)
    {χ : (E →L[ℝ] E) → (E →L[ℝ] E)} (hχ : ContDiff ℝ ∞ χ) {Bχ : ℕ → ℝ}
    (hBχ : ∀ j J, ‖iteratedFDeriv ℝ j χ J‖ ≤ Bχ j) :
    SmoothField (augField V χ) (augBound B Bχ) where
  smooth := by
    have h1 : ContDiff ℝ ∞ fun p : ℝ × (E × (E →L[ℝ] E)) => V p.1 p.2.1 :=
      hV.smooth.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
    have h2 : ContDiff ℝ ∞ fun p : ℝ × (E × (E →L[ℝ] E)) => fderiv ℝ (V p.1) p.2.1 :=
      hV.contDiff_fderiv_joint.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
    have h3 : ContDiff ℝ ∞ fun p : ℝ × (E × (E →L[ℝ] E)) => χ p.2.2 :=
      hχ.comp (contDiff_snd.comp contDiff_snd)
    exact h1.prodMk (h2.clm_comp h3)
  bound j s z := by
    set f1 : E × (E →L[ℝ] E) → E := V s ∘ ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)
    set a : E × (E →L[ℝ] E) → (E →L[ℝ] E) :=
      fderiv ℝ (V s) ∘ ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)
    set b : E × (E →L[ℝ] E) → (E →L[ℝ] E) := χ ∘ ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)
    set f2 : E × (E →L[ℝ] E) → (E →L[ℝ] E) :=
      fun z => ContinuousLinearMap.compL ℝ E E E (a z) (b z)
    have hVs := hV.contDiff_slice s
    have hf1 : ContDiff ℝ ∞ f1 := hVs.comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).contDiff
    have ha : ContDiff ℝ ∞ a :=
      (hVs.fderiv_right (m := ∞) le_rfl).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).contDiff
    have hb : ContDiff ℝ ∞ b := hχ.comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).contDiff
    have hf2 : ContDiff ℝ ∞ f2 := by
      have : f2 = fun z => (a z).comp (b z) := by funext z; simp [f2]
      rw [this]; exact ha.clm_comp hb
    have hsplit : augField V χ s = (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E) ∘ f1) +
          (ContinuousLinearMap.inr ℝ E (E →L[ℝ] E) ∘ f2) := by
      funext z; simp [augField, f1, f2, a, b]
    have hj : (j : WithTop ℕ∞) ≤ ∞ := natCast_le_inf j
    rw [hsplit, iteratedFDeriv_add_apply ((ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)).contDiff.comp hf1
      |>.of_le hj).contDiffAt ((ContinuousLinearMap.inr ℝ E (E →L[ℝ] E)).contDiff.comp hf2
      |>.of_le hj).contDiffAt]
    rw [augBound]
    have h1 : ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)) ∘ f1) z‖ ≤ B j := by
        refine ((ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)).norm_iteratedFDeriv_comp_left
          hf1.contDiffAt hj).trans ?_
        refine (mul_le_of_le_one_left (norm_nonneg (iteratedFDeriv ℝ j f1 z))
          (ContinuousLinearMap.norm_inl_le_one ℝ E (E →L[ℝ] E))).trans ?_
        exact (norm_iteratedFDeriv_comp_clm_le hVs (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (ContinuousLinearMap.norm_fst_le ℝ E (E →L[ℝ] E)) z j).trans
          (hV.bound j s _)
    have h2 : ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.inr ℝ E (E →L[ℝ] E)) ∘ f2) z‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B (i + 1) * Bχ (j - i) := by
        refine ((ContinuousLinearMap.inr ℝ E (E →L[ℝ] E)).norm_iteratedFDeriv_comp_left
          hf2.contDiffAt hj).trans ?_
        refine (mul_le_of_le_one_left (norm_nonneg (iteratedFDeriv ℝ j f2 z))
          (ContinuousLinearMap.norm_inr_le_one ℝ E (E →L[ℝ] E))).trans ?_
        refine ((ContinuousLinearMap.compL ℝ E E E).norm_iteratedFDeriv_le_of_bilinear_of_le_one ha hb z hj
          (ContinuousLinearMap.norm_compL_le _ _ _ _)).trans ?_
        refine Finset.sum_le_sum fun i hi => ?_
        have hia : ‖iteratedFDeriv ℝ i a z‖ ≤ B (i + 1) := by
          refine (norm_iteratedFDeriv_comp_clm_le (hVs.fderiv_right (m := ∞) le_rfl)
            (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
            (ContinuousLinearMap.norm_fst_le ℝ E (E →L[ℝ] E)) z i).trans ?_
          rw [norm_iteratedFDeriv_fderiv]; exact hV.bound _ s _
        have hib : ‖iteratedFDeriv ℝ (j - i) b z‖ ≤ Bχ (j - i) :=
          (norm_iteratedFDeriv_comp_clm_le hχ (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
            (ContinuousLinearMap.norm_snd_le ℝ E (E →L[ℝ] E)) z _).trans
            (hBχ _ _)
        gcongr
        exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg (iteratedFDeriv ℝ i a z)).trans hia)
    exact (norm_add_le
      (iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)) ∘ f1) z)
      (iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.inr ℝ E (E →L[ℝ] E)) ∘ f2) z)).trans
      (add_le_add h1 h2)

end AnomDiss
