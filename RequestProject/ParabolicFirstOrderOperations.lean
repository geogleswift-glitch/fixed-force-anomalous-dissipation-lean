module

public import RequestProject.ParabolicHolderOperations
public import RequestProject.TrueHorizontal
public import RequestProject.ScalarEnergy

/-! # Operations on the original first-order parabolic class -/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff
noncomputable section
namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsParabolicC01.parHolder {T β : ℝ} {v : ℝ → Pt 2 → E}
    (hv : IsParabolicC01 T β v) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : ParHolder T β v := by
  classical
  obtain ⟨B, hB⟩ := hv.bdd
  choose C hC using hv.bdd_d1
  let D : ℝ := |C 0|+|C 1|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : Pt 2) (j : Fin 2) :
      ‖pd j (v t) x‖ ≤ D := by
    have h := hC j t ht x
    fin_cases j
    · change ‖pd 0 (v t) x‖ ≤ |C 0|+|C 1|
      change ‖pd 0 (v t) x‖ ≤ C 0 at h
      linarith [le_abs_self (C 0), abs_nonneg (C 1)]
    · change ‖pd 1 (v t) x‖ ≤ |C 0|+|C 1|
      change ‖pd 1 (v t) x‖ ≤ C 1 at h
      linarith [le_abs_self (C 1), abs_nonneg (C 0)]
  apply parHolder_of_spatial_time _ hv.holder_time
  refine ⟨2*B+2*D, fun t ht x y => ?_⟩
  apply holder_of_lip_bdd (v t) (by positivity : 0 ≤ 2*D) (hB t ht) _ hβ0 hβ1
  intro x y
  exact (convex_univ : Convex ℝ (univ : Set (Pt 2))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hv.smooth_x t ht).differentiable one_ne_zero z)
    (fun z _ => by simpa only [Nat.cast_ofNat] using
      norm_fderiv_le_of_pd (v t) z hD (hpd t ht z)) (mem_univ y) (mem_univ x)

theorem continuous_of_parHolder_unit_clamped {β : ℝ} {g : ℝ → Pt 2 → E}
    (hβ : 0 < β) (hg : ParHolder 1 β g)
    (hclamp : ∀ t : ℝ, g (projIcc 0 1 (by norm_num) t) = g t) :
    Continuous (Function.uncurry g) := by
  have hc : Continuous (fun p : ℝ × Pt 2 =>
      (((projIcc 0 1 (by norm_num) p.1 : Icc (0 : ℝ) 1) : ℝ), p.2)) :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
  have h := (hg.continuousOn hβ).comp_continuous hc
    (fun p => ⟨Subtype.mem _, mem_univ _⟩)
  exact h.congr (fun p => congrFun (hclamp p.1) p.2)

end AnomDiss
