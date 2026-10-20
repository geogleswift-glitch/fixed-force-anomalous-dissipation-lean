module

public import RequestProject.TorusCalc
public import RequestProject.TorusFourier
public import RequestProject.Shears

/-!
# Quasi-periodic functions on `ℝ²`

A function `f : ℝ² → ℂ` is quasi-periodic with character `ξ` if `f(x + n) = e_ξ(n) f(x)` for all
integer vectors `n`.  Periodic functions are the case `ξ = 0`.  Products `f̄ g` of two such
functions with the same character are periodic, which is what makes energy estimates on the unit
cell work.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal InnerProductSpace

noncomputable section

namespace AnomDiss

/-- `f` is quasi-periodic with character `ξ`. -/
def IsQP (ξ : Pt 2) (f : Pt 2 → ℂ) : Prop :=
  ∀ x (m : Fin 2 → ℤ), f (x + intVec m) = expChar ξ (intVec m) * f x

variable {ξ : Pt 2} {f g : Pt 2 → ℂ}

lemma isQP_zero_iff : IsQP 0 f ↔ IsPeriodic f := by
  have h : ∀ v : Pt 2, expChar 0 v = 1 := fun v => by simp [expChar, dot]
  simp only [IsQP, IsPeriodic, h, one_mul]

lemma IsQP.add (hf : IsQP ξ f) (hg : IsQP ξ g) : IsQP ξ (f + g) := fun x m => by
  simp only [Pi.add_apply, hf x m, hg x m]; ring

lemma IsQP.sub (hf : IsQP ξ f) (hg : IsQP ξ g) : IsQP ξ (f - g) := fun x m => by
  simp only [Pi.sub_apply, hf x m, hg x m]; ring

lemma IsQP.const_mul (hf : IsQP ξ f) (c : ℂ) : IsQP ξ (fun x => c * f x) := fun x m => by
  simp only [hf x m]; ring

lemma IsQP.comp_lift (hf : IsQP ξ f) {ψ : Pt 2 → Pt 2} (hψ : IsLift ψ) : IsQP ξ (f ∘ ψ) :=
  fun x m => by simp only [Function.comp_apply, hψ x m]; exact hf _ m

lemma IsQP.comp_add (hf : IsQP ξ f) (c : Pt 2) : IsQP ξ (fun x => f (x + c)) := fun x m => by
  simp only [show x + intVec m + c = x + c + intVec m by abel]; exact hf _ m

lemma IsQP.pd (hf : IsQP ξ f) (hd : Differentiable ℝ f) (i : Fin 2) :
    IsQP ξ (AnomDiss.pd i f) := fun x m => by
  unfold AnomDiss.pd
  have e : (fun y => f (y + intVec m)) = fun y => expChar ξ (intVec m) * f y :=
    funext fun y => hf y m
  have h1 := congrArg (fun F => fderiv ℝ F x) e
  rw [fderiv_comp_add_right, fderiv_const_mul (hd x)] at h1
  rw [h1]
  simp

lemma norm_mul_expChar (v : Pt 2) (z : ℂ) : ‖expChar ξ v * z‖ = ‖z‖ := by
  rw [norm_mul, norm_expChar, one_mul]

lemma IsQP.periodic_norm (hf : IsQP ξ f) : IsPeriodic fun x => ‖f x‖ := fun x m => by
  simp only [hf x m, norm_mul_expChar]

lemma IsQP.periodic_norm_sq (hf : IsQP ξ f) : IsPeriodic fun x => ‖f x‖ ^ 2 := fun x m => by
  simp only [hf x m, norm_mul_expChar]

lemma inner_expChar_mul (v : Pt 2) (z w : ℂ) :
    ⟪expChar ξ v * z, expChar ξ v * w⟫_ℝ = ⟪z, w⟫_ℝ := by
  have h : ‖expChar ξ v‖ = 1 := norm_expChar ξ v
  rw [Complex.inner, Complex.inner, map_mul]
  have hc : expChar ξ v * (starRingEnd ℂ) (expChar ξ v) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc (expChar ξ v * w * ((starRingEnd ℂ) (expChar ξ v) * (starRingEnd ℂ) z)).re
      = ((expChar ξ v * (starRingEnd ℂ) (expChar ξ v)) * (w * (starRingEnd ℂ) z)).re := by
        ring_nf
    _ = (w * (starRingEnd ℂ) z).re := by rw [hc, one_mul]

lemma IsQP.periodic_inner (hf : IsQP ξ f) (hg : IsQP ξ g) :
    IsPeriodic fun x => ⟪f x, g x⟫_ℝ := fun x m => by
  simp only [hf x m, hg x m, inner_expChar_mul]

/-- A continuous quasi-periodic function is bounded. -/
lemma IsQP.bdd (hf : IsQP ξ f) (hc : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Pt 2)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨y, hy, m, rfl⟩ := exists_cell_rep x
  have := hf.periodic_norm y m
  simp only at this
  rw [this]
  exact hC y hy

end AnomDiss
