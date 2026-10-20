module

public import RequestProject.ScalarHeatFractionalSmoothing

/-! # Elementary bounded Hölder and product estimates used by scalar regularity bootstrap -/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

noncomputable section

namespace AnomDiss

lemma bounded_holder_lower {E : Type*} [NormedAddCommGroup E] {f : Pt 2 → E}
    {C H β α : ℝ} (hH : 0 ≤ H) (hbound : ∀ x, ‖f x‖ ≤ C)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * ‖x - y‖ ^ β)
    (hβ : 0 < β) (hα₀ : 0 ≤ α) (hαβ : α ≤ β) (x y : Pt 2) :
    ‖f x - f y‖ ≤ ((2 * C) ^ (1 - α / β) * H ^ (α / β)) * ‖x - y‖ ^ α := by
  have hA : ‖f x - f y‖ ≤ 2 * C :=
    (norm_sub_le _ _).trans ((add_le_add (hbound x) (hbound y)).trans_eq (by ring))
  have hη₀ : 0 ≤ α / β := div_nonneg hα₀ hβ.le
  have hη₁ : α / β ≤ 1 := (div_le_one hβ).2 hαβ
  apply (le_rpow_interpolation (norm_nonneg _) hA (hholder x y) hη₀ hη₁).trans_eq
  rw [Real.mul_rpow hH (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul (norm_nonneg _)]
  have he : β * (α / β) = α := by field_simp
  rw [he]
  ring

lemma bounded_holder_product {f g : Pt 2 → ℂ} {Cf Cg Hf Hg α : ℝ}
    (hCf : ∀ x, ‖f x‖ ≤ Cf) (hCg : ∀ x, ‖g x‖ ≤ Cg)
    (hHf : ∀ x y, ‖f x - f y‖ ≤ Hf * ‖x - y‖ ^ α)
    (hHg : ∀ x y, ‖g x - g y‖ ≤ Hg * ‖x - y‖ ^ α) (x y : Pt 2) :
    ‖f x * g x - f y * g y‖ ≤ (Cf * Hg + Cg * Hf) * ‖x - y‖ ^ α := by
  have hCf₀ : 0 ≤ Cf := (norm_nonneg _).trans (hCf x)
  calc
    ‖f x * g x - f y * g y‖ = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by congr 1; ring
    _ ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
    _ ≤ Cf * (Hg * ‖x - y‖ ^ α) + (Hf * ‖x - y‖ ^ α) * Cg := by
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul (hCf x) (hHg x y) (norm_nonneg _) hCf₀)
        (mul_le_mul (hHf x y) (hCg y) (norm_nonneg _)
          ((norm_nonneg _).trans (hHf x y)))
    _ = _ := by ring

lemma partial_holder_of_fderiv_holder {f : Pt 2 → ℂ} {H α : ℝ}
    (hH : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ H * ‖x - y‖ ^ α)
    (i : Fin 2) (x y : Pt 2) : ‖pd i f x - pd i f y‖ ≤ H * ‖x - y‖ ^ α := by
  unfold pd
  change ‖(fderiv ℝ f x - fderiv ℝ f y) (Pi.single i 1)‖ ≤ _
  apply ((fderiv ℝ f x - fderiv ℝ f y).le_opNorm _).trans
  simpa only [Pi.norm_single, norm_one, mul_one] using hH x y

end AnomDiss
