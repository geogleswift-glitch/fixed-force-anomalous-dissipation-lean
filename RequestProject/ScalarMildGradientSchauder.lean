module

public import RequestProject.ScalarMildGradientHolderLoss
public import RequestProject.ScalarSchauderSpatial

/-!
# Exact spatial Hölder exponent for the constructed scalar gradient

The short-time/long-time Schauder split keeps the drift exponent in the
actual Duhamel derivative.  Applied to the genuine fixed point, this gives
the full spatial Hölder exponent of its gradient on the entire closed slab.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The actual full spatial derivative of the constructed mild solution
is uniformly Hölder with exactly the original drift exponent. -/
theorem scalar_mild_fixedPoint_fderiv_spatial_holder {ν T β : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    (hbper : ∀ i t, IsPeriodic (fun x => b i (t, x))) (hfper : IsPeriodic f)
    (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ))
    (hbholder : ∀ i, ∃ H, ∀ t : Icc (0 : ℝ) T, ∀ x y,
      ‖b i (t, x) - b i (t, y)‖ ≤ H * ‖x - y‖ ^ β)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u) :
    ∃ H, 0 ≤ H ∧ ∀ (t : Icc (0 : ℝ) T) x y,
      ‖fderiv ℝ (fun z => u (t, z)) x - fderiv ℝ (fun z => u (t, z)) y‖ ≤
        H * ‖x - y‖ ^ β := by
  have hf₁ : ContDiff ℝ 1 (f : Pt 2 → ℂ) := hfc.of_le (by norm_num)
  choose H hH hper hholder using scalar_mild_product_sources_holder hν hT hβ₀ hβ₁ b f
    hbper hfper hf₁ hbholder hu
  obtain ⟨C₀, hC₀, hheat⟩ := fderiv_heatOp_C2_uniform_holder hfc hfper hβ₀.le hβ₁.le
  let D : Fin 2 → ℝ := fun i =>
    4 * duhamelSpaceDerivativeScale ν (H i) β / β +
      2 * duhamelThirdDerivativeScale ν (H i) β / (1 - β)
  have hD₀ : ∀ i, 0 ≤ D i := by
    intro i
    have hA : 0 ≤ duhamelSpaceDerivativeScale ν (H i) β := by
      have hHi := hH i
      have hg := gmom_nonneg (β + 1)
      have hg1 := gmom_nonneg 1
      unfold duhamelSpaceDerivativeScale
      positivity
    have hB := duhamelThirdDerivativeScale_nonneg hν.le (hH i) (β := β)
    exact add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) hA) hβ₀.le)
      (div_nonneg (mul_nonneg (by norm_num) hB) (sub_pos.mpr hβ₁).le)
  have hD : ∀ i (t : Icc (0 : ℝ) T) x y,
      ‖fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) x -
        fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) y‖ ≤
          D i * ‖x - y‖ ^ β := by
    intro i t x y
    exact fderiv_duhamelComponent_spatial_schauder hν
      (continuous_extendSlabScalar hT (b i * u)) (hper i)
      (norm_extendSlabScalar_le hT (b i * u))
      (hH i) hβ₀ hβ₁ (hholder i) i t.property.1 x y
  refine ⟨C₀ + ∑ i : Fin 2, D i,
    add_nonneg hC₀ (Finset.sum_nonneg fun i _ => hD₀ i), fun t x y => ?_⟩
  let v := Real.toNNReal (2 * ν * (t : ℝ))
  let A : Fin 2 → (Pt 2 →L[ℝ] ℂ) := fun i =>
    fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) x -
      fderiv ℝ (duhamelComponent ν (extendSlabScalar hT (b i * u)) i t) y
  calc
    ‖fderiv ℝ (fun z => u (t, z)) x - fderiv ℝ (fun z => u (t, z)) y‖
        = ‖(fderiv ℝ (heatOp v f) x - fderiv ℝ (heatOp v f) y) - ∑ i : Fin 2, A i‖ := by
      rw [scalar_mild_fixedPoint_fderiv_eq hν hT hβ₀ hβ₁ b f hbper hfper hf₁ hbholder hu t x,
        scalar_mild_fixedPoint_fderiv_eq hν hT hβ₀ hβ₁ b f hbper hfper hf₁ hbholder hu t y]
      unfold A v
      rw [Finset.sum_sub_distrib]
      congr 1
      abel
    _ ≤ ‖fderiv ℝ (heatOp v f) x - fderiv ℝ (heatOp v f) y‖ + ‖∑ i : Fin 2, A i‖ :=
      norm_sub_le _ _
    _ ≤ C₀ * ‖x - y‖ ^ β + ∑ i : Fin 2, D i * ‖x - y‖ ^ β :=
      add_le_add (hheat v x y)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hD i t x y))
    _ = _ := by
      rw [← Finset.sum_mul]
      ring

end AnomDiss
