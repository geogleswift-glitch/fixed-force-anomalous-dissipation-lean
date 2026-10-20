module

public import RequestProject.NSPhaseGalerkinCompactness

/-!
# Time integration of uniformly convergent coefficient curves

Clamping outside the original closed unit interval defines an actual linear
integration functional on the Banach space of bounded continuous time curves.
Its norm is at most one, so sup convergence commutes with every integral from
zero to a time in the interval.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff BoundedContinuousFunction

noncomputable section

namespace AnomDiss

def extendGalerkinTimeCurve (F : GalerkinTime →ᵇ ℂ) (s : ℝ) : ℂ :=
  F (projIcc 0 1 (by norm_num) s)

theorem continuous_extendGalerkinTimeCurve (F : GalerkinTime →ᵇ ℂ) :
    Continuous (extendGalerkinTimeCurve F) :=
  F.continuous.comp continuous_projIcc

theorem extendGalerkinTimeCurve_of_mem (F : GalerkinTime →ᵇ ℂ) {s : ℝ}
    (hs : s ∈ Icc 0 1) : extendGalerkinTimeCurve F s = F ⟨s, hs⟩ := by
  simp only [extendGalerkinTimeCurve, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs]

def galerkinTimeIntegralLinear (t : GalerkinTime) : (GalerkinTime →ᵇ ℂ) →ₗ[ℝ] ℂ where
  toFun F := ∫ s in (0 : ℝ)..t.1, extendGalerkinTimeCurve F s
  map_add' F G := by
    change (∫ s in (0 : ℝ)..t.1, extendGalerkinTimeCurve F s + extendGalerkinTimeCurve G s) = _
    exact intervalIntegral.integral_add
      ((continuous_extendGalerkinTimeCurve F).intervalIntegrable 0 t.1)
      ((continuous_extendGalerkinTimeCurve G).intervalIntegrable 0 t.1)
  map_smul' c F := by
    change (∫ s in (0 : ℝ)..t.1, c • extendGalerkinTimeCurve F s) = _
    exact intervalIntegral.integral_smul c _

theorem norm_galerkinTimeIntegralLinear_le (t : GalerkinTime) (F : GalerkinTime →ᵇ ℂ) :
    ‖galerkinTimeIntegralLinear t F‖ ≤ ‖F‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t.1) (fun s _ => F.norm_coe_le_norm (projIcc 0 1 (by norm_num) s))
  rw [sub_zero, abs_of_nonneg t.2.1] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg F) t.2.2)

def galerkinTimeIntegralCLM (t : GalerkinTime) : (GalerkinTime →ᵇ ℂ) →L[ℝ] ℂ :=
  (galerkinTimeIntegralLinear t).mkContinuous 1
    (fun F => by simpa only [one_mul] using norm_galerkinTimeIntegralLinear_le t F)

theorem galerkinTimeIntegralCLM_eq_integral (t : GalerkinTime) (F : GalerkinTime →ᵇ ℂ) :
    galerkinTimeIntegralCLM t F = ∫ s in (0 : ℝ)..t.1, extendGalerkinTimeCurve F s := rfl

/-- The bounded functional agrees with a prescribed actual time function
whose values agree with the curve on the original interval. -/
theorem galerkinTimeIntegralCLM_eq_of_values (t : GalerkinTime)
    (F : GalerkinTime →ᵇ ℂ) (f : ℝ → ℂ)
    (hF : ∀ (s : ℝ) (hs : s ∈ Icc 0 1), F ⟨s, hs⟩ = f s) :
    galerkinTimeIntegralCLM t F = ∫ s in (0 : ℝ)..t.1, f s := by
  change (∫ s in (0 : ℝ)..t.1, extendGalerkinTimeCurve F s) = _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.2.1] at hs
  have hs1 : s ∈ Icc 0 1 := ⟨hs.1, hs.2.trans t.2.2⟩
  rw [extendGalerkinTimeCurve_of_mem F hs1]
  exact hF s hs1

/-- Uniform convergence of the actual time curves passes through every
integral appearing in the Fourier evolution equation. -/
theorem galerkinTimeIntegralCLM_tendsto (t : GalerkinTime)
    {F : GalerkinTime →ᵇ ℂ} {f : ℕ → (GalerkinTime →ᵇ ℂ)}
    (hf : Tendsto f atTop (𝓝 F)) :
    Tendsto (fun n => galerkinTimeIntegralCLM t (f n)) atTop (𝓝 (galerkinTimeIntegralCLM t F)) :=
  (galerkinTimeIntegralCLM t).continuous.tendsto F |>.comp hf

end AnomDiss
