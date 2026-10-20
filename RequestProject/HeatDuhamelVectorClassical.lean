module

public import RequestProject.HeatDuhamelParabolic
public import RequestProject.ParabolicComponentAssembly
public import RequestProject.ScalarGlobalTimeEquation

/-!
# The genuine vector heat representation gives the original classical bundle

The actual component heat integral provides every field of the unchanged
parabolic class and the pointwise vector equation on the closed interval.
The statement assumes only analytic source bounds and the actual integral
representation, never the desired differentiability or PDE conclusion.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff
noncomputable section
namespace AnomDiss

set_option maxHeartbeats 1000000

theorem vector_heatDuhamel_parabolic_and_equation {ν β : ℝ}
    (hν : 0 < ν) (hβ0 : 0 < β) (hβ1 : β < 1)
    (v F : ℝ → Pt 2 → Pt 2)
    (hF : ∀ i : Fin 2, Continuous (Function.uncurry fun s x => (F s x i : ℂ)))
    (hp : ∀ i : Fin 2, ∀ s, IsPeriodic (fun x => (F s x i : ℂ)))
    (hdata : ∀ i : Fin 2, ∃ C H : ℝ, 0 ≤ H ∧
      (∀ s x, ‖(F s x i : ℂ)‖ ≤ C) ∧
      (∀ s x y, ‖(F s x i : ℂ)-(F s y i : ℂ)‖ ≤ H*‖x-y‖^β))
    (hpar : ∀ i : Fin 2, ParHolder 1 β (fun s x => (F s x i : ℂ)))
    (hrep : ∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) 1,
      (fun x => (v t x i : ℂ)) = heatDuhamel ν (fun s x => (F s x i : ℂ)) t) :
    IsParabolicC12 1 β v ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      dt 1 v t x = ν • lap (v t) x + F t x := by
  have hreg (i : Fin 2) : IsParabolicC12 1 β (fun t x => (v t x i : ℂ)) := by
    obtain ⟨C,H,hH,hC,hholder⟩ := hdata i
    exact (heatDuhamel_isParabolicC12 hν (by norm_num) (hF i) (hp i)
      hC hH hβ0 hβ1 hholder (hpar i)).congr (hrep i)
  have hv := isParabolicC12_vector_of_complex_components (by norm_num : (0 : ℝ) < 1) hreg
  refine ⟨hv, ?_⟩
  intro t ht x
  funext i
  obtain ⟨C,H,hH,hC,hholder⟩ := hdata i
  let Q : ℝ → Pt 2 → ℂ := fun s y => (v s y i : ℂ)
  have hd : dt 1 Q t x = ((dt 1 v t x i : ℝ) : ℂ) := by
    let L : Pt 2 →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
    exact dt_clm (by norm_num) L v x ht (hv.diff_t x t ht)
  have hC2 : ContDiff ℝ 2 (fun y => v t y i) := (contDiff_pi.mp (hv.smooth_x t ht)) i
  have hlap : lap (Q t) x = ((lap (v t) x i : ℝ) : ℂ) := by
    rw [lap_complex_ofReal_C2 _ hC2, lap_component _ (hv.smooth_x t ht)]
  have he : dt 1 Q t x = ν • lap (Q t) x + (F t x i : ℂ) := by
    calc
      _ = dt 1 (heatDuhamel ν (fun s y => (F s y i : ℂ))) t x := dt_congr (hrep i) ht x
      _ = ν • lap (heatDuhamel ν (fun s y => (F s y i : ℂ)) t) x + (F t x i : ℂ) :=
        dt_heatDuhamel_Icc hν (hF i) (hp i) hC hH hβ0 hholder (by norm_num) ht x
      _ = _ := by rw [← hrep i t ht]
  rw [hd, hlap] at he
  have hre := congrArg Complex.re he
  simpa only [map_add, Complex.real_smul, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] using hre

end AnomDiss
