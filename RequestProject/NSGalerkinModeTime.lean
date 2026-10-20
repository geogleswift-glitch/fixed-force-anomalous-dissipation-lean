module

public import RequestProject.NSGalerkinExistence
public import RequestProject.NSGalerkinModeEstimates
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Time equicontinuity of fixed Galerkin test coefficients

The constant depends on the fixed spatial test and uniform velocity `L²` and
`H¹` bounds, together with the original force `L²` bound. It does not depend on
the dimension of the finite Galerkin space.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss.FiniteSolenoidalSpace

variable (G : FiniteSolenoidalSpace)

set_option maxHeartbeats 800000

/-- The derivative of the actual finite-state test coefficient. -/
theorem hasDerivAt_test_coefficient {u : ℝ → G.State} {u' : G.State} {t : ℝ}
    (hu : HasDerivAt u u' t) (w : G.State) :
    HasDerivAt (fun s => cellVectorPair (G.eval w) (G.eval (u s)))
      (cellVectorPair (G.eval w) (G.eval u')) t := by
  simpa only [Function.comp_def, innerSL_apply_apply, G.inner_eq_cellPair] using
    ((innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t hu)

/-- A bound on the actual temporal coefficient derivative in the tested
Galerkin equation. No norm of a force derivative is needed. -/
theorem test_coefficient_derivative_bound {ν A D E H F : ℝ}
    (hν : 0 ≤ ν) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (w u u' : G.State) (g : Pt 2 → Pt 2) (hg : Continuous g)
    (hwb : ∀ x i, |G.eval w x i| ≤ A)
    (hwdb : ∀ x i j, |pd j (G.eval w) x i| ≤ D)
    (hE : l2sqV (G.eval u) ≤ E)
    (hH : (∫ x in cell 2, gradSqV (G.eval u) x) ≤ H)
    (hF : l2sqV g ≤ F)
    (hweak : cellVectorPair (G.eval w) (G.eval u') +
        cellVectorPair (G.eval w) (conv (G.eval u) (G.eval u)) =
      ν * cellVectorPair (G.eval w) (lap (G.eval u)) + cellVectorPair (G.eval w) g) :
    |cellVectorPair (G.eval w) (G.eval u')| ≤
      ν * (D * (H + 4)) + A * (F + 2) + A * (2 * E + H) := by
  have hφ : ContDiff ℝ 1 (G.eval w) := (G.eval_contDiff w).of_le (natCast_le_infty 1)
  have hv : ContDiff ℝ 2 (G.eval u) := (G.eval_contDiff u).of_le (natCast_le_infty 2)
  have hL := ns_laplacian_test_integral hD (G.eval w) (G.eval u) hφ hv
    (G.eval_periodic w) (G.eval_periodic u) hwdb
  have hB := ns_convective_test_integral hA (G.eval w) (G.eval u) hφ.continuous
    (hv.of_le (by norm_num)) hwb
  have hForce := ns_force_test_integral hA (G.eval w) g hφ.continuous hg hwb
  have hEq : cellVectorPair (G.eval w) (G.eval u') =
      ν * cellVectorPair (G.eval w) (lap (G.eval u)) + cellVectorPair (G.eval w) g -
        cellVectorPair (G.eval w) (conv (G.eval u) (G.eval u)) := by linarith
  rw [hEq]
  calc
    |ν * cellVectorPair (G.eval w) (lap (G.eval u)) + cellVectorPair (G.eval w) g -
        cellVectorPair (G.eval w) (conv (G.eval u) (G.eval u))| ≤
      |ν * cellVectorPair (G.eval w) (lap (G.eval u))| + |cellVectorPair (G.eval w) g| +
        |cellVectorPair (G.eval w) (conv (G.eval u) (G.eval u))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ν * (D * (H + 4)) + A * (F + 2) + A * (2 * E + H) := by
      rw [abs_mul, abs_of_nonneg hν]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (hL.trans (mul_le_mul_of_nonneg_left (add_le_add hH le_rfl) hD)) hν
        · exact hForce.trans (mul_le_mul_of_nonneg_left (add_le_add hF le_rfl) hA)
      · exact hB.trans (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num)) hH) hA)

/-- Fixed Galerkin test coefficients have a dimension-independent Lipschitz
time modulus under uniform velocity energy and enstrophy bounds. -/
theorem test_coefficient_lipschitz {ν T A D E H F : ℝ}
    (hν : 0 ≤ ν) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (u u' : ℝ → G.State) (g : ℝ → Pt 2 → Pt 2) (w : G.State)
    (hg : ∀ t ∈ Icc 0 T, Continuous (g t))
    (hwb : ∀ x i, |G.eval w x i| ≤ A)
    (hwdb : ∀ x i j, |pd j (G.eval w) x i| ≤ D)
    (hud : ∀ t ∈ Icc 0 T, HasDerivAt u (u' t) t)
    (hE : ∀ t ∈ Icc 0 T, l2sqV (G.eval (u t)) ≤ E)
    (hH : ∀ t ∈ Icc 0 T, (∫ x in cell 2, gradSqV (G.eval (u t)) x) ≤ H)
    (hF : ∀ t ∈ Icc 0 T, l2sqV (g t) ≤ F)
    (hweak : ∀ t ∈ Icc 0 T,
      cellVectorPair (G.eval w) (G.eval (u' t)) +
          cellVectorPair (G.eval w) (conv (G.eval (u t)) (G.eval (u t))) =
        ν * cellVectorPair (G.eval w) (lap (G.eval (u t))) + cellVectorPair (G.eval w) (g t)) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      |cellVectorPair (G.eval w) (G.eval (u t)) - cellVectorPair (G.eval w) (G.eval (u s))| ≤
        (ν * (D * (H + 4)) + A * (F + 2) + A * (2 * E + H)) * |t - s| := by
  intro s hs t ht
  have hder : ∀ r ∈ Icc 0 T,
      HasDerivWithinAt (fun r => cellVectorPair (G.eval w) (G.eval (u r)))
        (cellVectorPair (G.eval w) (G.eval (u' r))) (Icc 0 T) r :=
    fun r hr => (G.hasDerivAt_test_coefficient (hud r hr) w).hasDerivWithinAt
  have hb : ∀ r ∈ Icc 0 T,
      ‖cellVectorPair (G.eval w) (G.eval (u' r))‖ ≤
        ν * (D * (H + 4)) + A * (F + 2) + A * (2 * E + H) := by
    intro r hr
    rw [Real.norm_eq_abs]
    exact G.test_coefficient_derivative_bound hν hA hD w (u r) (u' r) (g r)
      (hg r hr) hwb hwdb (hE r hr) (hH r hr) (hF r hr) (hweak r hr)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Icc 0 T) hs ht

end AnomDiss.FiniteSolenoidalSpace
