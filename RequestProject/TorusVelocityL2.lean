module

public import RequestProject.NSFiniteGalerkinCore
public import RequestProject.SplitNegMoment
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The completed Hilbert space for the actual periodic velocity fields

The target is genuine Lebesgue `L²` on the unit cell with the Euclidean vector
norm. Smooth periodic fields embed by their actual representatives. Distances
are exactly the `l2sqV` distances used in the manuscript.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace AnomDiss

abbrev TorusVelocityL2 := Lp (EuclideanSpace ℝ (Fin 2)) 2 (volume.restrict (cell 2))

def euclideanVelocity (v : Pt 2 → Pt 2) (x : Pt 2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (v x)

theorem continuous_euclideanVelocity {v : Pt 2 → Pt 2} (hv : Continuous v) :
    Continuous (euclideanVelocity v) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp hv

theorem periodic_continuous_field_bound {F : Type*} [NormedAddCommGroup F]
    (v : Pt 2 → F) (hv : Continuous v) (hp : IsPeriodic v) :
    ∃ C : ℝ, ∀ x, ‖v x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨y, hy, n, rfl⟩ := exists_cell_rep x
  rw [hp y n]
  exact hC y hy

def periodicVelocityBCF (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) :
    Pt 2 →ᵇ EuclideanSpace ℝ (Fin 2) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (euclideanVelocity v)
    (continuous_euclideanVelocity hv)
    (Classical.choose (periodic_continuous_field_bound (euclideanVelocity v)
      (continuous_euclideanVelocity hv) (fun x n => by dsimp [euclideanVelocity]; rw [hp])))
    (Classical.choose_spec (periodic_continuous_field_bound (euclideanVelocity v)
      (continuous_euclideanVelocity hv) (fun x n => by dsimp [euclideanVelocity]; rw [hp])))

@[simp] theorem periodicVelocityBCF_apply (v : Pt 2 → Pt 2)
    (hv : Continuous v) (hp : IsPeriodic v) (x : Pt 2) :
    periodicVelocityBCF v hv hp x = euclideanVelocity v x := rfl

def periodicVelocityToL2 (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) : TorusVelocityL2 :=
  BoundedContinuousFunction.toLp 2 (volume.restrict (cell 2)) ℝ (periodicVelocityBCF v hv hp)

theorem periodicVelocityToL2_ae (v : Pt 2 → Pt 2) (hv : Continuous v) (hp : IsPeriodic v) :
    periodicVelocityToL2 v hv hp =ᵐ[volume.restrict (cell 2)] euclideanVelocity v :=
  (periodicVelocityBCF v hv hp).coeFn_toLp 2 (volume.restrict (cell 2)) ℝ

theorem inner_periodicVelocityToL2 (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hpv : IsPeriodic v) (hw : Continuous w) (hpw : IsPeriodic w) :
    ⟪periodicVelocityToL2 v hv hpv, periodicVelocityToL2 w hw hpw⟫_ℝ = cellVectorPair v w := by
  rw [L2.inner_def]
  unfold cellVectorPair dot
  apply integral_congr_ae
  filter_upwards [periodicVelocityToL2_ae v hv hpv, periodicVelocityToL2_ae w hw hpw] with x hxv hxw
  simp only [hxv, hxw, PiLp.inner_apply, RCLike.inner_apply, euclideanVelocity,
    starRingEnd_apply, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem norm_periodicVelocityToL2_sq (v : Pt 2 → Pt 2)
    (hv : Continuous v) (hp : IsPeriodic v) :
    ‖periodicVelocityToL2 v hv hp‖ ^ 2 = l2sqV v := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [periodicVelocityToL2_ae v hv hp] with x hx
  rw [hx]
  simp only [PiLp.inner_apply, RCLike.inner_apply, euclideanVelocity,
    starRingEnd_apply, star_trivial, pow_two]

theorem norm_periodicVelocityToL2_sub_sq (v w : Pt 2 → Pt 2)
    (hv : Continuous v) (hpv : IsPeriodic v) (hw : Continuous w) (hpw : IsPeriodic w) :
    ‖periodicVelocityToL2 v hv hpv - periodicVelocityToL2 w hw hpw‖ ^ 2 = l2sqV (v - w) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (periodicVelocityToL2 v hv hpv) (periodicVelocityToL2 w hw hpw),
    periodicVelocityToL2_ae v hv hpv, periodicVelocityToL2_ae w hw hpw] with x hxsub hxv hxw
  rw [hxsub]
  simp only [Pi.sub_apply, hxv, hxw, PiLp.inner_apply, RCLike.inner_apply, euclideanVelocity,
    PiLp.sub_apply, starRingEnd_apply, star_trivial, pow_two]

namespace FiniteSolenoidalSpace

variable (G : FiniteSolenoidalSpace)

def evalBCF : G.State →ₗ[ℝ] (Pt 2 →ᵇ EuclideanSpace ℝ (Fin 2)) where
  toFun v := periodicVelocityBCF (G.eval v) (G.eval_contDiff v).continuous (G.eval_periodic v)
  map_add' v w := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [periodicVelocityBCF_apply, euclideanVelocity, map_add, Pi.add_apply, WithLp.toLp_add,
      BoundedContinuousFunction.add_apply]
  map_smul' c v := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [periodicVelocityBCF_apply, euclideanVelocity, map_smul, Pi.smul_apply,
      WithLp.toLp_smul, BoundedContinuousFunction.smul_apply, RingHom.id_apply]

/-- A finite state embeds as its actual Euclidean-valued equivalence class. -/
def toL2 : G.State →ₗ[ℝ] TorusVelocityL2 :=
  (BoundedContinuousFunction.toLp 2 (volume.restrict (cell 2)) ℝ).toLinearMap.comp G.evalBCF

theorem toL2_eq_periodicVelocityToL2 (v : G.State) :
    G.toL2 v = periodicVelocityToL2 (G.eval v) (G.eval_contDiff v).continuous (G.eval_periodic v) := rfl

theorem norm_toL2_sq (v : G.State) : ‖G.toL2 v‖ ^ 2 = l2sqV (G.eval v) :=
  norm_periodicVelocityToL2_sq _ (G.eval_contDiff v).continuous (G.eval_periodic v)

def toL2Isometry : G.State →ₗᵢ[ℝ] TorusVelocityL2 where
  toLinearMap := G.toL2
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [G.norm_toL2_sq, G.norm_sq_eq_l2sqV]

end FiniteSolenoidalSpace
end AnomDiss
