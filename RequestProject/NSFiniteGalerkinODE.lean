module

public import RequestProject.NSFiniteGalerkinCore
public import RequestProject.NSGalerkinTests

/-!
# The actual projected Navier--Stokes ODE

The finite-state vector field is the Riesz representative of the genuine
spatial weak form. Its linear viscous and bilinear transport operators are
constructed from the derivatives of the actual fields. The dissipative ODE
theorem therefore constructs solutions of a real finite Galerkin system.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

lemma cellVectorPair_sub_left (u v w : Pt 2 → Pt 2)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    cellVectorPair (u - v) w = cellVectorPair u w - cellVectorPair v w := by
  unfold cellVectorPair
  have heq : (fun x => dot ((u - v) x) (w x)) =
      fun x => dot (u x) (w x) - dot (v x) (w x) := by
    funext x
    simp [dot, sub_mul, Finset.sum_sub_distrib]
  rw [heq, integral_sub
    (integrableOn_cell_of_continuous (continuous_dot_fields hu hw))
    (integrableOn_cell_of_continuous (continuous_dot_fields hv hw))]

lemma cellVectorPair_sub_right (u v w : Pt 2 → Pt 2)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    cellVectorPair u (v - w) = cellVectorPair u v - cellVectorPair u w := by
  rw [cellVectorPair_comm, cellVectorPair_sub_left _ _ _ hv hw hu,
    cellVectorPair_comm v u, cellVectorPair_comm w u]

lemma cellVectorPair_self_nonneg (v : Pt 2 → Pt 2) : 0 ≤ cellVectorPair v v := by
  rw [cellVectorPair_self]
  exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _

lemma galerkin_continuous_lap {v : Pt 2 → Pt 2} (hv : ContDiff ℝ 2 v) :
    Continuous (lap v) := by
  exact continuous_finset_sum _ fun i _ =>
    continuous_pd_of_C1 _ (contDiff_pd_of_C2 _ hv i) i

lemma galerkin_continuous_conv {v w : Pt 2 → Pt 2} (hv : Continuous v)
    (hw : ContDiff ℝ 1 w) : Continuous (conv v w) := by
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hv).smul (continuous_pd_of_C1 _ hw i)

lemma galerkin_lap_add (v w : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 2 w) :
    lap (v + w) = lap v + lap w := by
  have hdv := hv.differentiable (by norm_num)
  have hdw := hw.differentiable (by norm_num)
  have hpd : ∀ i, pd i (v + w) = pd i v + pd i w := fun i =>
    pd_add_fun v w i hdv hdw
  funext x
  simp only [lap, hpd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact pd_add' _ _ x (differentiable_pd hv i x) (differentiable_pd hw i x) i

lemma galerkin_lap_smul (c : ℝ) (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v) :
    lap (c • v) = c • lap v := by
  have hd := hv.differentiable (by norm_num)
  have hpd : ∀ i, pd i (c • v) = c • pd i v := fun i => funext fun x =>
    pd_const_smul_fun v c i x (hd x)
  funext x
  simp only [lap, hpd, Pi.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact pd_const_smul_fun _ c i x (differentiable_pd hv i x)

lemma galerkin_conv_add_left (u v w : Pt 2 → Pt 2) :
    conv (u + v) w = conv u w + conv v w := by
  funext x
  simp only [conv_eq_fderiv, Pi.add_apply, map_add]

lemma galerkin_conv_smul_left (c : ℝ) (v w : Pt 2 → Pt 2) :
    conv (c • v) w = c • conv v w := by
  funext x
  simp only [conv_eq_fderiv, Pi.smul_apply, map_smul]

lemma galerkin_conv_add_right (u v w : Pt 2 → Pt 2)
    (hv : Differentiable ℝ v) (hw : Differentiable ℝ w) :
    conv u (v + w) = conv u v + conv u w := by
  funext x
  simp only [conv_eq_fderiv, Pi.add_apply]
  rw [fderiv_add (hv x) (hw x)]
  rfl

lemma galerkin_conv_smul_right (c : ℝ) (v w : Pt 2 → Pt 2)
    (hw : Differentiable ℝ w) : conv v (c • w) = c • conv v w := by
  funext x
  simp only [conv_eq_fderiv, Pi.smul_apply]
  rw [fderiv_const_smul (hw x)]
  rfl

namespace FiniteSolenoidalSpace

variable (G : FiniteSolenoidalSpace)

/-- Pairing an actual continuous field with finite test fields. -/
def fieldPairDual : C(Pt 2, Pt 2) →ₗ[ℝ] (G.State →L[ℝ] ℝ) where
  toFun f := LinearMap.toContinuousLinearMap
    { toFun := fun w => cellVectorPair f (G.eval w)
      map_add' := fun u v => cellVectorPair_add_right _ _ _ f.continuous
        (G.eval_contDiff u).continuous (G.eval_contDiff v).continuous
      map_smul' := fun c w => cellVectorPair_smul_right c _ _ }
  map_add' f g := by
    ext w
    exact cellVectorPair_add_left _ _ _ f.continuous g.continuous
      (G.eval_contDiff w).continuous
  map_smul' c f := by
    ext w
    exact cellVectorPair_smul_left c _ _

/-- The `L²` orthogonal projection of an actual continuous field into the
finite space, constructed by the finite-dimensional Riesz theorem. -/
def projection : C(Pt 2, Pt 2) →ₗ[ℝ] G.State :=
  (InnerProductSpace.toDual ℝ G.State).symm.toLinearEquiv.toLinearMap.comp G.fieldPairDual

theorem inner_projection_test (f : C(Pt 2, Pt 2)) (w : G.State) :
    ⟪G.projection f, w⟫_ℝ = cellVectorPair f (G.eval w) := by
  exact InnerProductSpace.toDual_symm_apply

theorem projection_eval (v : G.State) :
    G.projection ⟨G.eval v, (G.eval_contDiff v).continuous⟩ = v := by
  apply ext_inner_right ℝ
  intro w
  rw [G.inner_projection_test, G.inner_eq_cellPair]
  rfl

theorem projection_residual_orthogonal (f : C(Pt 2, Pt 2)) (w : G.State) :
    cellVectorPair ((f : Pt 2 → Pt 2) - G.eval (G.projection f)) (G.eval w) = 0 := by
  rw [cellVectorPair_sub_left _ _ _ f.continuous
    (G.eval_contDiff _).continuous (G.eval_contDiff w).continuous,
    ← G.inner_eq_cellPair, G.inner_projection_test, sub_self]

/-- The finite projection has the exact Pythagorean identity in the true
torus norm; this is independent of the number or redundancy of modes. -/
theorem projection_pythagoras (f : C(Pt 2, Pt 2)) :
    l2sqV ((f : Pt 2 → Pt 2) - G.eval (G.projection f)) + ‖G.projection f‖ ^ 2 =
      l2sqV f := by
  have hc := (G.eval_contDiff (G.projection f)).continuous
  have hp : cellVectorPair f (G.eval (G.projection f)) = ‖G.projection f‖ ^ 2 := by
    rw [← G.inner_projection_test, real_inner_self_eq_norm_sq]
  have he : cellVectorPair (G.eval (G.projection f)) (G.eval (G.projection f)) =
      ‖G.projection f‖ ^ 2 := by
    rw [← G.inner_eq_cellPair, real_inner_self_eq_norm_sq]
  rw [← cellVectorPair_self,
    cellVectorPair_sub_left (f : Pt 2 → Pt 2) (G.eval (G.projection f))
      ((f : Pt 2 → Pt 2) - G.eval (G.projection f)) f.continuous hc (f.continuous.sub hc),
    cellVectorPair_sub_right (f : Pt 2 → Pt 2) (f : Pt 2 → Pt 2)
      (G.eval (G.projection f)) f.continuous f.continuous hc,
    cellVectorPair_sub_right (G.eval (G.projection f)) (f : Pt 2 → Pt 2)
      (G.eval (G.projection f)) hc f.continuous hc,
    cellVectorPair_self, hp, cellVectorPair_comm (G.eval (G.projection f)) f, hp, he]
  ring

theorem norm_projection_sq_le (f : C(Pt 2, Pt 2)) :
    ‖G.projection f‖ ^ 2 ≤ l2sqV f := by
  have h := G.projection_pythagoras f
  have hn := cellVectorPair_self_nonneg ((f : Pt 2 → Pt 2) - G.eval (G.projection f))
  rw [cellVectorPair_self] at hn
  linarith

def lapField : G.State →ₗ[ℝ] C(Pt 2, Pt 2) where
  toFun v := ⟨lap (G.eval v), galerkin_continuous_lap
    ((G.eval_contDiff v).of_le (natCast_le_infty 2))⟩
  map_add' v w := by
    apply ContinuousMap.ext
    intro x
    change lap (G.eval (v + w)) x = lap (G.eval v) x + lap (G.eval w) x
    rw [map_add, galerkin_lap_add _ _ ((G.eval_contDiff v).of_le (natCast_le_infty 2))
      ((G.eval_contDiff w).of_le (natCast_le_infty 2))]
    rfl
  map_smul' c v := by
    apply ContinuousMap.ext
    intro x
    change lap (G.eval (c • v)) x = c • lap (G.eval v) x
    rw [map_smul, galerkin_lap_smul _ _ ((G.eval_contDiff v).of_le (natCast_le_infty 2))]
    rfl

def convField : G.State →ₗ[ℝ] G.State →ₗ[ℝ] C(Pt 2, Pt 2) where
  toFun v :=
    { toFun := fun w => ⟨conv (G.eval v) (G.eval w),
        galerkin_continuous_conv (G.eval_contDiff v).continuous
          ((G.eval_contDiff w).of_le (by simp))⟩
      map_add' := fun u w => by
        apply ContinuousMap.ext
        intro x
        change conv (G.eval v) (G.eval (u + w)) x = _
        rw [map_add, galerkin_conv_add_right _ _ _
          ((G.eval_contDiff u).differentiable (by simp))
          ((G.eval_contDiff w).differentiable (by simp))]
        rfl
      map_smul' := fun c w => by
        apply ContinuousMap.ext
        intro x
        change conv (G.eval v) (G.eval (c • w)) x = _
        rw [map_smul, galerkin_conv_smul_right _ _ _
          ((G.eval_contDiff w).differentiable (by simp))]
        rfl }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply ContinuousMap.ext
    intro x
    change conv (G.eval (u + v)) (G.eval w) x = _
    rw [map_add, galerkin_conv_add_left]
    rfl
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    apply ContinuousMap.ext
    intro x
    change conv (G.eval (c • v)) (G.eval w) x = _
    rw [map_smul, galerkin_conv_smul_left]
    rfl

def viscosity : G.State →L[ℝ] G.State :=
  LinearMap.toContinuousLinearMap (G.projection.comp G.lapField)

def transport : G.State →L[ℝ] G.State →L[ℝ] G.State :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (G.State →ₗ[ℝ] G.State) ≃ₗ[ℝ] (G.State →L[ℝ] G.State)).toLinearMap.comp
      (G.convField.compr₂ G.projection))

theorem inner_viscosity_test (v w : G.State) :
    ⟪G.viscosity v, w⟫_ℝ = cellVectorPair (lap (G.eval v)) (G.eval w) :=
  G.inner_projection_test (G.lapField v) w

theorem inner_transport_test (u v w : G.State) :
    ⟪G.transport u v, w⟫_ℝ = cellVectorPair (conv (G.eval u) (G.eval v)) (G.eval w) :=
  G.inner_projection_test (G.convField u v) w

/-- The true finite Galerkin vector field. -/
def nsField (ν : ℝ) (v : G.State) : G.State :=
  ν • G.viscosity v - G.transport v v

theorem contDiff_nsField (ν : ℝ) : ContDiff ℝ ∞ (G.nsField ν) := by
  change ContDiff ℝ ∞ (fun v => ν • G.viscosity v - G.transport v v)
  exact (G.viscosity.contDiff.const_smul ν).sub
    (G.transport.contDiff.clm_apply contDiff_id)

theorem inner_nsField_test (ν : ℝ) (v w : G.State) :
    ⟪G.nsField ν v, w⟫_ℝ =
      ν * cellVectorPair (lap (G.eval v)) (G.eval w) -
        cellVectorPair (conv (G.eval v) (G.eval v)) (G.eval w) := by
  simp only [nsField, inner_sub_left, real_inner_smul_left,
    G.inner_viscosity_test, G.inner_transport_test]

theorem nsField_energy (ν : ℝ) (v : G.State) :
    ⟪v, G.nsField ν v⟫_ℝ = -(ν * ∫ x in cell 2, gradSqV (G.eval v) x) := by
  rw [real_inner_comm, G.inner_nsField_test,
    cellVectorPair_comm (lap (G.eval v)) (G.eval v),
    cellVectorPair_comm (conv (G.eval v) (G.eval v)) (G.eval v)]
  unfold cellVectorPair
  rw [ns_velocity_laplacian_pairing (G.eval v)
    ((G.eval_contDiff v).of_le (natCast_le_infty 2)) (G.eval_periodic v),
    ns_velocity_convection_cancellation (G.eval v)
    ((G.eval_contDiff v).of_le (natCast_le_infty 1)) (G.eval_periodic v) (G.eval_solenoidal v)]
  ring

theorem nsField_dissipative {ν : ℝ} (hν : 0 ≤ ν) (v : G.State) :
    ⟪v, G.nsField ν v⟫_ℝ ≤ 0 := by
  rw [G.nsField_energy]
  exact neg_nonpos.mpr (mul_nonneg hν (integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _))

/-- Time continuity of the actual force gives continuity of its finite
projection, without any norm assumption on spatial derivatives of the force. -/
theorem continuousOn_projected_force (f : ℝ → C(Pt 2, Pt 2)) {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn (fun q : ℝ × Pt 2 => f q.1 q.2) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun t => G.projection (f t)) (Icc 0 T) := by
  have hd : ContinuousOn (fun t => G.fieldPairDual (f t)) (Icc 0 T) := by
    apply continuousOn_clm_apply.mpr
    intro w
    change ContinuousOn (fun t => ∫ x in cell 2, dot (f t x) (G.eval w x)) (Icc 0 T)
    refine continuousOn_integral_cell' hT _ ?_
    exact continuousOn_finset_sum _ fun i _ =>
      ((continuous_apply i).comp_continuousOn hf).mul
        ((((continuous_apply i).comp (G.eval_contDiff w).continuous).comp continuous_snd).continuousOn)
  exact (InnerProductSpace.toDual ℝ G.State).symm.continuous.comp_continuousOn hd

theorem projected_ns_weak_form (ν : ℝ) (v w : G.State) (f : C(Pt 2, Pt 2)) :
    cellVectorPair (G.eval w) (G.eval (G.nsField ν v + G.projection f)) +
        cellVectorPair (G.eval w) (conv (G.eval v) (G.eval v)) =
      ν * cellVectorPair (G.eval w) (lap (G.eval v)) + cellVectorPair (G.eval w) f := by
  rw [← G.inner_eq_cellPair, inner_add_right, real_inner_comm (G.nsField ν v) w,
    G.inner_nsField_test, real_inner_comm (G.projection f) w, G.inner_projection_test,
    cellVectorPair_comm (lap (G.eval v)) (G.eval w),
    cellVectorPair_comm (conv (G.eval v) (G.eval v)) (G.eval w),
    cellVectorPair_comm f (G.eval w)]
  ring

/-- Actual global solutions of every finite Galerkin system. All assumptions
are properties of the prescribed viscosity, time interval and force. -/
theorem exists_ns_galerkin_state {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (f : ℝ → C(Pt 2, Pt 2))
    (hf : ContinuousOn (fun q : ℝ × Pt 2 => f q.1 q.2) (Icc 0 T ×ˢ univ))
    (v₀ : G.State) :
    ∃ u : ℝ → G.State, u 0 = v₀ ∧
      (∀ t ∈ Icc 0 T, HasDerivAt u (G.nsField ν (u t) + G.projection (f t)) t) ∧
      ∀ t ∈ Icc 0 T, ∀ w : G.State,
        cellVectorPair (G.eval w) (G.eval (G.nsField ν (u t) + G.projection (f t))) +
            cellVectorPair (G.eval w) (conv (G.eval (u t)) (G.eval (u t))) =
          ν * cellVectorPair (G.eval w) (lap (G.eval (u t))) +
            cellVectorPair (G.eval w) (f t) := by
  obtain ⟨u, hu0, hud⟩ := exists_dissipative_forced_ode_of_continuous (G.nsField ν)
    ((G.contDiff_nsField ν).of_le (natCast_le_infty 1)) (G.nsField_dissipative hν)
    (fun t => G.projection (f t)) T hT (G.continuousOn_projected_force f hT hf) v₀
  exact ⟨u, hu0, hud, fun t ht w => G.projected_ns_weak_form ν (u t) w (f t)⟩

end FiniteSolenoidalSpace
end AnomDiss
