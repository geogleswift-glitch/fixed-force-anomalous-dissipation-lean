module

public import RequestProject.ExistenceInterfaces
public import RequestProject.ForcedFiniteODE
public import RequestProject.NSGalerkinEnstrophy

/-!
# The actual finite Galerkin Hilbert space

A finite-dimensional subspace of smooth periodic solenoidal vector fields is
given the genuine torus `L²` inner product.  Positive definiteness uses continuity
and periodicity, so this construction does not identify distinct Fourier
coefficient representations or assume any PDE existence assertion.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

def cellVectorPair (v w : Pt 2 → Pt 2) : ℝ :=
  ∫ x in cell 2, dot (v x) (w x)

lemma continuous_dot_fields {v w : Pt 2 → Pt 2} (hv : Continuous v)
    (hw : Continuous w) : Continuous (fun x => dot (v x) (w x)) :=
  continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hv).mul ((continuous_apply i).comp hw)

lemma cellVectorPair_comm (v w : Pt 2 → Pt 2) :
    cellVectorPair v w = cellVectorPair w v := by
  unfold cellVectorPair
  congr 1
  funext x
  simp [dot, mul_comm]

lemma cellVectorPair_add_left (u v w : Pt 2 → Pt 2)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    cellVectorPair (u + v) w = cellVectorPair u w + cellVectorPair v w := by
  unfold cellVectorPair
  have heq : (fun x => dot ((u + v) x) (w x)) =
      fun x => dot (u x) (w x) + dot (v x) (w x) := by
    funext x
    simp [dot, add_mul, Finset.sum_add_distrib]
  rw [heq, integral_add
    (integrableOn_cell_of_continuous (continuous_dot_fields hu hw))
    (integrableOn_cell_of_continuous (continuous_dot_fields hv hw))]

lemma cellVectorPair_smul_left (c : ℝ) (v w : Pt 2 → Pt 2) :
    cellVectorPair (c • v) w = c * cellVectorPair v w := by
  unfold cellVectorPair
  have heq : (fun x => dot ((c • v) x) (w x)) =
      fun x => c * dot (v x) (w x) := by
    funext x
    simp only [dot, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  rw [heq, integral_const_mul]

lemma cellVectorPair_add_right (u v w : Pt 2 → Pt 2)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    cellVectorPair u (v + w) = cellVectorPair u v + cellVectorPair u w := by
  rw [cellVectorPair_comm, cellVectorPair_add_left _ _ _ hv hw hu,
    cellVectorPair_comm v u, cellVectorPair_comm w u]

lemma cellVectorPair_smul_right (c : ℝ) (v w : Pt 2 → Pt 2) :
    cellVectorPair v (c • w) = c * cellVectorPair v w := by
  rw [cellVectorPair_comm, cellVectorPair_smul_left, cellVectorPair_comm w v]

lemma cellVectorPair_self (v : Pt 2 → Pt 2) : cellVectorPair v v = l2sqV v := by
  simp only [cellVectorPair, l2sqV, dot, pow_two]

/-- Structural properties of a concrete finite subspace of spatial fields.
The Fourier spaces constructed separately supply these data. -/
structure FiniteSolenoidalSpace where
  space : Submodule ℝ (Pt 2 → Pt 2)
  finiteDimensional : FiniteDimensional ℝ space
  regular : ∀ v ∈ space, ContDiff ℝ ∞ v
  periodic : ∀ v ∈ space, IsPeriodic v
  solenoidal : ∀ v ∈ space, ∀ x, divergence v x = 0

namespace FiniteSolenoidalSpace

variable (G : FiniteSolenoidalSpace)

/-- The state is an actual spatial vector field, not a redundant coefficient table. -/
def State : Type := G.space

instance : AddCommGroup G.State := inferInstanceAs (AddCommGroup G.space)
instance : Module ℝ G.State := inferInstanceAs (Module ℝ G.space)
instance : FiniteDimensional ℝ G.State := G.finiteDimensional

def eval : G.State →ₗ[ℝ] (Pt 2 → Pt 2) := G.space.subtype

theorem eval_contDiff (v : G.State) : ContDiff ℝ ∞ (G.eval v) := G.regular v.1 v.2
theorem eval_periodic (v : G.State) : IsPeriodic (G.eval v) := G.periodic v.1 v.2
theorem eval_solenoidal (v : G.State) (x : Pt 2) : divergence (G.eval v) x = 0 :=
  G.solenoidal v.1 v.2 x
theorem eval_injective : Function.Injective G.eval := G.space.subtype_injective

def innerCore : InnerProductSpace.Core ℝ G.State where
  inner v w := cellVectorPair (G.eval v) (G.eval w)
  conj_inner_symm v w := cellVectorPair_comm _ _
  re_inner_nonneg v := by
    change 0 ≤ cellVectorPair (G.eval v) (G.eval v)
    rw [cellVectorPair_self]
    exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  add_left u v w := cellVectorPair_add_left _ _ _
    (G.eval_contDiff u).continuous (G.eval_contDiff v).continuous (G.eval_contDiff w).continuous
  smul_left v w c := cellVectorPair_smul_left c _ _
  definite v hv := by
    apply G.eval_injective
    rw [map_zero]
    exact periodic_vector_eq_zero_of_l2sqV_eq_zero (G.eval v)
      (G.eval_contDiff v).continuous (G.eval_periodic v) (by
        simpa only [cellVectorPair_self] using hv)

instance : InnerProductSpace.Core ℝ G.State := G.innerCore
instance : NormedAddCommGroup G.State :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ G.State :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ G.State)

instance : CompleteSpace G.State := FiniteDimensional.complete ℝ G.State

theorem inner_eq_cellPair (v w : G.State) :
    ⟪v, w⟫_ℝ = cellVectorPair (G.eval v) (G.eval w) := rfl

theorem norm_sq_eq_l2sqV (v : G.State) : ‖v‖ ^ 2 = l2sqV (G.eval v) := by
  rw [← real_inner_self_eq_norm_sq, G.inner_eq_cellPair, cellVectorPair_self]

/-- Every fixed-point evaluation is continuous for the `L²` norm on the finite
space. No point evaluation is claimed continuous on the infinite `L²` space. -/
def pointEval (x : Pt 2) : G.State →L[ℝ] Pt 2 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj x : (Pt 2 → Pt 2) →ₗ[ℝ] Pt 2).comp G.eval)

@[simp] theorem pointEval_apply (x : Pt 2) (v : G.State) :
    G.pointEval x v = G.eval v x := rfl

/-- The true spatial field inherits every finite-state time derivative. -/
theorem hasDerivAt_eval {u : ℝ → G.State} {u' : G.State} {t : ℝ}
    (hu : HasDerivAt u u' t) (x : Pt 2) :
    HasDerivAt (fun s => G.eval (u s) x) (G.eval u' x) t :=
  (G.pointEval x).hasFDerivAt.comp_hasDerivAt t hu

end FiniteSolenoidalSpace
end AnomDiss
