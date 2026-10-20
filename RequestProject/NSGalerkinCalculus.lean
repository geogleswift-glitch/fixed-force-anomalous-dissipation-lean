module

public import RequestProject.NSGalerkinApriori
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Calculus of finite-dimensional velocity curves

Spatial evaluation and its derivatives are linear maps on the actual finite
Galerkin space. Finite dimensionality makes those maps continuous, so the time
derivative of the velocity and its vorticity follows from the coefficient ODE.
No evolution or existence assumption is made here.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

section Evaluation

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X]

/-- A finite-dimensional linear family of continuous functions is jointly
continuous in its coefficient vector and spatial point. -/
theorem ns_finite_linear_evaluation_continuous (L : E →ₗ[ℝ] (X → F))
    (hc : ∀ z, Continuous (L z)) : Continuous (fun q : E × X => L q.1 q.2) := by
  let b := Module.finBasis ℝ E
  have hex (z : E) (x : X) : L z x = ∑ i, b.repr z i • L (b i) x := by
    have h := congrArg (fun y : E => L y x) (b.sum_repr z)
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply] using h.symm
  have hf : (fun q : E × X => L q.1 q.2) =
      fun q => ∑ i, b.repr q.1 i • L (b i) q.2 := by
    funext q
    exact hex q.1 q.2
  rw [hf]
  exact continuous_finset_sum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_fst).smul
      ((hc (b i)).comp continuous_snd)

/-- Evaluation at a fixed point, as a linear map on the coefficient space. -/
def nsEvaluationLinear (L : E →ₗ[ℝ] (X → F)) (x : X) : E →ₗ[ℝ] F where
  toFun z := L z x
  map_add' z w := by simp
  map_smul' c z := by simp

omit [TopologicalSpace X] in
/-- The actual time derivative of finite-dimensional evaluation. -/
theorem ns_hasDerivAt_evaluation (L : E →ₗ[ℝ] (X → F))
    {u : ℝ → E} {z : E} {t : ℝ} (hu : HasDerivAt u z t) (x : X) :
    HasDerivAt (fun s => L (u s) x) (L z x) t := by
  exact ((nsEvaluationLinear L x).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hu)

end Evaluation

section SpatialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A spatial directional derivative evaluated at a point is a linear map on
any finite-dimensional family of differentiable velocity fields. -/
def nsPartialEvaluationLinear (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, Differentiable ℝ (L z)) (j : Fin 2) (x : Pt 2) : E →ₗ[ℝ] Pt 2 where
  toFun z := pd j (L z) x
  map_add' z w := by
    rw [map_add]
    change pd j (fun y => L z y + L w y) x = _
    unfold pd
    rw [fderiv_fun_add (hL z x) (hL w x)]
    rfl
  map_smul' c z := by
    rw [map_smul]
    change pd j (fun y => c • L z y) x = c • pd j (L z) x
    unfold pd
    rw [fderiv_fun_const_smul (hL z x)]
    rfl

/-- Vorticity evaluated at a point, as a linear map on the finite-dimensional
velocity space. -/
def nsCurlEvaluationLinear (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, Differentiable ℝ (L z)) (x : Pt 2) : E →ₗ[ℝ] ℝ where
  toFun z := curl2 (L z) x
  map_add' z w := by
    have h0 := (nsPartialEvaluationLinear L hL 0 x).map_add z w
    have h1 := (nsPartialEvaluationLinear L hL 1 x).map_add z w
    change pd 0 (L (z + w)) x = pd 0 (L z) x + pd 0 (L w) x at h0
    change pd 1 (L (z + w)) x = pd 1 (L z) x + pd 1 (L w) x at h1
    simp only [curl2, h0, h1, Pi.add_apply]
    ring
  map_smul' c z := by
    have h0 := (nsPartialEvaluationLinear L hL 0 x).map_smul c z
    have h1 := (nsPartialEvaluationLinear L hL 1 x).map_smul c z
    change pd 0 (L (c • z)) x = c • pd 0 (L z) x at h0
    change pd 1 (L (c • z)) x = c • pd 1 (L z) x at h1
    simp only [curl2, h0, h1, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Differentiating a Galerkin coefficient curve commutes with its spatial
directional derivatives. -/
theorem ns_hasDerivAt_partial_evaluation (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, Differentiable ℝ (L z))
    {u : ℝ → E} {z : E} {t : ℝ} (hu : HasDerivAt u z t) (j : Fin 2) (x : Pt 2) :
    HasDerivAt (fun s => pd j (L (u s)) x) (pd j (L z) x) t := by
  exact ((nsPartialEvaluationLinear L hL j x).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hu)

/-- The vorticity derivative evidence needed in the enstrophy estimate follows
from the actual finite-dimensional time ODE. -/
theorem ns_hasDerivAt_curl_evaluation (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, Differentiable ℝ (L z))
    {u : ℝ → E} {z : E} {t : ℝ} (hu : HasDerivAt u z t) (x : Pt 2) :
    HasDerivAt (fun s => curl2 (L (u s)) x) (curl2 (L z) x) t := by
  exact ((nsCurlEvaluationLinear L hL x).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hu)

/-- The spatial partial derivative family as an algebraic linear map into
actual velocity functions. -/
def nsPartialFamilyLinear (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, Differentiable ℝ (L z)) (j : Fin 2) : E →ₗ[ℝ] (Pt 2 → Pt 2) :=
  LinearMap.pi (fun x => nsPartialEvaluationLinear L hL j x)

/-- Vorticity as an algebraic linear map into scalar functions. -/
def nsCurlFamilyLinear (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, Differentiable ℝ (L z)) : E →ₗ[ℝ] (Pt 2 → ℝ) :=
  LinearMap.pi (fun x => nsCurlEvaluationLinear L hL x)

/-- The partial derivative is jointly continuous in coefficient and space,
provided the reconstructed fields have two continuous spatial derivatives. -/
theorem ns_partial_evaluation_continuous (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, ContDiff ℝ 2 (L z)) (j : Fin 2) :
    Continuous (fun q : E × Pt 2 => pd j (L q.1) q.2) := by
  exact ns_finite_linear_evaluation_continuous
    (nsPartialFamilyLinear L (fun z => (hL z).differentiable (by norm_num)) j)
    (fun z => continuous_pd_of_C1 _ ((hL z).of_le (by norm_num)) j)

/-- The vorticity is jointly continuous in coefficient and space. -/
theorem ns_curl_evaluation_continuous (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, ContDiff ℝ 2 (L z)) :
    Continuous (fun q : E × Pt 2 => curl2 (L q.1) q.2) := by
  exact ns_finite_linear_evaluation_continuous
    (nsCurlFamilyLinear L (fun z => (hL z).differentiable (by norm_num)))
    (fun z => continuous_curl2 (hL z))

/-- The Laplacian is an actual linear map on the reconstructed finite-dimensional
velocity family. -/
def nsLaplacianFamilyLinear (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, ContDiff ℝ 2 (L z)) : E →ₗ[ℝ] (Pt 2 → Pt 2) :=
  ∑ j : Fin 2, nsPartialFamilyLinear
    (nsPartialFamilyLinear L (fun z => (hL z).differentiable (by norm_num)) j)
    (fun z => (contDiff_pd_of_C2 _ (hL z) j).differentiable one_ne_zero) j

omit [FiniteDimensional ℝ E] in
@[simp] theorem nsLaplacianFamilyLinear_apply (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, ContDiff ℝ 2 (L z)) (z : E) (x : Pt 2) :
    nsLaplacianFamilyLinear L hL z x = lap (L z) x := by
  simp only [nsLaplacianFamilyLinear, LinearMap.sum_apply, Finset.sum_apply]
  rfl

/-- The Laplacian is jointly continuous in coefficient and space. -/
theorem ns_laplacian_evaluation_continuous (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, ContDiff ℝ 2 (L z)) :
    Continuous (fun q : E × Pt 2 => lap (L q.1) q.2) := by
  simpa only [nsLaplacianFamilyLinear_apply] using
    ns_finite_linear_evaluation_continuous (nsLaplacianFamilyLinear L hL)
      (fun z => by
        change Continuous (lap (L z))
        apply continuous_pi
        intro k
        have heq : (fun x => lap (L z) x k) = lap (cmp (L z) k) :=
          funext fun x => (lap_component (L z) (hL z) k x).symm
        rw [heq]
        exact continuous_lap_of_C2 (cmp (L z) k) (contDiff_cmp (hL z) k))

/-- Time differentiation commutes with the spatial Laplacian in a finite
Galerkin family. -/
theorem ns_hasDerivAt_laplacian_evaluation (L : E →ₗ[ℝ] (Pt 2 → Pt 2))
    (hL : ∀ z, ContDiff ℝ 2 (L z))
    {u : ℝ → E} {z : E} {t : ℝ} (hu : HasDerivAt u z t) (x : Pt 2) :
    HasDerivAt (fun s => lap (L (u s)) x) (lap (L z) x) t := by
  simpa only [nsLaplacianFamilyLinear_apply] using
    ns_hasDerivAt_evaluation (nsLaplacianFamilyLinear L hL) hu x

end SpatialCalculus

end AnomDiss
