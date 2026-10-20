module

public import RequestProject.Main
public import RequestProject.EnergyCalc
public import RequestProject.ScalarStages
public import RequestProject.NSClassicalEnergy

/-!
# Existence-only analytic interfaces

Uniqueness and energy identities are theorems for the classical solution
predicates used by this project. They need not be included in the external
analytic hypotheses. This module separates the existence interfaces; the
scalar interface is proved downstream in `ScalarGlobalSpatialSchauder`,
while the Navier--Stokes existence and regularity assertion remains open.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- The existence and regularity part of `ExternalNS2D`, without either the
energy identity or uniqueness as additional hypotheses. -/
def NSClassicalExistence : Prop :=
  ∀ (T ν : ℝ), 0 < T → 0 < ν → ∀ (v₀ : Pt 2 → Pt 2) (g : ℝ → Pt 2 → Pt 2),
    ContDiff ℝ ∞ v₀ → IsPeriodic v₀ → (∀ x, divergence v₀ x = 0) →
    (∫ x in cell 2, v₀ x) = 0 → IsTimeSmoothForce g → (∀ t, (∫ x in cell 2, g t x) = 0) →
    ∃ (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
      (∀ β, 0 < β → β < 1 → IsParabolicC12 T β v ∧ IsParabolicC01 T β p) ∧
      IsClassicalNS T ν v₀ g v p

/-- The existence and regularity part of `ExternalScalar`, without uniqueness. -/
def ScalarClassicalExistence : Prop :=
  ∀ (T ν β : ℝ), 0 < T → 0 < ν → 0 < β → β < 1 → ∀ (v : ℝ → Pt 2 → Pt 2),
    (∀ t ∈ Icc 0 T, IsPeriodic (v t)) → IsParabolicC01 T β v →
    (∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0) →
    ∀ θ₀ : Pt 2 → ℝ, IsPeriodic θ₀ → IsHolderC2 β θ₀ →
    ∃ θ : ℝ → Pt 2 → ℝ, IsParabolicC12 T β θ ∧ IsClassicalScalar T ν v θ₀ θ

/-- Scalar uniqueness is derived from the maximum principle; it is not an
additional analytic input. -/
theorem externalScalar_of_existence (hex : ScalarClassicalExistence) : ExternalScalar := by
  intro T ν β hT hν hβ0 hβ1 v hp hv hd θ₀ hθp hθ
  obtain ⟨θ, hreg, hsol⟩ := hex T ν β hT hν hβ0 hβ1 v hp hv hd θ₀ hθp hθ
  exact ⟨θ, hreg, hsol, fun θ' hsol' =>
    classical_scalar_unique T ν hν.le v θ₀ θ' θ hsol' hsol⟩

/-- This equivalence only removes a condition already formally proved; neither
side is asserted to hold without a proof of scalar existence. -/
theorem scalarClassicalExistence_iff_externalScalar :
    ScalarClassicalExistence ↔ ExternalScalar := by
  refine ⟨externalScalar_of_existence, ?_⟩
  intro hex T ν β hT hν hβ0 hβ1 v hp hv hd θ₀ hθp hθ
  obtain ⟨θ, hreg, hsol, -⟩ := hex T ν β hT hν hβ0 hβ1 v hp hv hd θ₀ hθp hθ
  exact ⟨θ, hreg, hsol⟩

/-- A continuous periodic vector field with zero kinetic energy vanishes
pointwise, including on the boundary of the fundamental cell. -/
lemma periodic_vector_eq_zero_of_l2sqV_eq_zero (w : Pt 2 → Pt 2)
    (hc : Continuous w) (hp : IsPeriodic w) (hz : l2sqV w = 0) : w = 0 := by
  let G : Pt 2 → ℝ := fun x => ∑ k, w x k ^ 2
  have hGc : Continuous G := continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp hc).pow 2
  have hG0 : 0 ≤ G := fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hae : G =ᵐ[(volume : Measure (Pt 2)).restrict (cell 2)] 0 :=
    (integral_eq_zero_iff_of_nonneg hG0 hGc.integrableOn_Icc).1 hz
  have hcell : cell 2 = Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) 1) := by
    simpa [cell] using (Set.pi_univ_Icc (0 : Pt 2) 1).symm
  have hclosure : closure (interior (cell 2)) = cell 2 := by
    rw [hcell, interior_pi_set (Set.finite_univ), closure_pi_set]
    simp only [interior_Icc, closure_Ioo (zero_ne_one' ℝ)]
  have heq : EqOn G 0 (cell 2) := Measure.eqOn_of_ae_eq hae hGc.continuousOn
    continuousOn_const (by rw [hclosure])
  have hwcell : ∀ x ∈ cell 2, w x = 0 := by
    intro x hx
    ext k
    have hs : w x k ^ 2 ≤ G x := Finset.single_le_sum
      (fun i _ => sq_nonneg (w x i)) (Finset.mem_univ k)
    have hz' := heq hx
    simp only [Pi.zero_apply] at hz'
    rw [hz'] at hs
    simpa only [Pi.zero_apply, sq_nonpos_iff] using hs
  funext x
  obtain ⟨y, hy, n, rfl⟩ := exists_cell_rep x
  simpa only [hp y n, Pi.zero_apply] using hwcell y hy

/-- Classical two-dimensional Navier--Stokes velocities with the same force
and initial data are unique. This is proved from the equations by the
perturbation energy estimate, without an external existence hypothesis. -/
theorem classical_ns_velocity_unique (T ν : ℝ) (hν : 0 ≤ ν)
    (u₀ : Pt 2 → Pt 2) (f : ℝ → Pt 2 → Pt 2)
    (u v : ℝ → Pt 2 → Pt 2) (p q : ℝ → Pt 2 → ℝ)
    (hu : IsClassicalNS T ν u₀ f u p) (hv : IsClassicalNS T ν u₀ f v q) :
    ∀ t ∈ Icc 0 T, u t = v t := by
  obtain ⟨β, hβ, -, ru, rp⟩ := hu.regular
  obtain ⟨γ, hγ, -, rv, rq⟩ := hv.regular
  choose C hC using rv.bdd_d1
  let B : ℝ := ∑ i, |C i|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpd : ∀ s ∈ Icc 0 T, ∀ x i, ‖pd i (v s) x‖ ≤ B := by
    intro s hs x i
    exact (hC i s hs x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_univ i)))
  have hgrad : ∀ s ∈ Icc 0 T, ∀ x, eucOp (fderiv ℝ (v s) x) ≤ 4 * B := by
    intro s hs x
    have hn := norm_fderiv_le_of_pd (v s) x hB (fun i => hpd s hs x i)
    calc eucOp (fderiv ℝ (v s) x) ≤ 2 * ‖fderiv ℝ (v s) x‖ := eucOp_le_two_norm _
      _ ≤ 2 * (2 * B) := mul_le_mul_of_nonneg_left (by simpa using hn) (by norm_num)
      _ = 4 * B := by ring
  let w : ℝ → Pt 2 → Pt 2 := fun s x => u s x - v s x
  let W : ℝ → Pt 2 → Pt 2 := fun s x => dt T u s x - dt T v s x
  let pressureDiff : ℝ → Pt 2 → ℝ := fun s x => p s x - q s x
  have hwp : ∀ s ∈ Icc 0 T, IsPeriodic (w s) := by
    intro s hs x n
    simp only [w, hu.periodic_u s hs x n, hv.periodic_u s hs x n]
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hen := perturbation_energy hT ν hν u w W v pressureDiff (fun _ => 4 * B)
    (ru.continuousOn.sub rv.continuousOn)
    ((ru.holder_dt.continuousOn hβ).sub (rv.holder_dt.continuousOn hγ))
    (fun s hs x =>
      ((ru.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)).sub
      ((rv.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)))
    (fun s hs => by
      have hs' := Ioo_subset_Icc_self hs
      have hus := ru.smooth_x s hs'
      have hvs := rv.smooth_x s hs'
      refine ⟨hus.of_le (by norm_num), hu.periodic_u s hs', hu.div_free s hs',
        hus.sub hvs, hwp s hs', ?_, (rp.smooth_x s hs').sub (rq.smooth_x s hs'),
        ?_, hvs.of_le (by norm_num), hgrad s hs'⟩
      · intro x
        rw [divergence_sub_fun _ _ (hus.differentiable (by norm_num))
          (hvs.differentiable (by norm_num)), hu.div_free s hs', hv.div_free s hs', sub_zero]
      · intro x n
        simp only [pressureDiff, hu.periodic_p s hs' x n, hv.periodic_p s hs' x n])
    (fun s hs x => by
      have hs' := Ioo_subset_Icc_self hs
      have hus := ru.smooth_x s hs'
      have hvs := rv.smooth_x s hs'
      have e1 := hu.eqn s hs' x
      have e2 := hv.eqn s hs' x
      change dt T u s x - dt T v s x + conv (u s) (fun y => u s y - v s y) x +
        conv (fun y => u s y - v s y) (v s) x + grad (fun y => p s y - q s y) x =
        ν • lap (fun y => u s y - v s y) x
      rw [conv_sub_right _ _ _ (hus.differentiable (by norm_num))
        (hvs.differentiable (by norm_num)), conv_sub_left,
        grad_sub_fun _ _ ((rp.smooth_x s hs').differentiable (by norm_num))
          ((rq.smooth_x s hs').differentiable (by norm_num)), lap_sub_fun _ _ hus hvs,
        smul_sub]
      rw [show dt T u s x - dt T v s x + (conv (u s) (u s) x - conv (u s) (v s) x) +
        (conv (u s) (v s) x - conv (v s) (v s) x) + (grad (p s) x - grad (q s) x) =
        (dt T u s x + conv (u s) (u s) x + grad (p s) x) -
        (dt T v s x + conv (v s) (v s) x + grad (q s) x) by abel, e1, e2]
      abel)
    continuousOn_const t ht
  have hw0 : w 0 = 0 := by
    funext x
    simp only [w, hu.init, hv.init, sub_self, Pi.zero_apply]
  rw [hw0] at hen
  simp only [l2sqV, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    integral_zero, zero_mul] at hen
  have hnonneg : 0 ≤ l2sqV (w t) := setIntegral_nonneg measurableSet_Icc fun x _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg (w t x k)
  have hzero : w t = 0 := periodic_vector_eq_zero_of_l2sqV_eq_zero (w t)
    ((ru.smooth_x t ht).continuous.sub (rv.smooth_x t ht).continuous) (hwp t ht)
    (le_antisymm hen hnonneg)
  funext x
  exact sub_eq_zero.mp (congrFun hzero x)

/-- The kinetic-energy identity and velocity uniqueness are proved from the
classical equations, rather than imported as part of the existence input. -/
theorem externalNS2D_of_existence (hex : NSClassicalExistence) : ExternalNS2D := by
  intro T ν hT hν v₀ g hs hp hd hm hg hgm
  obtain ⟨v, p, hreg, hsol⟩ := hex T ν hT hν v₀ g hs hp hd hm hg hgm
  exact ⟨v, p, hreg, hsol,
    hsol.kinetic_energy_identity hT.le (fun t _ => (hg.smooth_slice t).continuous),
    fun v' p' hsol' => classical_ns_velocity_unique T ν hν.le v₀ g v' v p' p hsol' hsol⟩

/-- This equivalence removes only formally derived energy and uniqueness
requirements; it does not supply a proof of analytic existence. -/
theorem nsClassicalExistence_iff_externalNS2D : NSClassicalExistence ↔ ExternalNS2D := by
  refine ⟨externalNS2D_of_existence, ?_⟩
  intro hex T ν hT hν v₀ g hs hp hd hm hg hgm
  obtain ⟨v, p, hreg, hsol, -, -⟩ := hex T ν hT hν v₀ g hs hp hd hm hg hgm
  exact ⟨v, p, hreg, hsol⟩

/-- The anomalous-dissipation theorem requires only the two analytic
existence/regularity inputs. Its energy and uniqueness ingredients have
independent Lean proofs. The existence inputs remain explicit premises. -/
theorem main_theorem_from_existence (hNS : NSClassicalExistence)
    (hSc : ScalarClassicalExistence) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x :=
  main_theorem (externalNS2D_of_existence hNS) (externalScalar_of_existence hSc) ε hε0 hε1

end AnomDiss
