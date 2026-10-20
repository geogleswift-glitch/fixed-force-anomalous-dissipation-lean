module

public import RequestProject.EnergyCalc

/-!
# The kinetic-energy identity of classical two-dimensional Navier–Stokes solutions

The existence of a solution is not assumed in any external interface here: given an
`IsClassicalNS` witness, periodic integration by parts proves its energy identity.
Consequently an eventual existence theorem need not separately assume that identity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- A divergence-free periodic field does no work against a periodic pressure gradient. -/
lemma ns_pressure_work_zero (v : Pt 2 → Pt 2) (p : Pt 2 → ℝ)
    (hv : ContDiff ℝ 1 v) (hvp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0)
    (hp : ContDiff ℝ 1 p) (hpp : IsPeriodic p) :
    (∫ x in cell 2, dot (v x) (grad p x)) = 0 := by
  have hvk : ∀ k : Fin 2, ContDiff ℝ 1 (fun x => v x k) :=
    fun k => (contDiff_apply ℝ ℝ k).comp hv
  have hvkp : ∀ k : Fin 2, IsPeriodic (fun x => v x k) :=
    fun k x n => by simp [hvp x n]
  simp only [dot, grad]
  rw [integral_finset_sum (f := fun k x => v x k * pd k p x) _
    fun k _ => integrableOn_cell_of_continuous
      (((continuous_apply k).comp hv.continuous).mul (continuous_pd_of_C1 p hp k))]
  simp only [fun k => integral_mul_pd (fun x => v x k) p (hvk k) hp (hvkp k) hpp k]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum
    (f := fun k x => pd k (fun y => v y k) x * p x) _
    fun k _ => integrableOn_cell_of_continuous
      ((continuous_pd_of_C1 _ (hvk k) k).mul hp.continuous)]
  have heq : ∀ x, ∑ k : Fin 2, pd k (fun y => v y k) x * p x = 0 := by
    intro x
    rw [← Finset.sum_mul]
    have hd := hdiv x
    unfold divergence at hd
    simp only [← pd_component v x (hv.differentiable one_ne_zero x)] at hd
    rw [hd, zero_mul]
  simp [heq]

/-- The spatial Navier–Stokes energy balance, before integration in time. -/
lemma ns_spatial_energy_identity (ν : ℝ) (v W' g : Pt 2 → Pt 2) (p : Pt 2 → ℝ)
    (hv : ContDiff ℝ 2 v) (hvp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0)
    (hp : ContDiff ℝ 1 p) (hpp : IsPeriodic p) (hg : Continuous g)
    (heq : ∀ x, W' x + conv v v x + grad p x = ν • lap v x + g x) :
    (∫ x in cell 2, 2 * dot (v x) (W' x)) =
      -(2 * ν) * (∫ x in cell 2, gradSqV v x) +
        2 * (∫ x in cell 2, dot (g x) (v x)) := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hvk : ∀ k : Fin 2, ContDiff ℝ 2 (fun x => v x k) :=
    fun k => (contDiff_apply ℝ ℝ k).comp hv
  have hvk1 : ∀ k : Fin 2, ContDiff ℝ 1 (fun x => v x k) :=
    fun k => (hvk k).of_le (by norm_num)
  have hvkp : ∀ k : Fin 2, IsPeriodic (fun x => v x k) :=
    fun k x n => by simp [hvp x n]
  set S : Pt 2 → ℝ := fun x => ∑ k, 2 * v x k *
    (ν * lap (fun y => v y k) x - conv v (fun y => v y k) x)
  set P : Pt 2 → ℝ := fun x => dot (v x) (grad p x)
  set F : Pt 2 → ℝ := fun x => dot (g x) (v x)
  have hS : Continuous S := continuous_finset_sum _ fun k _ =>
    (continuous_const.mul ((continuous_apply k).comp hv.continuous)).mul
      ((continuous_const.mul (continuous_lap_of_C2 _ (hvk k))).sub
        (continuous_conv_of_C1 v hv.continuous _ (hvk1 k)))
  have hP : Continuous P := continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp hv.continuous).mul (continuous_pd_of_C1 p hp k)
  have hF : Continuous F := continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp hg).mul ((continuous_apply k).comp hv.continuous)
  have hSk : ∀ k : Fin 2, IntegrableOn (fun x => 2 * v x k *
      (ν * lap (fun y => v y k) x - conv v (fun y => v y k) x)) (cell 2) :=
    fun k => integrableOn_cell_of_continuous
      ((continuous_const.mul ((continuous_apply k).comp hv.continuous)).mul
        ((continuous_const.mul (continuous_lap_of_C2 _ (hvk k))).sub
          (continuous_conv_of_C1 v hv.continuous _ (hvk1 k))))
  have hS_eq : (∫ x in cell 2, S x) = -(2 * ν) * (∫ x in cell 2, gradSqV v x) := by
    rw [show S = fun x => ∑ k : Fin 2, 2 * v x k *
      (ν * lap (fun y => v y k) x - conv v (fun y => v y k) x) from rfl,
      integral_finset_sum _ (fun k _ => hSk k)]
    simp only [fun k => integral_energy_rhs ν v hv1 hvp hdiv
      (fun x => v x k) (hvk k) (hvkp k)]
    rw [← Finset.mul_sum]
    congr 1
    rw [← integral_finset_sum (f := fun k x => gradSq (fun y => v y k) x) _
      fun k _ => integrableOn_cell_of_continuous
        (continuous_finset_sum _ fun i _ => (continuous_pd_of_C1 _ (hvk1 k) i).pow 2)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    simp only [gradSq, gradSqV, pd_component v x (hv1.differentiable one_ne_zero x)]
    exact Finset.sum_comm
  have hP_eq : (∫ x in cell 2, P x) = 0 :=
    ns_pressure_work_zero v p hv1 hvp hdiv hp hpp
  have heq' : ∀ x, 2 * dot (v x) (W' x) = S x - 2 * P x + 2 * F x := by
    intro x
    have hW : W' x = ν • lap v x + g x - conv v v x - grad p x := by
      rw [← heq x]
      abel
    simp only [hW, S, P, F, dot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      lap_component v hv, conv_component v v (hv1.differentiable one_ne_zero), grad, Fin.sum_univ_two]
    ring
  rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc (fun x _ => heq' x),
    integral_add (f := fun x => S x - 2 * P x) (g := fun x => 2 * F x)
      ((integrableOn_cell_of_continuous hS).sub
      ((integrableOn_cell_of_continuous hP).const_mul 2))
      ((integrableOn_cell_of_continuous hF).const_mul 2),
    integral_sub (f := S) (g := fun x => 2 * P x) (integrableOn_cell_of_continuous hS)
      ((integrableOn_cell_of_continuous hP).const_mul 2),
    integral_const_mul, integral_const_mul, hS_eq, hP_eq]
  ring

/-- The spatial dissipation rate of a parabolically regular velocity is continuous. -/
lemma IsParabolicC12.continuousOn_gradSqV {T β : ℝ} (hT : 0 ≤ T) (hβ : 0 < β)
    {v : ℝ → Pt 2 → Pt 2} (hv : IsParabolicC12 T β v) :
    ContinuousOn (fun t => ∫ x in cell 2, gradSqV (v t) x) (Icc 0 T) := by
  refine continuousOn_integral_cell hT _ ?_
  unfold gradSqV
  refine continuousOn_finset_sum _ fun i _ => ?_
  have hi : ContinuousOn (fun q : ℝ × Pt 2 => pd i (v q.1) q.2) (Icc 0 T ×ˢ univ) :=
    continuousOn_of_timeHolder (by positivity)
      (fun t ht => continuous_pd_of_C1 _ ((hv.smooth_x t ht).of_le (by norm_num)) i)
      (hv.holder_d1_time i)
  exact continuousOn_finset_sum _ fun k _ => ((continuous_apply k).comp_continuousOn hi).pow 2

/-- Every classical two-dimensional Navier–Stokes solution satisfies the forced
kinetic-energy identity. Only continuity of each force slice is needed. -/
theorem IsClassicalNS.kinetic_energy_identity {T ν : ℝ} (hT : 0 ≤ T)
    {v₀ : Pt 2 → Pt 2} {g v : ℝ → Pt 2 → Pt 2} {p : ℝ → Pt 2 → ℝ}
    (hv : IsClassicalNS T ν v₀ g v p)
    (hg : ∀ t ∈ Icc 0 T, Continuous (g t)) :
    ∀ t ∈ Icc 0 T,
      l2sqV (v t) / 2 + ν * (∫ s in (0 : ℝ)..t, ∫ x in cell 2, gradSqV (v s) x) =
        l2sqV v₀ / 2 + (∫ s in (0 : ℝ)..t, ∫ x in cell 2, dot (g s x) (v s x)) := by
  obtain ⟨β, hβ, -, reg, preg⟩ := hv.regular
  obtain ⟨hform, hrcont⟩ := l2sqV_integral_form hT v (dt T v) reg.continuousOn
    (reg.holder_dt.continuousOn hβ) (fun s hs x =>
      (reg.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs.1 hs.2))
  set A : ℝ → ℝ := fun s => ∫ x in cell 2, 2 * dot (v s x) (dt T v s x)
  set D : ℝ → ℝ := fun s => ∫ x in cell 2, gradSqV (v s) x
  set W : ℝ → ℝ := fun s => ∫ x in cell 2, dot (g s x) (v s x)
  have hDcont : ContinuousOn D (Icc 0 T) := reg.continuousOn_gradSqV hT hβ
  have hbalance : ∀ s ∈ Icc 0 T, A s = -(2 * ν) * D s + 2 * W s := by
    intro s hs
    exact ns_spatial_energy_identity ν (v s) (dt T v s) (g s) (p s)
      (reg.smooth_x s hs) (hv.periodic_u s hs) (hv.div_free s hs)
      (preg.smooth_x s hs) (hv.periodic_p s hs) (hg s hs) (hv.eqn s hs)
  have hWcont : ContinuousOn W (Icc 0 T) := by
    have hc : ContinuousOn (fun s => (A s + 2 * ν * D s) / 2) (Icc 0 T) :=
      (hrcont.add ((continuousOn_const :
        ContinuousOn (fun _ : ℝ => 2 * ν) (Icc 0 T)).mul hDcont)).div_const 2
    apply hc.congr
    intro s hs
    dsimp only [A, D, W] at hbalance ⊢
    linarith [hbalance s hs]
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hDI : IntervalIntegrable D volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hDcont.mono hsub
  have hWI : IntervalIntegrable W volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hWcont.mono hsub
  have hAI : (∫ s in (0 : ℝ)..t, A s) =
      -(2 * ν) * (∫ s in (0 : ℝ)..t, D s) + 2 * (∫ s in (0 : ℝ)..t, W s) := by
    rw [intervalIntegral.integral_congr (fun s hs => hbalance s (by
      rw [uIcc_of_le ht.1] at hs
      exact hsub hs)), intervalIntegral.integral_add (hDI.const_mul _) (hWI.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have henergy := hform t ht
  rw [hv.init] at henergy
  change l2sqV (v t) = l2sqV v₀ + ∫ s in (0 : ℝ)..t, A s at henergy
  rw [hAI] at henergy
  change l2sqV (v t) / 2 + ν * (∫ s in (0 : ℝ)..t, D s) =
    l2sqV v₀ / 2 + (∫ s in (0 : ℝ)..t, W s)
  linarith

end AnomDiss
