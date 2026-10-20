module

public import RequestProject.DriftRegularity
public import RequestProject.External
public import RequestProject.ForceRegularity

/-!
# Proposition 4.9: true horizontal solutions

Assembly of the true horizontal solutions from the external results, the regularity of the
force (Lemma 4.6) and Lemma 1.7.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative is controlled by the partial derivatives. -/
lemma norm_fderiv_le_of_pd (f : Pt d → E) (z : Pt d) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j, ‖pd j f z‖ ≤ B) : ‖fderiv ℝ f z‖ ≤ d * B := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Pt d) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [hv, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖fderiv ℝ f z (v j • (Pi.single j (1 : ℝ) : Pt d))‖ ≤ ∑ _j : Fin d, B * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [map_smul, norm_smul, mul_comm]
        exact mul_le_mul (hB j) (norm_le_pi_norm v j) (norm_nonneg _) hB0
    _ = d * B * ‖∑ j, v j • (Pi.single j (1 : ℝ) : Pt d)‖ := by
        rw [← hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `C^{1+β/2,2+β}` is contained in `C^{β/2,1+β}` on a bounded time interval. -/
lemma IsParabolicC12.toC01 {T β : ℝ} (hT : 0 ≤ T) (hβ0 : 0 < β) (hβ1 : β < 1)
    {u : ℝ → Pt d → E} (hu : IsParabolicC12 T β u) : IsParabolicC01 T β u := by
  refine ⟨fun t ht => (hu.smooth_x t ht).of_le (by norm_num), hu.bdd, ?_, hu.bdd_d1, fun i => ?_⟩
  · obtain ⟨C, hC⟩ := hu.time_lipschitz
    refine ⟨|C| * T ^ (1 - β / 2), fun t ht s hs x => ?_⟩
    have hr : |t - s| ≤ T := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
    calc ‖u t x - u s x‖ ≤ C * |t - s| := hC x t ht s hs
      _ ≤ |C| * |t - s| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      _ ≤ |C| * (T ^ (1 - β / 2) * |t - s| ^ (β / 2)) :=
          mul_le_mul_of_nonneg_left (le_rpow_bound (abs_nonneg _) hr (by linarith)) (abs_nonneg _)
      _ = _ := by ring
  · obtain ⟨B1, hB1⟩ := hu.bdd_d1 i
    choose B2 hB2 using fun j => hu.bdd_d2 j i
    obtain ⟨Ct, hCt⟩ := hu.holder_d1_time i
    set B := ∑ j, |B2 j|
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hBj : ∀ j, |B2 j| ≤ B := fun j =>
      Finset.single_le_sum (f := fun j => |B2 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    -- spatial Hölder bound
    have hsp : ∀ t ∈ Icc 0 T, ∀ x y, ‖pd i (u t) x - pd i (u t) y‖ ≤
        (2 * |B1| + d * B) * ‖x - y‖ ^ β := by
      intro t ht x y
      have hC1 : ContDiff ℝ 1 (pd i (u t)) := contDiff_pd_of_C2 _ (hu.smooth_x t ht) i
      refine holder_of_lip_bdd _ (by positivity) (fun z => (hB1 t ht z).trans (le_abs_self _))
        (fun x y => ?_) hβ0.le hβ1.le x y
      have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (hC1.differentiable one_ne_zero) z)
        (fun z _ => norm_fderiv_le_of_pd (pd i (u t)) z hB0
          (fun j => (hB2 j t ht z).trans ((le_abs_self _).trans (hBj j))))
        (mem_univ y) (mem_univ x)
      simpa using this
    refine ⟨(2 * |B1| + d * B) + |Ct| * T ^ (1 / 2 : ℝ), fun t ht s hs x y => ?_⟩
    have hr : |t - s| ≤ T := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
    have htime : ‖pd i (u t) y - pd i (u s) y‖ ≤ |Ct| * T ^ (1 / 2 : ℝ) * |t - s| ^ (β / 2) := by
      refine (hCt t ht s hs y).trans ?_
      have hsplit : |t - s| ^ ((1 + β) / 2) = |t - s| ^ (1 / 2 : ℝ) * |t - s| ^ (β / 2) := by
        rw [← Real.rpow_add' (abs_nonneg _) (by positivity)]; ring_nf
      rw [hsplit]
      calc Ct * (|t - s| ^ (1 / 2 : ℝ) * |t - s| ^ (β / 2))
          ≤ |Ct| * (|t - s| ^ (1 / 2 : ℝ) * |t - s| ^ (β / 2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |Ct| * (T ^ (1 / 2 : ℝ) * |t - s| ^ (β / 2)) := by
            gcongr
        _ = _ := by ring
    have h1 := hsp t ht x y
    have hxy : 0 ≤ ‖x - y‖ ^ β := by positivity
    have hts : 0 ≤ |t - s| ^ (β / 2) := by positivity
    have hc1 : 0 ≤ 2 * |B1| + d * B := by positivity
    have hc2 : 0 ≤ |Ct| * T ^ (1 / 2 : ℝ) := by positivity
    calc ‖pd i (u t) x - pd i (u s) y‖
        ≤ ‖pd i (u t) x - pd i (u t) y‖ + ‖pd i (u t) y - pd i (u s) y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (2 * |B1| + d * B) * ‖x - y‖ ^ β + |Ct| * T ^ (1 / 2 : ℝ) * |t - s| ^ (β / 2) :=
          add_le_add h1 htime
      _ ≤ _ := by nlinarith

/-- **Proposition 4.9** (true horizontal solutions).  Assuming the external results, for every
`ν > 0` and `ω` there is a classical solution `(v,p)` of the forced 2D Navier–Stokes system on
`[0,1]` with force `g_ω` and `v(0) = 0`, lying in `C^{1+β/2,2+β} × C^{β/2,1+β}` for every
`β`, satisfying the energy identity; and for every smooth periodic `θ₀` the advection–diffusion
equation with drift `v` has a unique classical solution, which satisfies the maximum principle
and the scalar energy identity. -/
theorem true_horizontal_existence (hNS : ExternalNS2D) (hSc : ExternalScalar) (ν : ℝ)
    (hν : 0 < ν) (w : Phase) :
    ∃ (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
      IsClassicalNS 1 ν 0 (gForce w) v p ∧
      (∀ β, 0 < β → β < 1 → IsParabolicC12 1 β v ∧ IsParabolicC01 1 β p) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, l2sqV (v t) / 2 + ν * ∫ s in (0 : ℝ)..t, ∫ x in cell 2, gradSqV (v s) x
          = ∫ s in (0 : ℝ)..t, ∫ x in cell 2, dot (gForce w s x) (v s x)) ∧
      ∀ θ₀ : Pt 2 → ℝ, ContDiff ℝ ∞ θ₀ → IsPeriodic θ₀ →
        ∃ θ : ℝ → Pt 2 → ℝ, IsClassicalScalar 1 ν v θ₀ θ ∧
          (∀ θ', IsClassicalScalar 1 ν v θ₀ θ' → ∀ t ∈ Icc (0 : ℝ) 1, θ' t = θ t) ∧
          (∀ M, (∀ x, |θ₀ x| ≤ M) → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |θ t x| ≤ M) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, l2sq (θ t) / 2 + dissipation ν θ t = l2sq θ₀ / 2) := by
  obtain ⟨hadm, hmean⟩ := force_regularity.1 w
  obtain ⟨v, p, hreg, hns, hen, -⟩ := hNS 1 ν one_pos hν 0 (gForce w) contDiff_const
    (fun _ _ => rfl) (fun x => by simp [divergence, pd]) (by simp) hadm.toIsTimeSmoothForce hmean
  refine ⟨v, p, hns, hreg, fun t ht => ?_, fun θ₀ hθ₀ hp => ?_⟩
  · have h0 : l2sqV (0 : Pt 2 → Pt 2) = 0 := by simp [l2sqV]
    have := hen t ht
    rw [h0, zero_div, zero_add] at this
    exact this
  have hvC01 : IsParabolicC01 1 (1 / 2) v :=
    (hreg (1 / 2) (by norm_num) (by norm_num)).1.toC01 zero_le_one (by norm_num) (by norm_num)
  obtain ⟨θ, -, hθ, huniq⟩ := hSc 1 ν (1 / 2) one_pos hν (by norm_num) (by norm_num) v
    hns.periodic_u hvC01 hns.div_free θ₀ hp
    (holderC2_of_smooth_periodic θ₀ hθ₀ hp (by norm_num) (by norm_num))
  obtain ⟨hmax, hen'⟩ := scalar_energy_max 1 ν (1 / 2) hν v hns.periodic_u hvC01 hns.div_free
    θ₀ θ hθ
  exact ⟨θ, hθ, huniq, hmax, hen'⟩

end AnomDiss
