module

public import RequestProject.ScalarSchauderSpatial
public import RequestProject.ScalarGlobalC2Bridge

/-!
# Spatial Hessian Hölder bounds for the actual scalar fixed point

Heat averaging preserves the Hölder seminorm of each initial Hessian entry.
The genuine divergence-form Duhamel terms inherit the Hölder exponent of
their flux derivatives. Combining them in the original mild equation yields
a time-uniform spatial Hessian estimate without changing the exponent.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

/-- The heat flow preserves every spatial Hessian Hölder seminorm, including
at zero variance. -/
theorem pd2_heatOp_holder_of_C2 {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : IsPeriodic f) {β H : ℝ}
    (hholder : ∀ i j x y,
      ‖pd i (pd j f) x - pd i (pd j f) y‖ ≤ H * ‖x - y‖ ^ β)
    (v : ℝ≥0) (i j : Fin 2) (x y : Pt 2) :
    ‖pd i (pd j (heatOp v f)) x - pd i (pd j (heatOp v f)) y‖ ≤
      H * ‖x - y‖ ^ β := by
  have hc : Continuous (pd i (pd j f)) :=
    continuous_pd_of_C1 _ (contDiff_pd_of_C2 f hf j) i
  have hper : IsPeriodic (pd i (pd j f)) :=
    isPeriodic_pd _ (isPeriodic_pd f hp j) i
  obtain ⟨C, hC⟩ := (isQP_zero_iff.2 hper).bdd hc
  rw [pd2_heatOp (isQP_zero_iff.2 hp) hf v i j x,
    pd2_heatOp (isQP_zero_iff.2 hp) hf v i j y]
  exact heatOp_holder_distance hc hC (hholder i j) v x y

lemma pd2_sub_fun_C2 (f g : Pt 2 → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (i j : Fin 2) :
    pd i (pd j (fun x => f x - g x)) =
      fun x => pd i (pd j f) x - pd i (pd j g) x := by
  rw [pd_sub_fun f g (hf.differentiable (by norm_num))
    (hg.differentiable (by norm_num)) j]
  exact pd_sub_fun _ _ ((contDiff_pd_of_C2 f hf j).differentiable one_ne_zero)
    ((contDiff_pd_of_C2 g hg j).differentiable one_ne_zero) i

/-- The actual scalar mild fixed point has uniformly spatially Hölder
Hessian entries at the same exponent as its initial Hessian and flux
derivatives. The source hypotheses are explicit and concern the actual flux. -/
theorem scalar_mild_fixedPoint_hessian_spatial_holder
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hβ0 : 0 < β) (hβ1 : β < 1)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u)
    (hfc : IsHolderC2 β (f : Pt 2 → ℂ)) (hfper : IsPeriodic f)
    (hflux : ∀ k : Fin 2,
      let G := extendSlabScalar hT (b k * u)
      Continuous (Function.uncurry (fun s x => pd k (G s) x)) ∧
      (∀ s, ContDiff ℝ 1 (G s)) ∧
      (∀ s, IsPeriodic (G s)) ∧
      (∃ C, ∀ s x, ‖pd k (G s) x‖ ≤ C) ∧
      (∃ H, 0 ≤ H ∧ ∀ s x y,
        ‖pd k (G s) x - pd k (G s) y‖ ≤ H * ‖x - y‖ ^ β)) :
    ∃ H, 0 ≤ H ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ i j x y,
      ‖pd i (pd j (extendSlabScalar hT u t)) x -
        pd i (pd j (extendSlabScalar hT u t)) y‖ ≤ H * ‖x - y‖ ^ β := by
  classical
  let A : ℝ → Pt 2 → ℂ := fun t => heatOp (Real.toNNReal (2 * ν * t)) f
  let D : Fin 2 → ℝ → Pt 2 → ℂ := fun k =>
    duhamelComponent ν (extendSlabScalar hT (b k * u)) k
  have hD2 : ∀ k t, 0 ≤ t → ContDiff ℝ 2 (D k t) := by
    intro k t ht
    obtain ⟨hc, hs, hp, ⟨C, hC⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    exact contDiff_two_duhamelComponent_of_flux_derivative_holder hν k hc hs hp hC hH
      hβ0 hholder ht
  have hDholder : ∀ k : Fin 2, ∃ K, 0 ≤ K ∧
      ∀ t, 0 ≤ t → ∀ i j x y,
        ‖pd i (pd j (D k t)) x - pd i (pd j (D k t)) y‖ ≤ K * ‖x - y‖ ^ β := by
    intro k
    obtain ⟨hc, hs, hp, ⟨C, hC⟩, ⟨H, hH, hholder⟩⟩ := hflux k
    let K := 4 * duhamelSpaceDerivativeScale ν H β / β +
      2 * duhamelThirdDerivativeScale ν H β / (1 - β)
    have hscale : 0 ≤ duhamelSpaceDerivativeScale ν H β := by
      have hg := gmom_nonneg (β + 1)
      have hg1 := gmom_nonneg 1
      unfold duhamelSpaceDerivativeScale
      positivity
    have hthird := duhamelThirdDerivativeScale_nonneg hν.le hH (β := β)
    have hK : 0 ≤ K := add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) hscale) hβ0.le)
      (div_nonneg (mul_nonneg (by norm_num) hthird) (by linarith))
    refine ⟨K, hK, fun t ht i j x y => ?_⟩
    have he : D k t = heatDuhamel ν
        (fun s => pd k (extendSlabScalar hT (b k * u) s)) t := by
      funext z
      exact duhamelComponent_eq_heatDuhamel_pd hν hs hp ht k z
    rw [he]
    exact pd2_heatDuhamel_spatial_schauder hν hc
      (fun s => isPeriodic_pd _ (hp s) k) hC hH hβ0 hβ1 hholder i j ht x y
  choose K hK hDK using hDholder
  obtain ⟨hf2, Hf, hHf⟩ := hfc
  let H₀ := max Hf 0
  have hH₀ : 0 ≤ H₀ := le_max_right _ _
  have hAH : ∀ t i j x y,
      ‖pd i (pd j (A t)) x - pd i (pd j (A t)) y‖ ≤ H₀ * ‖x - y‖ ^ β := by
    intro t i j x y
    exact pd2_heatOp_holder_of_C2 hf2 hfper
      (fun i j x y => (hHf i j x y).trans
        (mul_le_mul_of_nonneg_right (le_max_left Hf 0)
          (Real.rpow_nonneg (norm_nonneg _) _))) _ i j x y
  have hA2 : ∀ t, ContDiff ℝ 2 (A t) :=
    fun t => contDiff_heatOp (isQP_zero_iff.2 hfper) hf2 _
  have he : ∀ t ∈ Icc (0 : ℝ) T, extendSlabScalar hT u t =
      fun y => A t y - D 0 t y - D 1 t y := by
    intro t ht
    funext y
    rw [extendSlabScalar_of_mem hT u ht]
    have hh := congrArg (fun w : SlabScalar T => w (⟨t, ht⟩, y)) hu
    simpa [scalarMildMap, A, D, Fin.sum_univ_two, sub_add_eq_sub_sub] using hh.symm
  refine ⟨H₀ + K 0 + K 1, add_nonneg (add_nonneg hH₀ (hK 0)) (hK 1), ?_⟩
  intro t ht i j x y
  have hpd2 : ∀ z, pd i (pd j (extendSlabScalar hT u t)) z =
      pd i (pd j (A t)) z - pd i (pd j (D 0 t)) z - pd i (pd j (D 1 t)) z := by
    intro z
    rw [he t ht,
      pd2_sub_fun_C2 (fun y => A t y - D 0 t y) (D 1 t)
        ((hA2 t).sub (hD2 0 t ht.1)) (hD2 1 t ht.1) i j,
      pd2_sub_fun_C2 (A t) (D 0 t) (hA2 t) (hD2 0 t ht.1) i j]
  rw [hpd2 x, hpd2 y]
  have halg : ∀ a b c d e f : ℂ,
      (a - b - c) - (d - e - f) = ((a - d) - (b - e)) - (c - f) := by intros; ring
  rw [halg]
  calc
    ‖(pd i (pd j (A t)) x - pd i (pd j (A t)) y -
        (pd i (pd j (D 0 t)) x - pd i (pd j (D 0 t)) y)) -
        (pd i (pd j (D 1 t)) x - pd i (pd j (D 1 t)) y)‖
        ≤ (‖pd i (pd j (A t)) x - pd i (pd j (A t)) y‖ +
          ‖pd i (pd j (D 0 t)) x - pd i (pd j (D 0 t)) y‖) +
          ‖pd i (pd j (D 1 t)) x - pd i (pd j (D 1 t)) y‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (H₀ * ‖x - y‖ ^ β + K 0 * ‖x - y‖ ^ β) + K 1 * ‖x - y‖ ^ β :=
      add_le_add (add_le_add (hAH t i j x y) (hDK 0 t ht.1 i j x y))
        (hDK 1 t ht.1 i j x y)
    _ = _ := by ring

end AnomDiss
