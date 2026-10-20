module

public import RequestProject.TorusCOV
public import RequestProject.H2Heat
public import RequestProject.H2Comp
public import RequestProject.Commutator
public import RequestProject.HeatInterpDeriv
public import RequestProject.SplitRepFull
public import RequestProject.SplitConvergence
public import RequestProject.Residue
public import RequestProject.Comparison

/-!
# Lemma 3.10: `L²` convergence of the Lie splitting

For a smooth, periodic, divergence-free field `V`, each splitting step
`g ↦ H_{2κτ}(g ∘ Φ_{t₁ → t₀})` is compared with the exact solution `h` through the interpolant
`z(r) = H_{2κ(r - t₀)}(g ∘ Φ_{r → t₀})`, which solves the advection–diffusion equation up to the
commutator `V·∇z - H(V·∇(g ∘ Φ))`.  The energy estimate gives a local error `O(κτ²‖g‖_{H²})`,
while the `H²` norm grows by at most a factor `1 + Cτ` per step.  Summing over the `n` steps
yields `‖P_n h - T h‖₂ ≤ (Cκ/n)‖h‖_{H²}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {ξ : Pt 2}

/-- One splitting step from time `t₀` to time `t₁`: `g ↦ H_{2κ(t₁-t₀)}(g ∘ Φ_{t₁ → t₀})`. -/
def stepOut (V : ℝ → Pt 2 → Pt 2) (κ t₀ t₁ : ℝ) (g : Pt 2 → ℂ) : Pt 2 → ℂ :=
  heatOp (Real.toNNReal (2 * κ * (t₁ - t₀))) (g ∘ gflow V t₁ t₀)

lemma stepOut_regular {V : ℝ → Pt 2 → Pt 2} {Bd : ℕ → ℝ} (hS : SmoothField V Bd)
    (hper : ∀ s x (m : Fin 2 → ℤ), V s (x + intVec m) = V s x) {g : Pt 2 → ℂ}
    (hg : ContDiff ℝ 2 g) (hqp : IsQP ξ g) (κ t₀ t₁ : ℝ) :
    ContDiff ℝ 2 (stepOut V κ t₀ t₁ g) ∧ IsQP ξ (stepOut V κ t₀ t₁ g) := by
  have hF : ContDiff ℝ 2 (g ∘ gflow V t₁ t₀) :=
    hg.comp (gflow_C2 hS.toGood hS.toC2 t₁ t₀).1
  have hFq : IsQP ξ (g ∘ gflow V t₁ t₀) := hqp.comp_lift (gflow_isLift hS.toGood hper t₁ t₀)
  exact ⟨contDiff_heatOp hFq hF _, heatOp_isQP hFq _⟩

/-- The `H²` density along the backward flow: pointwise and integrated growth by `1 + G|t - t₀|`. -/
theorem flow_h2_bound (Bd : ℕ → ℝ) : ∃ G : ℝ, 0 ≤ G ∧ ∀ (V : ℝ → Pt 2 → Pt 2),
    SmoothField V Bd → (∀ s y, TraceFree (fderiv ℝ (V s) y)) →
    (∀ s x (m : Fin 2 → ℤ), V s (x + intVec m) = V s x) →
    ∀ (ξ : Pt 2) (g : Pt 2 → ℂ) (t t₀ : ℝ), ContDiff ℝ 2 g → IsQP ξ g → |t - t₀| ≤ 1 →
    (∀ y, h2Dens (g ∘ gflow V t t₀) y ≤ (1 + G * |t - t₀|) * h2Dens g (gflow V t t₀ y)) ∧
    ∫ y in cell 2, h2Dens (g ∘ gflow V t t₀) y ≤ (1 + G * |t - t₀|) * ∫ y in cell 2, h2Dens g y := by
  obtain ⟨Cc, hCc0, hcomp⟩ := h2Dens_comp_le
  set A := (Bd 1 + Bd 2) * Real.exp (3 * Bd 1) with hA
  refine ⟨Cc * |A| * (1 + |A|) ^ 3, by positivity, ?_⟩
  intro V hS hdiv hper ξ g t t₀ hg hqp hτ
  have hB1 := hS.B_nonneg 1
  have hB2 := hS.B_nonneg 2
  have hA0 : 0 ≤ A := by positivity
  rw [abs_of_nonneg hA0]
  set τ := |t - t₀| with hτdef
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hfl := gflow_C2 hS.toGood hS.toC2 t t₀
  have hτ' : |t₀ - t| = τ := abs_sub_comm _ _
  simp only [NNReal.coe_mk, hτ'] at hfl
  have hexp1 : Real.exp (Bd 1 * τ) ≤ Real.exp (3 * Bd 1) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hexp3 : Real.exp (3 * Bd 1 * τ) ≤ Real.exp (3 * Bd 1) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hD1 : ∀ x, ‖fderiv ℝ (gflow V t t₀) x - ContinuousLinearMap.id ℝ (Pt 2)‖ ≤ A * τ := by
    intro x
    refine ((hfl.2 x).1).trans ?_
    change Bd 1 * τ * Real.exp (Bd 1 * τ) ≤ A * τ
    rw [hA]
    have : Bd 1 * τ * Real.exp (Bd 1 * τ) ≤ Bd 1 * τ * Real.exp (3 * Bd 1) := by gcongr
    nlinarith [mul_nonneg (mul_nonneg hB2 hτ0) (Real.exp_pos (3 * Bd 1)).le]
  have hD2 : ∀ x, ‖fderiv ℝ (fderiv ℝ (gflow V t t₀)) x‖ ≤ A * τ := by
    intro x
    refine ((hfl.2 x).2).trans ?_
    change Bd 2 * τ * Real.exp (3 * Bd 1 * τ) ≤ A * τ
    rw [hA]
    have : Bd 2 * τ * Real.exp (3 * Bd 1 * τ) ≤ Bd 2 * τ * Real.exp (3 * Bd 1) := by gcongr
    nlinarith [mul_nonneg (mul_nonneg hB1 hτ0) (Real.exp_pos (3 * Bd 1)).le]
  have hpt : ∀ y, h2Dens (g ∘ gflow V t t₀) y ≤
      (1 + Cc * A * (1 + A) ^ 3 * τ) * h2Dens g (gflow V t t₀ y) := by
    intro y
    refine (hcomp g _ (A * τ) hg hfl.1 (by positivity) hD1 hD2 y).trans ?_
    gcongr ?_ * _
    · exact h2Dens_nonneg _ _
    have h1 : (1 + A * τ) ^ 3 ≤ (1 + A) ^ 3 := by
      gcongr; nlinarith
    calc 1 + Cc * (A * τ) * (1 + A * τ) ^ 3 ≤ 1 + Cc * (A * τ) * (1 + A) ^ 3 := by gcongr
      _ = 1 + Cc * A * (1 + A) ^ 3 * τ := by ring
  refine ⟨hpt, ?_⟩
  have hYc : ContDiff ℝ 2 (g ∘ gflow V t t₀) := hg.comp hfl.1
  calc ∫ y in cell 2, h2Dens (g ∘ gflow V t t₀) y
      ≤ ∫ y in cell 2, (1 + Cc * A * (1 + A) ^ 3 * τ) * h2Dens g (gflow V t t₀ y) :=
        setIntegral_mono (integrableOn_cell_of_continuous (continuous_h2Dens hYc))
          (integrableOn_cell_of_continuous (continuous_const.mul
            ((continuous_h2Dens hg).comp (hS.toGood.continuous_gflow t t₀)))) hpt
    _ = (1 + Cc * A * (1 + A) ^ 3 * τ) * ∫ y in cell 2, h2Dens g y := by
        rw [integral_const_mul]
        congr 1
        exact integral_cell_comp_lift (hfl.1.of_le (by norm_num))
          (hS.toGood.continuous_gflow t₀ t) (fun x => hS.toGood.gflow_inv t t₀ x)
          (fun x => hS.toGood.gflow_inv t₀ t x) (gflow_isLift hS.toGood hper t t₀)
          (fun x => det_jac_gflow hS hdiv t t₀ x) (periodic_h2Dens hqp hg)

/-- **One step of the splitting** in `L²`, together with the growth of the `H²` norm. -/
theorem split_step_L2 (Bd : ℕ → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → Pt 2 → Pt 2) (Lt : ℝ),
    SmoothField V Bd → (∀ s y, TraceFree (fderiv ℝ (V s) y)) →
    (∀ s x (m : Fin 2 → ℤ), V s (x + intVec m) = V s x) →
    (∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) →
    ∀ (ξ : Pt 2) (κ β : ℝ) (h : ℝ → Pt 2 → ℂ), 0 ≤ κ → IsParabolicC12 1 β h →
    (∀ s ∈ Icc (0 : ℝ) 1, IsQP ξ (h s)) →
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ y, dt 1 h s y + conv (V s) (h s) y = κ • lap (h s) y) →
    ∀ (g : Pt 2 → ℂ) (t₀ t₁ : ℝ), ContDiff ℝ 2 g → IsQP ξ g → 0 ≤ t₀ → t₀ < t₁ → t₁ ≤ 1 →
    Real.sqrt (∫ y in cell 2, ‖stepOut V κ t₀ t₁ g y - h t₁ y‖ ^ 2) ≤
        Real.sqrt (∫ y in cell 2, ‖g y - h t₀ y‖ ^ 2) +
          C * κ * (t₁ - t₀) ^ 2 * Real.sqrt (∫ y in cell 2, h2Dens g y) ∧
      ∫ y in cell 2, h2Dens (stepOut V κ t₀ t₁ g) y ≤
        (1 + C * (t₁ - t₀)) * ∫ y in cell 2, h2Dens g y := by
  obtain ⟨G, hG0, hflow⟩ := flow_h2_bound Bd
  obtain ⟨Cm, hCm0, hcomm⟩ := commutator_L2
  set K' := |Bd 1| + |Bd 2| with hK'
  set Cr := 2 * Real.sqrt Cm * K' * Real.sqrt (1 + G) with hCr
  have hK'0 : 0 ≤ K' := by positivity
  have hK1 : Bd 1 ≤ K' := by rw [hK']; linarith [le_abs_self (Bd 1), abs_nonneg (Bd 2)]
  have hK2 : Bd 2 ≤ K' := by rw [hK']; linarith [le_abs_self (Bd 2), abs_nonneg (Bd 1)]
  have hCr0 : 0 ≤ Cr := by positivity
  refine ⟨G + Cr, by positivity, ?_⟩
  intro V Lt hS hdiv hper hLt ξ κ β h hκ hreg hqph heqh g t₀ t₁ hg hqp h0 h01 h1
  have hGd := hS.toGood
  have hC2V := hS.toC2
  have hB0 := hS.B_nonneg 0
  set τ := t₁ - t₀ with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  have hτ1 : τ ≤ 1 := by rw [hτ]; linarith
  set Mg := ∫ y in cell 2, h2Dens g y with hMg
  have hMg0 : 0 ≤ Mg := setIntegral_nonneg measurableSet_Icc fun y _ => h2Dens_nonneg _ _
  -- the transported data
  set F : ℝ → Pt 2 → ℂ := fun t => g ∘ gflow V t t₀ with hF
  have hFC : ∀ t, ContDiff ℝ 2 (F t) := fun t => hg.comp (gflow_C2 hGd hC2V t t₀).1
  have hFq : ∀ t, IsQP ξ (F t) := fun t => hqp.comp_lift (gflow_isLift hGd hper t t₀)
  set vv : ℝ → ℝ≥0 := fun t => Real.toNNReal (2 * κ * (t - t₀)) with hvv
  set z : ℝ → Pt 2 → ℂ := fun t => heatOp (vv t) (F t) with hz
  have hzC : ∀ t, ContDiff ℝ 2 (z t) := fun t => contDiff_heatOp (hFq t) (hFC t) _
  have hzq : ∀ t, IsQP ξ (z t) := fun t => heatOp_isQP (hFq t) _
  have hτt : ∀ t ∈ Icc t₀ t₁, |t - t₀| ≤ 1 := fun t ht => by
    rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
  have hGt : ∀ t ∈ Icc t₀ t₁, 1 + G * |t - t₀| ≤ 1 + G := fun t ht => by
    have := hτt t ht; nlinarith
  -- `H²` bounds along the flow
  have hFM : ∀ t ∈ Icc t₀ t₁, ∫ y in cell 2, h2Dens (F t) y ≤ (1 + G) * Mg := fun t ht =>
    ((hflow V hS hdiv hper ξ g t t₀ hg hqp (hτt t ht)).2).trans (by gcongr; linarith [hGt t ht])
  obtain ⟨Cg, hCg⟩ := bdd_h2Dens hqp hg
  have hCg0 : 0 ≤ Cg := (h2Dens_nonneg g 0).trans (hCg 0)
  set D := Real.sqrt ((1 + G) * Cg) with hD
  have hFpt : ∀ t ∈ Icc t₀ t₁, ∀ y, Real.sqrt (h2Dens (F t) y) ≤ D := fun t ht y => by
    refine Real.sqrt_le_sqrt (((hflow V hS hdiv hper ξ g t t₀ hg hqp (hτt t ht)).1 y).trans ?_)
    exact mul_le_mul (hGt t ht) (hCg _) (h2Dens_nonneg _ _) (by positivity)
  have hpdF : ∀ t ∈ Icc t₀ t₁, ∀ j y, ‖pd j (F t) y‖ ≤ D := fun t ht j y =>
    (norm_pd_le_sqrt_h2Dens _ j y).trans (hFpt t ht y)
  have hpd2F : ∀ t ∈ Icc t₀ t₁, ∀ i j y, ‖pd i (pd j (F t)) y‖ ≤ D := fun t ht i j y =>
    (norm_pd2_le_sqrt_h2Dens _ i j y).trans (hFpt t ht y)
  -- facts about the solution `h`
  have hIcc : ∀ t ∈ Icc t₀ t₁, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨h0.trans ht.1, ht.2.trans h1⟩
  have hIoo : ∀ t ∈ Ioo t₀ t₁, t ∈ Icc t₀ t₁ := fun t ht => ⟨ht.1.le, ht.2.le⟩
  have hhC : ∀ t ∈ Icc t₀ t₁, ContDiff ℝ 2 (h t) := fun t ht => hreg.smooth_x t (hIcc t ht)
  obtain ⟨Ch, hCh⟩ := hreg.bdd
  obtain ⟨Cd, hCd⟩ := hreg.bdd_dt
  have hhder : ∀ t ∈ Ioo t₀ t₁, ∀ x, HasDerivAt (fun s => h s x) (dt 1 h t x) t := by
    intro t ht x
    have hmem : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
    exact ((hreg.diff_t x t (hIcc t (hIoo t ht))).hasDerivWithinAt).hasDerivAt hmem
  have hhcont : ∀ x, ContinuousOn (fun s => h s x) (Icc t₀ t₁) := by
    intro x
    have : ContinuousOn (fun s => h s x) (Icc (0 : ℝ) 1) := fun t ht =>
      (hreg.diff_t x t ht).continuousWithinAt
    exact this.mono (Icc_subset_Icc h0 h1)
  -- bound for `g`
  obtain ⟨C0, hC0⟩ := hqp.bdd hg.continuous
  -- the field
  have hVC : ∀ t, ContDiff ℝ 2 (V t) := fun t =>
    (hS.contDiff_slice t).of_le (by exact_mod_cast natCast_le_inf 2)
  have hVdiv : ∀ t x, divergence (V t) x = 0 := by
    intro t x
    have := hdiv t x
    unfold TraceFree at this
    unfold divergence pd
    simpa [Fin.sum_univ_two] using this
  -- the energy estimate
  set ρ := Cr * κ * τ * Real.sqrt Mg with hρ
  have hE := energy_step_L2 (a := t₀) (b := t₁) (κ := κ) (ρ := ρ) h01.le hκ (by positivity)
    (B := V) (fun t => (hVC t).of_le (by norm_num)) (fun t x m => hper t x m) hVdiv
    (e := fun t x => z t x - h t x)
    (e' := fun t x => κ • lap (z t) x - heatOp (vv t) (conv (V t) (F t)) x - dt 1 h t x)
    (R := fun t x => conv (V t) (z t) x - heatOp (vv t) (conv (V t) (F t)) x)
    (fun t ht => (hzC t).continuous.sub (hhC t ht).continuous)
    (fun t ht => (hzC t).sub (hhC t (hIoo t ht)))
    (fun t ht => (hzq t).sub (hqph t (hIcc t (hIoo t ht))))
    (fun x => (continuous_heat_interp hGd hg hqp κ t₀ x).continuousOn.sub (hhcont x))
    (fun t ht x => (hasDerivAt_heat_interp hGd hC2V hLt hper hg hqp hκ ht.1 x).sub
      (hhder t ht x))
    ⟨C0 + Ch, fun t ht x => by
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hCh t (hIcc t ht) x))
      exact norm_heatOp_le (fun y => hC0 _) _ _⟩
    ⟨κ * (2 * D) + 2 * (Bd 0 * D) + Cd, fun t ht x => by
      have ht' := hIoo t ht
      have hlap : ‖lap (z t) x‖ ≤ 2 * D := by
        unfold lap
        refine (norm_sum_le _ _).trans ?_
        have : ∀ i, ‖pd i (pd i (z t)) x‖ ≤ D := fun i => by
          rw [hz]; simp only
          rw [pd2_heatOp (hFq t) (hFC t)]
          exact norm_heatOp_le (fun y => hpd2F t ht' i i y) _ _
        simp only [Fin.sum_univ_two]; linarith [this 0, this 1]
      have hconv : ‖heatOp (vv t) (conv (V t) (F t)) x‖ ≤ 2 * (Bd 0 * D) :=
        norm_heatOp_le (fun y => norm_conv_le (hS.norm_le t) (hpdF t ht') y) _ _
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add ?_ hconv)) (hCd t (hIcc t ht') x))
      rw [norm_smul, Real.norm_of_nonneg hκ]
      exact mul_le_mul_of_nonneg_left hlap hκ⟩
    (fun t ht x => by
      have ht' := hIcc t (hIoo t ht)
      have hd : dt 1 h t x = κ • lap (h t) x - conv (V t) (h t) x := by
        rw [← heqh t ht' x]; abel
      show _ = -conv (V t) (fun y => z t y - h t y) x + κ • lap (fun y => z t y - h t y) x + _
      rw [conv_sub_right _ _ _ ((hzC t).differentiable (by norm_num))
        ((hhC t (hIoo t ht)).differentiable (by norm_num)),
        lap_sub_fun _ _ (hzC t) (hhC t (hIoo t ht))]
      beta_reduce
      rw [hd, smul_sub]
      abel)
    (fun t ht => (continuous_conv (hVC t).continuous ((hzC t).of_le (by norm_num))).sub
      (continuous_gavg (continuous_conv (hVC t).continuous ((hFC t).of_le (by norm_num)))
        (fun y => norm_conv_le (hS.norm_le t) (hpdF t (hIoo t ht)) y) _))
    (fun t ht => by
      have ht' := hIoo t ht
      have hc := hcomm (V t) (Bd 0) K' ξ (F t) (vv t) (hVC t) (hS.norm_le t)
        (fun x => (hS.norm_fderiv_le t x).trans hK1)
        (fun x => (hS.norm_fderiv_fderiv_le t x).trans hK2)
        (hFC t) (hFq t)
      have hv : (vv t : ℝ) ≤ 2 * κ * τ := by
        rw [hvv]; simp only
        rw [Real.coe_toNNReal _ (by nlinarith [ht.1])]
        nlinarith [ht.2]
      have hv0 : (0 : ℝ) ≤ vv t := (vv t).2
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, hc.trans ?_⟩
      have hsq : ρ ^ 2 = Cm * K' ^ 2 * (2 * κ * τ) ^ 2 * ((1 + G) * Mg) := by
        rw [hρ, hCr]
        have e1 := Real.sq_sqrt hCm0
        have e2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + G by linarith)
        have e3 := Real.sq_sqrt hMg0
        calc (2 * Real.sqrt Cm * K' * Real.sqrt (1 + G) * κ * τ * Real.sqrt Mg) ^ 2
            = 4 * (Real.sqrt Cm) ^ 2 * K' ^ 2 * (Real.sqrt (1 + G)) ^ 2 * κ ^ 2 * τ ^ 2 *
              (Real.sqrt Mg) ^ 2 := by ring
          _ = _ := by rw [e1, e2, e3]; ring
      rw [hsq]
      have hvv2 : (vv t : ℝ) ^ 2 ≤ (2 * κ * τ) ^ 2 := pow_le_pow_left₀ hv0 hv 2
      have hint0 : 0 ≤ ∫ y in cell 2, h2Dens (F t) y :=
        setIntegral_nonneg measurableSet_Icc fun y _ => h2Dens_nonneg _ _
      calc Cm * K' ^ 2 * (vv t : ℝ) ^ 2 * ∫ y in cell 2, h2Dens (F t) y
          ≤ Cm * K' ^ 2 * (2 * κ * τ) ^ 2 * ∫ y in cell 2, h2Dens (F t) y := by gcongr
        _ ≤ Cm * K' ^ 2 * (2 * κ * τ) ^ 2 * ((1 + G) * Mg) := by gcongr; exact hFM t ht')
  -- identify the endpoints
  have hz0 : ∀ x, z t₀ x = g x := by
    intro x
    rw [hz, hvv]; simp only [sub_self, mul_zero, Real.toNNReal_zero]
    rw [heatOp_zero (hFC t₀).continuous, hF]
    simp [hGd.gflow_self]
  simp only [hz0] at hE
  constructor
  · refine hE.trans ?_
    have : ρ * τ ≤ (G + Cr) * κ * τ ^ 2 * Real.sqrt Mg := by
      rw [hρ]
      have : 0 ≤ κ * τ ^ 2 * Real.sqrt Mg := by positivity
      nlinarith
    exact add_le_add_right this _
  · calc ∫ y in cell 2, h2Dens (stepOut V κ t₀ t₁ g) y
        ≤ ∫ y in cell 2, h2Dens (F t₁) y := integral_h2Dens_heatOp_le (hFq t₁) (hFC t₁) _
      _ ≤ (1 + G * |t₁ - t₀|) * Mg := (hflow V hS hdiv hper ξ g t₁ t₀ hg hqp
          (hτt t₁ ⟨h01.le, le_rfl⟩)).2
      _ ≤ (1 + (G + Cr) * τ) * Mg := by
          rw [abs_of_pos hτ0]
          gcongr
          linarith

lemma one_add_div_pow_le_exp {c : ℝ} (hc : 0 ≤ c) {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ n) :
    (1 + c / n) ^ j ≤ Real.exp c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc (1 + c / n) ^ j ≤ Real.exp (c / n) ^ j :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (c / n)]) j
    _ = Real.exp (j * (c / n)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp c := by
        gcongr
        have : (j : ℝ) ≤ n := by exact_mod_cast hj
        calc (j : ℝ) * (c / n) ≤ n * (c / n) := by gcongr
          _ = c := by field_simp

/-- **Convergence of the splitting in `L²`** for a general smooth periodic divergence-free field,
with a constant depending only on the derivative bounds of the field. -/
theorem split_conv_core (Bd : ℕ → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → Pt 2 → Pt 2) (Lt : ℝ),
    SmoothField V Bd → (∀ s y, TraceFree (fderiv ℝ (V s) y)) →
    (∀ s x (m : Fin 2 → ℤ), V s (x + intVec m) = V s x) →
    (∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) →
    ∀ (ξ : Pt 2) (μ β : ℝ) (h : ℝ → Pt 2 → ℂ) (h₀ : Pt 2 → ℂ) (n : ℕ), 0 ≤ μ →
    IsParabolicC12 1 β h → (∀ s ∈ Icc (0 : ℝ) 1, IsQP ξ (h s)) →
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ y,
      dt 1 h s y + conv (V s) (h s) y = (μ / (4 * π ^ 2)) • lap (h s) y) →
    h 0 = h₀ → ContDiff ℝ 2 h₀ → IsQP ξ h₀ → 1 ≤ n →
    Real.sqrt (∫ y in cell 2, ‖splitOp μ n (fun i => gflow V ((i : ℝ) / n) (((i : ℝ) - 1) / n))
        n h₀ y - h 1 y‖ ^ 2) ≤ C * (μ / (4 * π ^ 2)) / n * h2Norm h₀ := by
  obtain ⟨C₁, hC₁, hstep⟩ := split_step_L2 Bd
  refine ⟨C₁ * Real.sqrt (Real.exp C₁), by positivity, ?_⟩
  intro V Lt hS hdiv hper hLt ξ μ β h h₀ n hμ hreg hqph heqh hh0 hh₀ hqp₀ hn
  set κ := μ / (4 * π ^ 2) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set ψ : ℕ → Pt 2 → Pt 2 := fun i => gflow V ((i : ℝ) / n) (((i : ℝ) - 1) / n) with hψ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set M₀ := ∫ y in cell 2, h2Dens h₀ y with hM₀
  have hM₀0 : 0 ≤ M₀ := setIntegral_nonneg measurableSet_Icc fun y _ => h2Dens_nonneg _ _
  set B := C₁ * κ * (1 / (n : ℝ)) ^ 2 * Real.sqrt (Real.exp C₁ * M₀) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the splitting iterates
  have key : ∀ j, j ≤ n → ContDiff ℝ 2 (splitOp μ n ψ j h₀) ∧ IsQP ξ (splitOp μ n ψ j h₀) ∧
      ∫ y in cell 2, h2Dens (splitOp μ n ψ j h₀) y ≤ (1 + C₁ / n) ^ j * M₀ ∧
      Real.sqrt (∫ y in cell 2, ‖splitOp μ n ψ j h₀ y - h ((j : ℝ) / n) y‖ ^ 2) ≤ j * B := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨hh₀, hqp₀, le_of_eq (by rw [pow_zero, one_mul]; rfl), ?_⟩
      simp only [splitOp, Nat.cast_zero, zero_div, zero_mul, hh0, sub_self, norm_zero]
      norm_num
    | succ j ih =>
      intro hj
      obtain ⟨hgC, hgq, hgM, hgE⟩ := ih (by omega)
      have hstepEq : splitOp μ n ψ (j + 1) h₀ =
          stepOut V κ ((j : ℝ) / n) (((j + 1 : ℕ) : ℝ) / n) (splitOp μ n ψ j h₀) := by
        rw [splitOp_succ]
        unfold stepOut
        have e1 : ψ (j + 1) = gflow V (((j + 1 : ℕ) : ℝ) / n) ((j : ℝ) / n) := by
          show gflow V (((j + 1 : ℕ) : ℝ) / n) ((((j + 1 : ℕ) : ℝ) - 1) / n) = _
          congr 1; push_cast; ring
        have e2 : splitVar μ n = Real.toNNReal (2 * κ * (((j + 1 : ℕ) : ℝ) / n - (j : ℝ) / n)) := by
          unfold splitVar
          congr 1
          rw [hκ]
          push_cast
          field_simp
          ring
        rw [e1, e2]
      have ht0 : (0 : ℝ) ≤ (j : ℝ) / n := by positivity
      have ht01 : (j : ℝ) / n < ((j + 1 : ℕ) : ℝ) / n := by
        gcongr; linarith
      have ht1 : ((j + 1 : ℕ) : ℝ) / n ≤ 1 := by
        rw [div_le_one hn0]; exact_mod_cast hj
      have hdt : ((j + 1 : ℕ) : ℝ) / n - (j : ℝ) / n = 1 / n := by
        push_cast; field_simp; ring
      obtain ⟨hE, hM⟩ := hstep V Lt hS hdiv hper hLt ξ κ β h hκ0 hreg hqph heqh _ _ _ hgC hgq
        ht0 ht01 ht1
      rw [hdt] at hE hM
      obtain ⟨hC', hq'⟩ := stepOut_regular hS hper hgC hgq κ ((j : ℝ) / n)
        (((j + 1 : ℕ) : ℝ) / n)
      rw [hstepEq]
      have hpow : (1 + C₁ / n) ^ j ≤ Real.exp C₁ :=
        one_add_div_pow_le_exp hC₁ hn (by omega)
      have hMj0 : 0 ≤ ∫ y in cell 2, h2Dens (splitOp μ n ψ j h₀) y :=
        setIntegral_nonneg measurableSet_Icc fun y _ => h2Dens_nonneg _ _
      refine ⟨hC', hq', ?_, ?_⟩
      · calc ∫ y in cell 2, h2Dens (stepOut V κ _ _ (splitOp μ n ψ j h₀)) y
            ≤ (1 + C₁ * (1 / n)) * ∫ y in cell 2, h2Dens (splitOp μ n ψ j h₀) y := hM
          _ ≤ (1 + C₁ * (1 / n)) * ((1 + C₁ / n) ^ j * M₀) := by gcongr
          _ = (1 + C₁ / n) ^ (j + 1) * M₀ := by rw [pow_succ]; ring
      · refine hE.trans ?_
        have hsq : Real.sqrt (∫ y in cell 2, h2Dens (splitOp μ n ψ j h₀) y) ≤
            Real.sqrt (Real.exp C₁ * M₀) := by
          gcongr
          exact hgM.trans (by gcongr)
        have : C₁ * κ * (1 / (n : ℝ)) ^ 2 *
            Real.sqrt (∫ y in cell 2, h2Dens (splitOp μ n ψ j h₀) y) ≤ B := by
          rw [hB]; gcongr
        push_cast
        nlinarith
  obtain ⟨-, -, -, hE⟩ := key n le_rfl
  rw [div_self hn0.ne'] at hE
  refine hE.trans (le_of_eq ?_)
  rw [hB, h2Norm_eq, ← hM₀, Real.sqrt_mul (Real.exp_pos _).le]
  field_simp

/-! ### The damped field -/

variable {L M : ℕ} {S : ℕ → ℝ}

/-- A time-Lipschitz constant for `B_{μ,ω}`, uniform in `μ ∈ [0,1]` and `ω`. -/
def dampedLt (cf : ControlFamily L M S) : ℝ := 2 * (coefDerivBound cf + 2 * coefBound cf)

lemma dampedB_time_lip (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (s s' : ℝ) (x : Pt 2) :
    ‖dampedB cf μ w s x - dampedB cf μ w s' x‖ ≤ dampedLt cf * |s - s'| := by
  have hc : ‖dampedCoef cf μ w s - dampedCoef cf μ w s'‖ ≤
      (coefDerivBound cf + 2 * coefBound cf) * ‖s - s'‖ := by
    refine convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hasDerivAt_dampedCoef cf μ w t).hasDerivWithinAt) (fun t _ => ?_)
      (mem_univ _) (mem_univ _)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1]
    have h1 := norm_deriv_coef_le cf w.1 t
    have h2 := norm_dampedCoef_le_gen cf hμ.1 w t
    have h3 := coefBound_nonneg cf
    have h4 : μ * ‖dampedCoef cf μ w t‖ ≤ 1 * ((1 + 1) * coefBound cf) := by
      refine mul_le_mul hμ.2 (h2.trans ?_) (norm_nonneg _) zero_le_one
      gcongr; exact hμ.2
    linarith
  rw [dampedB_eq, dampedB_eq]
  simp only
  rw [eField_sub_coef]
  refine (norm_eField_le _ _).trans ?_
  rw [Real.norm_eq_abs] at hc
  unfold dampedLt
  linarith

/-- **Lemma 3.10** (convergence of the splitting): `‖P_n h - T_{μ,ω}h‖₂ ≤ (Cκ/n)‖h‖_{H²}`
for periodic `h`, and the analogous estimate (with a constant depending on `ξ`) for the
quasi-periodic exponential `e_ξ` on a unit cell. -/
theorem split_convergence {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) :
    (∃ C : ℝ, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ w n ψ, 1 ≤ n → IsSplitting (dampedB cf μ w) n ψ →
      ∀ (h₀ : Pt 2 → ℂ) (h : ℝ → Pt 2 → ℂ), ContDiff ℝ 2 h₀ → IsPeriodic h₀ →
        IsClassicalScalar 1 (μ / (4 * π ^ 2)) (dampedB cf μ w) h₀ h →
        Real.sqrt (∫ y in cell 2, ‖splitOp μ n ψ n h₀ y - h 1 y‖ ^ 2) ≤
          C * (μ / (4 * π ^ 2)) / n * h2Norm h₀) ∧
    (∀ ξ : Pt 2, ∃ C : ℝ, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ w n ψ, 1 ≤ n →
      IsSplitting (dampedB cf μ w) n ψ → ∀ h : ℝ → Pt 2 → ℂ,
        IsCellSolution (dampedB cf μ w) μ ξ h →
        Real.sqrt (∫ y in cell 2, ‖splitOp μ n ψ n (expChar ξ) y - h 1 y‖ ^ 2) ≤
          C * (μ / (4 * π ^ 2)) / n) := by
  obtain ⟨C, -, hcore⟩ := split_conv_core (dampedBd cf 1)
  have hψeq : ∀ {μ : ℝ}, μ ∈ Icc (0 : ℝ) 1 → ∀ w n ψ, IsSplitting (dampedB cf μ w) n ψ →
      ∀ g : Pt 2 → ℂ, splitOp μ n ψ n g =
        splitOp μ n (fun i => gflow (dampedB cf μ w) ((i : ℝ) / n) (((i : ℝ) - 1) / n)) n g :=
    fun {μ} hμ w n ψ hψ g => splitOp_congr μ n g fun i h1 h2 => isSplitting_eq cf hμ.1 w hψ i h1 h2
  refine ⟨⟨C, fun μ hμ w n ψ hn hψ h₀ h hh₀ hp₀ hsol => ?_⟩, fun ξ => ⟨C * h2Norm (expChar ξ),
    fun μ hμ w n ψ hn hψ h hcell => ?_⟩⟩
  · obtain ⟨β, -, -, hreg⟩ := hsol.regular
    rw [hψeq hμ w n ψ hψ]
    exact hcore (dampedB cf μ w) (dampedLt cf) (dampedB_smooth_unif cf hμ w)
      (dampedB_traceFree cf hμ.1 w) (dampedB_periodic cf μ w) (dampedB_time_lip cf hμ w) 0 μ β h
      h₀ n hμ.1 hreg (fun s hs => isQP_zero_iff.2 (hsol.periodic s hs)) hsol.eqn hsol.init hh₀
      (isQP_zero_iff.2 hp₀) hn
  · obtain ⟨β, -, -, hreg⟩ := hcell.regular
    rw [hψeq hμ w n ψ hψ]
    have := hcore (dampedB cf μ w) (dampedLt cf) (dampedB_smooth_unif cf hμ w)
      (dampedB_traceFree cf hμ.1 w) (dampedB_periodic cf μ w) (dampedB_time_lip cf hμ w) ξ μ β h
      (expChar ξ) n hμ.1 hreg (fun s hs y m => hcell.quasi_periodic s hs y m) hcell.eqn
      hcell.init ((contDiff_expChar ξ).of_le (by exact_mod_cast natCast_le_inf 2))
      (fun y m => by rw [expChar_add_right, mul_comm]) hn
    refine this.trans (le_of_eq ?_)
    ring

end AnomDiss
