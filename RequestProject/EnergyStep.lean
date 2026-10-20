module

public import RequestProject.QPBasic

/-!
# An `L²` energy estimate for a forced advection–diffusion equation on the torus

If `e` is quasi-periodic, `C²` in space, and `∂ₜe = -B·∇e + κΔe + R` with a periodic
divergence-free drift `B` and `κ ≥ 0`, then `‖e(b)‖₂ ≤ ‖e(a)‖₂ + ρ (b - a)` whenever
`‖R(t)‖₂ ≤ ρ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal InnerProductSpace

noncomputable section

namespace AnomDiss

variable {ξ : Pt 2}

lemma integrableOn_cell_of_continuous' {E : Type*} [NormedAddCommGroup E] {F : Pt 2 → E}
    (hF : Continuous F) : IntegrableOn F (cell 2) :=
  hF.continuousOn.integrableOn_compact isCompact_Icc

lemma pd_norm_sq {e : Pt 2 → ℂ} (he : Differentiable ℝ e) (j : Fin 2) (x : Pt 2) :
    pd j (fun y => ‖e y‖ ^ 2) x = 2 * ⟪e x, pd j e x⟫_ℝ := by
  unfold pd
  rw [((he x).hasFDerivAt.norm_sq).fderiv]
  simp
  ring

lemma pd_inner {e f : Pt 2 → ℂ} (he : Differentiable ℝ e) (hf : Differentiable ℝ f) (j : Fin 2)
    (x : Pt 2) :
    pd j (fun y => ⟪e y, f y⟫_ℝ) x = ⟪pd j e x, f x⟫_ℝ + ⟪e x, pd j f x⟫_ℝ := by
  unfold pd
  rw [((he x).hasFDerivAt.inner ℝ (hf x).hasFDerivAt).fderiv]
  simp [fderivInnerCLM_apply]
  ring

lemma contDiff_pd_one {e : Pt 2 → ℂ} (he : ContDiff ℝ 2 e) (i : Fin 2) : ContDiff ℝ 1 (pd i e) :=
  contDiff_pd_of_C2 e he i

/-- The transport term does not change the energy. -/
lemma integral_inner_conv {Bv : Pt 2 → Pt 2} (hB : ContDiff ℝ 1 Bv) (hBp : IsPeriodic Bv)
    (hdiv : ∀ x, divergence Bv x = 0) {e : Pt 2 → ℂ} (he : ContDiff ℝ 1 e) (hqp : IsQP ξ e) :
    ∫ x in cell 2, ⟪e x, conv Bv e x⟫_ℝ = 0 := by
  have hd : Differentiable ℝ e := he.differentiable one_ne_zero
  set P : Pt 2 → ℝ := fun y => ‖e y‖ ^ 2 with hP
  have hPc : ContDiff ℝ 1 P := (contDiff_norm_sq ℝ).comp he
  have hPp : IsPeriodic P := hqp.periodic_norm_sq
  have hBj : ∀ j : Fin 2, ContDiff ℝ 1 (fun y => Bv y j) := fun j =>
    (contDiff_apply ℝ ℝ j).comp hB
  have hBjp : ∀ j : Fin 2, IsPeriodic (fun y => Bv y j) := fun j x n => by simp [hBp x n]
  have hpt : ∀ x, ⟪e x, conv Bv e x⟫_ℝ = ∑ j, Bv x j * (pd j P x / 2) := fun x => by
    unfold conv
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, hP, pd_norm_sq hd]
    ring
  simp only [hpt]
  have hcont : ∀ j : Fin 2, Continuous fun x => Bv x j * (pd j P x / 2) := fun j =>
    (hBj j).continuous.mul ((continuous_pd_of_C1 P hPc j).div_const 2)
  rw [integral_finset_sum _ fun j _ => integrableOn_cell_of_continuous (hcont j)]
  have hj : ∀ j : Fin 2, ∫ x in cell 2, Bv x j * (pd j P x / 2) =
      -(∫ x in cell 2, pd j (fun y => Bv y j) x * P x) / 2 := fun j => by
    have := integral_mul_pd (fun y => Bv y j) P (hBj j) hPc (hBjp j) hPp j
    rw [← this, ← integral_div]
    congr 1; funext x; ring
  simp only [hj]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  have hsum : ∑ j : Fin 2, ∫ x in cell 2, pd j (fun y => Bv y j) x * P x =
      ∫ x in cell 2, ∑ j : Fin 2, pd j (fun y => Bv y j) x * P x :=
    (integral_finset_sum _ fun j _ =>
      integrableOn_cell_of_continuous ((continuous_pd_of_C1 _ (hBj j) j).mul hPc.continuous)).symm
  rw [hsum]
  have h0 : ∀ x, ∑ j : Fin 2, pd j (fun y => Bv y j) x * P x = 0 := fun x => by
    rw [← Finset.sum_mul]
    have := hdiv x
    unfold divergence at this
    simp only [← pd_component Bv x (hB.differentiable one_ne_zero x)] at this
    rw [this, zero_mul]
  simp [h0]

/-- The diffusion term dissipates energy. -/
lemma integral_inner_lap_nonpos {e : Pt 2 → ℂ} (he : ContDiff ℝ 2 e) (hqp : IsQP ξ e) :
    ∫ x in cell 2, ⟪e x, lap e x⟫_ℝ ≤ 0 := by
  have h1 : ContDiff ℝ 1 e := he.of_le (by norm_num)
  have hd : Differentiable ℝ e := h1.differentiable one_ne_zero
  have hpd : ∀ i, ContDiff ℝ 1 (pd i e) := fun i => contDiff_pd_one he i
  have hpdd : ∀ i, Differentiable ℝ (pd i e) := fun i => (hpd i).differentiable one_ne_zero
  have hpt : ∀ x, ⟪e x, lap e x⟫_ℝ =
      ∑ i, (pd i (fun y => ⟪e y, pd i e y⟫_ℝ) x - ‖pd i e x‖ ^ 2) := fun x => by
    unfold lap
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_inner hd (hpdd i), real_inner_self_eq_norm_sq]
    ring
  simp only [hpt]
  have hQ : ∀ i, ContDiff ℝ 1 (fun y => ⟪e y, pd i e y⟫_ℝ) := fun i => h1.inner ℝ (hpd i)
  have hc : ∀ i : Fin 2, Continuous fun x =>
      pd i (fun y => ⟪e y, pd i e y⟫_ℝ) x - ‖pd i e x‖ ^ 2 := fun i =>
    (continuous_pd_of_C1 _ (hQ i) i).sub ((hpd i).continuous.norm.pow 2)
  rw [integral_finset_sum _ fun i _ => integrableOn_cell_of_continuous (hc i)]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [integral_sub (f := fun x => pd i (fun y => ⟪e y, pd i e y⟫_ℝ) x)
    (g := fun x => ‖pd i e x‖ ^ 2)
    (integrableOn_cell_of_continuous (continuous_pd_of_C1 _ (hQ i) i))
    (integrableOn_cell_of_continuous ((hpd i).continuous.norm.pow 2)),
    integral_pd_periodic _ (hQ i) (hqp.periodic_inner (hqp.pd hd i)) i, zero_sub, neg_nonpos]
  exact setIntegral_nonneg measurableSet_Icc fun x _ => by positivity

/-- Energy production by the equation `∂ₜe = -B·∇e + κΔe + R`. -/
lemma integral_inner_rhs_le {Bv : Pt 2 → Pt 2} (hB : ContDiff ℝ 1 Bv) (hBp : IsPeriodic Bv)
    (hdiv : ∀ x, divergence Bv x = 0) {κ : ℝ} (hκ : 0 ≤ κ) {e R : Pt 2 → ℂ}
    (he : ContDiff ℝ 2 e) (hqp : IsQP ξ e) (hR : Continuous R) :
    ∫ x in cell 2, ⟪e x, -conv Bv e x + κ • lap e x + R x⟫_ℝ ≤
      Real.sqrt (∫ x in cell 2, ‖e x‖ ^ 2) * Real.sqrt (∫ x in cell 2, ‖R x‖ ^ 2) := by
  have h1 : ContDiff ℝ 1 e := he.of_le (by norm_num)
  have hd : Differentiable ℝ e := h1.differentiable one_ne_zero
  have hcc : Continuous (conv Bv e) := by
    unfold conv
    exact continuous_finset_sum _ fun j _ => ((continuous_apply j).comp hB.continuous).smul
      (continuous_pd_of_C1 e h1 j)
  have hcl : Continuous (lap e) := by
    unfold lap
    exact continuous_finset_sum _ fun i _ => continuous_pd_of_C1 _ (contDiff_pd_one he i) i
  have hpt : ∀ x, ⟪e x, -conv Bv e x + κ • lap e x + R x⟫_ℝ =
      -⟪e x, conv Bv e x⟫_ℝ + κ * ⟪e x, lap e x⟫_ℝ + ⟪e x, R x⟫_ℝ := fun x => by
    rw [inner_add_right, inner_add_right, inner_neg_right, real_inner_smul_right]
  simp only [hpt]
  have i1 := integrableOn_cell_of_continuous (hd.continuous.inner hcc)
  have i2 := integrableOn_cell_of_continuous (hd.continuous.inner hcl)
  have i3 := integrableOn_cell_of_continuous (hd.continuous.inner hR)
  rw [integral_add (f := fun x => -⟪e x, conv Bv e x⟫_ℝ + κ * ⟪e x, lap e x⟫_ℝ)
    (g := fun x => ⟪e x, R x⟫_ℝ) (i1.neg.add (i2.const_mul κ)) i3,
    integral_add (f := fun x => -⟪e x, conv Bv e x⟫_ℝ) (g := fun x => κ * ⟪e x, lap e x⟫_ℝ)
      i1.neg (i2.const_mul κ),
    integral_neg, integral_const_mul, integral_inner_conv hB hBp hdiv h1 hqp, neg_zero, zero_add]
  have hlap := integral_inner_lap_nonpos he hqp
  have hκl : κ * ∫ x in cell 2, ⟪e x, lap e x⟫_ℝ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ hlap
  -- Cauchy–Schwarz
  have hCS : ∫ x in cell 2, ⟪e x, R x⟫_ℝ ≤
      Real.sqrt (∫ x in cell 2, ‖e x‖ ^ 2) * Real.sqrt (∫ x in cell 2, ‖R x‖ ^ 2) := by
    have hle : ∫ x in cell 2, ⟪e x, R x⟫_ℝ ≤ ∫ x in cell 2, ‖e x‖ * ‖R x‖ :=
      setIntegral_mono_on i3 (integrableOn_cell_of_continuous
        (hd.continuous.norm.mul hR.norm)) measurableSet_Icc fun x _ => real_inner_le_norm _ _
    refine hle.trans ?_
    have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (cell 2))
      Real.HolderConjugate.two_two (f := fun x => ‖e x‖) (g := fun x => ‖R x‖)
      (Eventually.of_forall fun x => norm_nonneg _) (Eventually.of_forall fun x => norm_nonneg _)
      ?_ ?_
    · simp only [Real.rpow_two] at this
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      convert this using 3
    · rw [show ENNReal.ofReal 2 = 2 by simp]
      refine (memLp_two_iff_integrable_sq ?_).2 ?_
      · exact hd.continuous.norm.aestronglyMeasurable
      · exact integrableOn_cell_of_continuous (hd.continuous.norm.pow 2)
    · rw [show ENNReal.ofReal 2 = 2 by simp]
      refine (memLp_two_iff_integrable_sq ?_).2 ?_
      · exact hR.norm.aestronglyMeasurable
      · exact integrableOn_cell_of_continuous (hR.norm.pow 2)
  linarith

lemma volume_cell_ne_top : (volume : Measure (Pt 2)) (cell 2) ≠ ⊤ :=
  (isCompact_Icc (a := (0 : Pt 2)) (b := 1)).measure_lt_top.ne

lemma integrable_const_cell (c : ℝ) : Integrable (fun _ : Pt 2 => c) (volume.restrict (cell 2)) :=
  integrableOn_const volume_cell_ne_top

/-- **Energy estimate** on a time interval. -/
theorem energy_step_L2 {a b κ ρ : ℝ} (hab : a ≤ b) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    {B : ℝ → Pt 2 → Pt 2} (hB : ∀ t, ContDiff ℝ 1 (B t)) (hBp : ∀ t, IsPeriodic (B t))
    (hdiv : ∀ t x, divergence (B t) x = 0) {e e' R : ℝ → Pt 2 → ℂ}
    (hec : ∀ t ∈ Icc a b, Continuous (e t))
    (hC2 : ∀ t ∈ Ioo a b, ContDiff ℝ 2 (e t)) (hqp : ∀ t ∈ Ioo a b, IsQP ξ (e t))
    (hcont : ∀ x, ContinuousOn (fun t => e t x) (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => e s x) (e' t x) t)
    (hbd : ∃ C, ∀ t ∈ Icc a b, ∀ x, ‖e t x‖ ≤ C) (hbd' : ∃ C, ∀ t ∈ Ioo a b, ∀ x, ‖e' t x‖ ≤ C)
    (heq : ∀ t ∈ Ioo a b, ∀ x, e' t x = -conv (B t) (e t) x + κ • lap (e t) x + R t x)
    (hRc : ∀ t ∈ Ioo a b, Continuous (R t))
    (hR : ∀ t ∈ Ioo a b, Real.sqrt (∫ x in cell 2, ‖R t x‖ ^ 2) ≤ ρ) :
    Real.sqrt (∫ x in cell 2, ‖e b x‖ ^ 2) ≤
      Real.sqrt (∫ x in cell 2, ‖e a x‖ ^ 2) + ρ * (b - a) := by
  obtain ⟨C, hC⟩ := hbd
  obtain ⟨C', hC'⟩ := hbd'
  set N : ℝ → ℝ := fun t => ∫ x in cell 2, ‖e t x‖ ^ 2 with hN
  have hN0 : ∀ t, 0 ≤ N t := fun t => setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
  -- continuity of the energy
  have hNc : ContinuousOn N (Icc a b) := by
    refine continuousOn_of_dominated (bound := fun _ => C ^ 2) (fun t ht => ?_) (fun t ht => ?_)
      (integrable_const_cell _) (Eventually.of_forall fun x => ?_)
    · exact ((hec t ht).norm.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC t ht x) 2
    · exact ((hcont x).norm).pow 2
  -- derivative of the energy
  have hNd : ∀ t ∈ Ioo a b, HasDerivAt N (∫ x in cell 2, 2 * ⟪e t x, e' t x⟫_ℝ) t := by
    intro t ht
    have hnhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    have he'c : Continuous (e' t) := by
      have h1 : ContDiff ℝ 1 (e t) := (hC2 t ht).of_le (by norm_num)
      have hcc : Continuous (conv (B t) (e t)) := by
        unfold conv
        exact continuous_finset_sum _ fun j _ => ((continuous_apply j).comp (hB t).continuous).smul
          (continuous_pd_of_C1 _ h1 j)
      have hcl : Continuous (lap (e t)) := by
        unfold lap
        exact continuous_finset_sum _ fun i _ =>
          continuous_pd_of_C1 _ (contDiff_pd_one (hC2 t ht) i) i
      have : e' t = fun x => -conv (B t) (e t) x + κ • lap (e t) x + R t x := funext (heq t ht)
      rw [this]
      exact (hcc.neg.add (hcl.const_smul κ)).add (hRc t ht)
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (cell 2))
      (F := fun s x => ‖e s x‖ ^ 2) (F' := fun s x => 2 * ⟪e s x, e' s x⟫_ℝ)
      (bound := fun _ => 2 * (C * C')) (x₀ := t) hnhds
      (Filter.eventually_of_mem hnhds fun s hs =>
        ((hec s (Ioo_subset_Icc_self hs)).norm.pow 2).aestronglyMeasurable)
      ?_ ?_ ?_ (integrable_const_cell _) ?_
    · exact this.2
    · exact integrableOn_cell_of_continuous ((hec t (Ioo_subset_Icc_self ht)).norm.pow 2)
    · exact (continuous_const.mul ((hec t (Ioo_subset_Icc_self ht)).inner he'c)).aestronglyMeasurable
    · refine Eventually.of_forall fun x s hs => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_two, Real.norm_eq_abs]
      have h1 := abs_real_inner_le_norm (e s x) (e' s x)
      have h2 := hC s (Ioo_subset_Icc_self hs) x
      have h3 := hC' s hs x
      have := h1.trans (mul_le_mul h2 h3 (norm_nonneg _) ((norm_nonneg _).trans h2))
      linarith
    · exact Eventually.of_forall fun x s hs => (hderiv s hs x).norm_sq
  -- the derivative bound
  have hMle : ∀ t ∈ Ioo a b,
      ∫ x in cell 2, 2 * ⟪e t x, e' t x⟫_ℝ ≤ 2 * (Real.sqrt (N t) * ρ) := by
    intro t ht
    rw [integral_const_mul]
    have e1 : (fun x => ⟪e t x, e' t x⟫_ℝ) =
        fun x => ⟪e t x, -conv (B t) (e t) x + κ • lap (e t) x + R t x⟫_ℝ :=
      funext fun x => by rw [heq t ht x]
    rw [e1]
    have h := integral_inner_rhs_le (hB t) (hBp t) (hdiv t) hκ (hC2 t ht) (hqp t ht) (hRc t ht)
    have h2 := mul_le_mul_of_nonneg_left (hR t ht) (Real.sqrt_nonneg (N t))
    linarith
  -- comparison argument
  have key : ∀ ε > 0, Real.sqrt (N b + ε ^ 2) ≤ Real.sqrt (N a + ε ^ 2) + ρ * (b - a) := by
    intro ε hε
    set G : ℝ → ℝ := fun t => Real.sqrt (N t + ε ^ 2) - ρ * t with hG
    have hpos : ∀ t, 0 < N t + ε ^ 2 := fun t => by have := hN0 t; positivity
    have hGd : ∀ t ∈ Ioo a b, HasDerivAt G
        ((∫ x in cell 2, 2 * ⟪e t x, e' t x⟫_ℝ) / (2 * Real.sqrt (N t + ε ^ 2)) - ρ) t :=
      fun t ht => by
        have := (((hNd t ht).add_const (ε ^ 2)).sqrt (hpos t).ne').fun_sub
          ((hasDerivAt_id t).const_mul ρ)
        simpa using this
    have hanti : AntitoneOn G (Icc a b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
      · exact ((hNc.add continuousOn_const).sqrt).sub (continuousOn_const.mul continuousOn_id)
      · rw [interior_Icc]
        exact fun t ht => (hGd t ht).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hGd t ht).deriv]
        have h1 := hMle t ht
        have h2 : Real.sqrt (N t) ≤ Real.sqrt (N t + ε ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
        have h3 : 0 < Real.sqrt (N t + ε ^ 2) := Real.sqrt_pos.2 (hpos t)
        rw [sub_nonpos, div_le_iff₀ (by positivity)]
        nlinarith
    have := hanti ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
    simp only [hG] at this
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := key ε hε
  have h2 : Real.sqrt (N b) ≤ Real.sqrt (N b + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h3 : Real.sqrt (N a + ε ^ 2) ≤ Real.sqrt (N a) + ε := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := Real.sq_sqrt (hN0 a)
    nlinarith [Real.sqrt_nonneg (N a)]
  linarith

end AnomDiss
