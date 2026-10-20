module

public import RequestProject.TorusCalc

/-!
# Lemma 1.7: the scalar energy identity and the maximum principle

Joint continuity of parabolic Hölder functions, the energy identity
`½‖θ(t)‖₂² + ν∫₀ᵗ‖∇θ‖₂² = ½‖θ₀‖₂²` for classical solutions of the advection–diffusion equation
with a periodic divergence-free `C¹` drift, and the maximum principle.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Functions in `C^{1+β/2,2+β}` are Lipschitz in time, uniformly in space. -/
lemma IsParabolicC12.time_lipschitz {T β : ℝ} {u : ℝ → Pt d → E} (hu : IsParabolicC12 T β u) :
    ∃ C, ∀ x, ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ‖u t x - u s x‖ ≤ C * |t - s| := by
  obtain ⟨C, hC⟩ := hu.bdd_dt
  refine ⟨C, fun x t ht s hs => ?_⟩
  have := (convex_Icc (0:ℝ) T).norm_image_sub_le_of_norm_derivWithin_le
    (f := fun r => u r x) (C := C) (fun r hr => (hu.diff_t x r hr)) (fun r hr => hC r hr x) hs ht
  simpa [Real.norm_eq_abs] using this

/-- Functions in `C^{1+β/2,2+β}` are jointly continuous on `[0,T] × ℝ^d`. -/
lemma IsParabolicC12.continuousOn {T β : ℝ} {u : ℝ → Pt d → E} (hu : IsParabolicC12 T β u) :
    ContinuousOn (fun p : ℝ × Pt d => u p.1 p.2) (Icc 0 T ×ˢ univ) := by
  obtain ⟨C, hC⟩ := hu.time_lipschitz
  rintro ⟨s, y⟩ ⟨hs, -⟩
  have hcy : ContinuousAt (u s) y :=
    ((hu.smooth_x s hs).continuous).continuousAt
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun p : ℝ × Pt d => |C| * |p.1 - s| + ‖u s p.2 - u s y‖)
      (𝓝[Icc 0 T ×ˢ univ] (s, y)) (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ × Pt d => |C| * |p.1 - s|) (𝓝 (s, y)) (𝓝 0) := by
      have : Continuous (fun p : ℝ × Pt d => |C| * |p.1 - s|) := by fun_prop
      simpa using this.tendsto (s, y)
    have h2 : Tendsto (fun p : ℝ × Pt d => ‖u s p.2 - u s y‖) (𝓝 (s, y)) (𝓝 0) := by
      have := (hcy.tendsto.comp (continuous_snd.tendsto (s, y)))
      rw [tendsto_iff_norm_sub_tendsto_zero] at this
      exact this
    simpa using (h1.add h2).mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with p hp
  calc ‖u p.1 p.2 - u s y‖ = ‖(u p.1 p.2 - u s p.2) + (u s p.2 - u s y)‖ := by abel_nf
    _ ≤ ‖u p.1 p.2 - u s p.2‖ + ‖u s p.2 - u s y‖ := norm_add_le _ _
    _ ≤ |C| * |p.1 - s| + ‖u s p.2 - u s y‖ := by
        gcongr
        exact (hC p.2 p.1 hp.1 s hs).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))

omit [NormedSpace ℝ E] in
/-- Parabolically Hölder functions are jointly continuous on `[0,T] × ℝ^d`. -/
lemma ParHolder.continuousOn {T β : ℝ} (hβ : 0 < β) {g : ℝ → Pt d → E} (hg : ParHolder T β g) :
    ContinuousOn (fun p : ℝ × Pt d => g p.1 p.2) (Icc 0 T ×ˢ univ) := by
  obtain ⟨C, hC⟩ := hg
  rintro ⟨s, y⟩ ⟨hs, -⟩
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun p : ℝ × Pt d => C * (‖p.2 - y‖ ^ β + |p.1 - s| ^ (β / 2)))
      (𝓝[Icc 0 T ×ˢ univ] (s, y)) (𝓝 0) := by
    have hc : Continuous (fun p : ℝ × Pt d => C * (‖p.2 - y‖ ^ β + |p.1 - s| ^ (β / 2))) := by
      refine continuous_const.mul (((Real.continuous_rpow_const hβ.le).comp (by fun_prop)).add
        ((Real.continuous_rpow_const (by positivity)).comp (by fun_prop)))
    have := hc.tendsto (s, y)
    simp only [sub_self, norm_zero, abs_zero] at this
    rw [Real.zero_rpow hβ.ne', Real.zero_rpow (by positivity), add_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact hC p.1 hp.1 s hs p.2 y

lemma continuous_lap_of_C2 (h : Pt 2 → ℝ) (hh : ContDiff ℝ 2 h) : Continuous (lap h) := by
  unfold lap
  exact continuous_finset_sum _ fun i _ => continuous_pd_of_C1 _ (contDiff_pd_of_C2 h hh i) i

lemma continuous_conv_of_C1 (u : Pt 2 → Pt 2) (hu : Continuous u) (h : Pt 2 → ℝ)
    (hh : ContDiff ℝ 1 h) : Continuous (conv u h) := by
  unfold conv
  exact continuous_finset_sum _ fun j _ =>
    ((continuous_apply j).comp hu).smul (continuous_pd_of_C1 h hh j)

/-- Spatial part of the energy identity: `∫ θ (νΔθ - v·∇θ) = -ν ∫ |∇θ|²`. -/
lemma integral_energy_rhs (ν : ℝ) (u : Pt 2 → Pt 2) (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u)
    (hdiv : ∀ x, divergence u x = 0) (θ : Pt 2 → ℝ) (hθ : ContDiff ℝ 2 θ) (hp : IsPeriodic θ) :
    ∫ x in cell 2, 2 * θ x * (ν * lap θ x - conv u θ x) =
      -(2 * ν) * ∫ x in cell 2, gradSq θ x := by
  have h1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have e : ∀ x, 2 * θ x * (ν * lap θ x - conv u θ x) =
      (2 * ν) * (θ x * lap θ x) - 2 * (θ x * conv u θ x) := fun x => by ring
  simp only [e]
  rw [integral_sub (f := fun x => 2 * ν * (θ x * lap θ x)) (g := fun x => 2 * (θ x * conv u θ x))
    (integrableOn_cell_of_continuous (continuous_const.mul
      (h1.continuous.mul (continuous_lap_of_C2 θ hθ))))
    (integrableOn_cell_of_continuous (continuous_const.mul
      (h1.continuous.mul (continuous_conv_of_C1 u hu.continuous θ h1)))),
    integral_const_mul, integral_const_mul, integral_mul_lap θ hθ hp,
    integral_mul_conv u hu hup hdiv θ h1 hp]
  ring

/-- The scalar energy identity for classical solutions with a `C¹` periodic divergence-free
drift. -/
lemma energy_identity_core (T ν : ℝ) (v : ℝ → Pt 2 → Pt 2)
    (hvper : ∀ t ∈ Icc 0 T, IsPeriodic (v t)) (hvC1 : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (v t))
    (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℝ) (θ : ℝ → Pt 2 → ℝ) (hθ : IsClassicalScalar T ν v θ₀ θ)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    l2sq (θ t) / 2 + dissipation ν θ t = l2sq θ₀ / 2 := by
  obtain ⟨β, hβ0, -, reg⟩ := hθ.regular
  set F : ℝ → Pt 2 → ℝ := fun s x => 2 * θ s x * dt T θ s x with hF
  have hθc := reg.continuousOn
  have hdc := reg.holder_dt.continuousOn hβ0
  have hFc : ContinuousOn (fun p : ℝ × Pt 2 => F p.1 p.2) (Icc 0 T ×ˢ univ) :=
    (continuousOn_const.mul hθc).mul hdc
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hline : ∀ x, ∀ {G : ℝ → Pt 2 → ℝ},
      ContinuousOn (fun p : ℝ × Pt 2 => G p.1 p.2) (Icc 0 T ×ˢ univ) →
      ContinuousOn (fun s => G s x) (Icc 0 t) := fun x G hG =>
    hG.comp (Continuous.prodMk continuous_id continuous_const).continuousOn (fun s hs => ⟨hsub hs, mem_univ _⟩)
  -- Step 1: fundamental theorem of calculus at each point
  have step1 : ∀ x, θ t x ^ 2 - θ 0 x ^ 2 = ∫ s in (0:ℝ)..t, F s x := by
    intro x
    symm
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      ((hline x hθc).pow 2) (fun s hs => ?_) ?_
    · have hsT : s ∈ Icc 0 T := hsub (Ioo_subset_Icc_self hs)
      have hd : HasDerivAt (fun r => θ r x) (dt T θ s x) s :=
        (reg.diff_t x s hsT).hasDerivWithinAt.hasDerivAt
          (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
      have := hd.fun_mul hd
      refine HasDerivAt.hasDerivWithinAt ?_
      convert this using 1
      · funext r; simp only [Pi.mul_apply, Pi.pow_apply]; ring
      · simp only [hF]; ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1]
      exact hline x hFc
  -- Step 2: integrate over the cell
  have hθt : Continuous (θ t) := (reg.smooth_x t ht).continuous
  have hθ0 : Continuous (θ 0) := (reg.smooth_x 0 ⟨le_rfl, ht.1.trans ht.2⟩).continuous
  have step2 : l2sq (θ t) - l2sq θ₀ = ∫ x in cell 2, ∫ s in (0:ℝ)..t, F s x := by
    rw [← hθ.init, l2sq, l2sq, ← integral_sub (f := fun x => θ t x ^ 2)
      (g := fun x => θ 0 x ^ 2) (integrableOn_cell_of_continuous (hθt.pow 2))
      (integrableOn_cell_of_continuous (hθ0.pow 2))]
    exact setIntegral_congr_fun measurableSet_Icc fun x _ => step1 x
  -- Step 3: Fubini
  have step3 : ∫ x in cell 2, ∫ s in (0:ℝ)..t, F s x = ∫ s in (0:ℝ)..t, ∫ x in cell 2, F s x := by
    simp only [intervalIntegral.integral_of_le ht.1]
    refine integral_integral_swap ?_
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : ContinuousOn (fun q : Pt 2 × ℝ => F q.2 q.1) (cell 2 ×ˢ Icc 0 t) :=
      hFc.comp continuous_swap.continuousOn (fun q hq => ⟨hsub hq.2, mem_univ _⟩)
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono subset_rfl Ioc_subset_Icc_self)
  -- Step 4: the spatial identity at each time
  have step4 : ∀ s ∈ uIcc 0 t, ∫ x in cell 2, F s x =
      -(2 * ν) * ∫ x in cell 2, gradSq (θ s) x := by
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsT := hsub hs
    rw [← integral_energy_rhs ν (v s) (hvC1 s hsT) (hvper s hsT) (hvdiv s hsT) (θ s)
      (reg.smooth_x s hsT) (hθ.periodic s hsT)]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    have := hθ.eqn s hsT x
    simp only [hF, smul_eq_mul] at this ⊢
    congr 1
    linarith
  rw [step3, intervalIntegral.integral_congr step4, intervalIntegral.integral_const_mul] at step2
  unfold dissipation
  linarith

/-! ### The maximum principle -/

section maxp
variable {d : ℕ}

/-- At a left-sided maximum, the left derivative is nonnegative. -/
lemma deriv_nonneg_of_left_max {φ : ℝ → ℝ} {D T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    (hd : HasDerivWithinAt φ D (Icc 0 T) s) (hmax : ∀ r ∈ Icc 0 s, φ r ≤ φ s) : 0 ≤ D := by
  have h1 : HasDerivWithinAt φ D (Icc 0 s) s := hd.mono (Icc_subset_Icc_right hsT)
  have h2 : HasDerivWithinAt φ D (Iic s) s :=
    h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hs)
  have h3 : HasDerivWithinAt φ D (Iio s) s := h2.Iio_of_Iic
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 h3
  rw [show Iio s \ {s} = Iio s from diff_singleton_eq_self (lt_irrefl s)] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hs] with r hr
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (by linarith [hmax r ⟨hr.1.le, hr.2.le⟩]) (by linarith [hr.2])

/-- At a global maximum, partial derivatives vanish. -/
lemma pd_eq_zero_of_max (h : Pt d → ℝ) (hh : Differentiable ℝ h) (x : Pt d)
    (hmax : ∀ y, h y ≤ h x) (i : Fin d) : pd i h x = 0 := by
  have hl : IsLocalMax (fun r : ℝ => h (x + r • eb i)) 0 :=
    Eventually.of_forall fun r => by simpa using hmax (x + r • eb i)
  have := (hasDerivAt_line h x i 0 (hh _)).deriv
  simp only [zero_smul, add_zero] at this
  rw [← this]
  exact hl.deriv_eq_zero

/-- At a global maximum of a `C²` function, the pure second derivatives are nonpositive. -/
lemma pd_pd_nonpos_of_max (h : Pt d → ℝ) (hh : ContDiff ℝ 2 h) (x : Pt d)
    (hmax : ∀ y, h y ≤ h x) (i : Fin d) : pd i (pd i h) x ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  set g : ℝ → ℝ := fun r => h (x + r • eb i)
  set g' : ℝ → ℝ := fun r => pd i h (x + r • eb i)
  have hg : ∀ r, HasDerivAt g (g' r) r := fun r =>
    hasDerivAt_line h x i r (hh.differentiable (by norm_num) _)
  have hg' : HasDerivAt g' (pd i (pd i h) x) 0 := by
    have := hasDerivAt_line (pd i h) x i 0 ((contDiff_pd_of_C2 h hh i).differentiable one_ne_zero _)
    simpa using this
  have hg'0 : g' 0 = 0 := by
    simp only [g', zero_smul, add_zero]
    exact pd_eq_zero_of_max h (hh.differentiable (by norm_num)) x hmax i
  have hev : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r⁻¹ • (g' (0 + r) - g' 0) :=
    hg'.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos)
  obtain ⟨δ, hδ, hδs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  have hpos' : ∀ r ∈ Ioo 0 δ, 0 < g' r := by
    intro r hr
    have := hδs hr
    simp only [mem_setOf_eq, zero_add, hg'0, sub_zero, smul_eq_mul] at this
    exact pos_of_mul_pos_right this (inv_pos.2 hr.1).le
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' (half_pos hδ)
    (fun r _ => (hg r).continuousAt.continuousWithinAt) (fun r _ => hg r)
  have h1 : 0 < g' c := hpos' c ⟨hc.1, hc.2.trans (half_lt_self hδ)⟩
  rw [hcs] at h1
  have h2 : g (δ / 2) ≤ g 0 := by simpa [g] using hmax (x + (δ / 2) • eb i)
  have : 0 < g (δ / 2) - g 0 := by
    have := div_pos_iff.1 h1
    rcases this with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith [show (0:ℝ) < δ from hδ]
  linarith

/-- The weak maximum principle for `∂ₜu + v·∇u = νΔu` (upper bound). -/
lemma max_principle_upper (T ν : ℝ) (hν : 0 ≤ ν) (v : ℝ → Pt 2 → Pt 2) (u : ℝ → Pt 2 → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2) (Icc 0 T ×ˢ univ))
    (hper : ∀ t ∈ Icc 0 T, IsPeriodic (u t))
    (hC2 : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (u t))
    (hdiff : ∀ x, ∀ t ∈ Icc 0 T, DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (heq : ∀ t ∈ Icc 0 T, ∀ x, dt T u t x + conv (v t) (u t) x = ν • lap (u t) x)
    (M : ℝ) (h0 : ∀ x, u 0 x ≤ M) : ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ M := by
  intro t1 ht1 x1
  suffices H : ∀ ε > 0, u t1 x1 ≤ M + ε * t1 by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := H (ε / (t1 + 1)) (by have := ht1.1; positivity)
    have h2 : ε / (t1 + 1) * t1 < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith [ht1.1])]
      nlinarith [ht1.1]
    linarith
  intro ε hε
  have hKsub : Icc 0 t1 ×ˢ cell 2 ⊆ Icc 0 T ×ˢ univ := fun p hp =>
    ⟨Icc_subset_Icc_right ht1.2 hp.1, mem_univ _⟩
  have hwc : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2 - ε * p.1) (Icc 0 t1 ×ˢ cell 2) :=
    (hcont.mono hKsub).sub (by fun_prop)
  have hne : (Icc 0 t1 ×ˢ cell 2).Nonempty :=
    ⟨(0, 0), ⟨le_rfl, ht1.1⟩, ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨⟨s, y⟩, hK, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn hne hwc
  have hall : ∀ r ∈ Icc 0 t1, ∀ z, u r z - ε * r ≤ u s y - ε * s := by
    intro r hr z
    obtain ⟨z', hz', n, rfl⟩ := exists_cell_rep z
    rw [hper r (Icc_subset_Icc_right ht1.2 hr) z' n]
    exact hmax (show (r, z') ∈ Icc 0 t1 ×ˢ cell 2 from ⟨hr, hz'⟩)
  have key := hall t1 ⟨ht1.1, le_rfl⟩ x1
  rcases eq_or_lt_of_le hK.1.1 with hs0 | hs0
  · subst hs0
    have := h0 y
    simp only [mul_zero, sub_zero] at key
    linarith
  · exfalso
    have hsT : s ∈ Icc 0 T := ⟨hs0.le, hK.1.2.trans ht1.2⟩
    have hxmax : ∀ z, u s z ≤ u s y := fun z => by
      have := hall s ⟨hs0.le, hK.1.2⟩ z; linarith
    have hC := hC2 s hsT
    have hgrad : ∀ j, pd j (u s) y = 0 := fun j =>
      pd_eq_zero_of_max _ (hC.differentiable (by norm_num)) y hxmax j
    have hlap : lap (u s) y ≤ 0 :=
      Finset.sum_nonpos fun i _ => pd_pd_nonpos_of_max _ hC y hxmax i
    have hconv : conv (v s) (u s) y = 0 := by simp [conv, hgrad]
    have hdt : dt T u s y ≤ 0 := by
      have := heq s hsT y
      rw [hconv, add_zero, smul_eq_mul] at this
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hν hlap
    have hd : HasDerivWithinAt (fun r => u r y - ε * r) (dt T u s y - ε * 1) (Icc 0 T) s :=
      (hdiff y s hsT).hasDerivWithinAt.sub ((hasDerivAt_id s).const_mul ε).hasDerivWithinAt
    have := deriv_nonneg_of_left_max hs0 hsT.2 hd fun r hr =>
      hall r ⟨hr.1, hr.2.trans hK.1.2⟩ y
    linarith

lemma pd_neg_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Pt d → E) (i : Fin d) :
    pd i (fun x => -h x) = fun x => -pd i h x := by
  funext x; simp [pd]

/-- The maximum principle `|u(t)| ≤ M` when `|u(0)| ≤ M`. -/
lemma max_principle_abs (T ν : ℝ) (hν : 0 ≤ ν) (v : ℝ → Pt 2 → Pt 2) (u : ℝ → Pt 2 → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2) (Icc 0 T ×ˢ univ))
    (hper : ∀ t ∈ Icc 0 T, IsPeriodic (u t))
    (hC2 : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (u t))
    (hdiff : ∀ x, ∀ t ∈ Icc 0 T, DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (heq : ∀ t ∈ Icc 0 T, ∀ x, dt T u t x + conv (v t) (u t) x = ν • lap (u t) x)
    (M : ℝ) (h0 : ∀ x, |u 0 x| ≤ M) : ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M := by
  intro t ht x
  rw [abs_le]
  constructor
  · have := max_principle_upper T ν hν v (fun t x => -u t x) hcont.neg
      (fun t ht y n => by simp [hper t ht y n]) (fun t ht => (hC2 t ht).neg)
      (fun y t ht => (hdiff y t ht).neg) ?_ M (fun y => (neg_le.1 (abs_le.1 (h0 y)).1))
      t ht x
    · linarith
    · intro t ht y
      have := heq t ht y
      have e1 : dt T (fun t x => -u t x) t y = -dt T u t y := by
        simp only [dt]; exact derivWithin.fun_neg
      have e2 : conv (v t) (fun x => -u t x) y = -conv (v t) (u t) y := by
        simp only [conv, pd_neg_fun, smul_neg, Finset.sum_neg_distrib]
      have e3 : lap (fun x => -u t x) y = -lap (u t) y := by
        simp only [lap, pd_neg_fun, Finset.sum_neg_distrib]
      rw [e1, e2, e3, smul_neg]
      rw [← neg_add, this]
  · exact max_principle_upper T ν hν v u hcont hper hC2 hdiff heq M
      (fun y => (abs_le.1 (h0 y)).2) t ht x
end maxp

end AnomDiss
