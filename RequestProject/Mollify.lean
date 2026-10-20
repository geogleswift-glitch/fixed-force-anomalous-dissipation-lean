module

public import RequestProject.TorusCalc

/-!
# Spatial mollification on `ℝ²`

Convolution `(φ ⋆ h)(x) = ∫ φ(y) h(x - y) dy` of a function `h` on `ℝ²` with a smooth compactly
supported kernel `φ`.  Used in Section 6 to give a meaning to the vorticity equation for
classical (only `C^{1,2}`) Navier–Stokes solutions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff Convolution

noncomputable section

namespace AnomDiss

/-- Mollification `(φ ⋆ h)(x) = ∫ φ(y) h(x - y) dy`. -/
def mc (φ h : Pt 2 → ℝ) (x : Pt 2) : ℝ := ∫ y, φ y * h (x - y)

lemma mc_eq_flip (φ h : Pt 2 → ℝ) (x : Pt 2) : mc φ h x = ∫ z, h z * φ (x - z) := by
  unfold mc
  rw [← integral_sub_left_eq_self (fun y => φ y * h (x - y)) volume x]
  simp [mul_comm]

lemma mc_eq_conv (φ h : Pt 2 → ℝ) (x : Pt 2) :
    mc φ h x = (h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] φ) x := by
  rw [mc_eq_flip]; rfl

lemma hasFDerivAt_mc {φ h : Pt 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (x : Pt 2) :
    HasFDerivAt (mc φ h)
      ((h ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR (Pt 2), volume] fderiv ℝ φ) x) x := by
  have e : mc φ h = h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] φ := funext fun x => mc_eq_conv φ h x
  rw [e]
  exact hφc.hasFDerivAt_convolution_right _ hh.locallyIntegrable hφ x

lemma pd_mc {φ h : Pt 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (i : Fin 2) (x : Pt 2) :
    pd i (mc φ h) x = mc (pd i φ) h x := by
  unfold pd
  rw [(hasFDerivAt_mc hφ hφc hh x).fderiv,
    convolution_precompR_apply _ hh.locallyIntegrable (hφc.fderiv ℝ)
      (hφ.continuous_fderiv one_ne_zero), mc_eq_conv]

lemma differentiable_mc {φ h : Pt 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) : Differentiable ℝ (mc φ h) := fun x =>
  (hasFDerivAt_mc hφ hφc hh x).differentiableAt

lemma contDiff_mc {n : ℕ∞} {φ h : Pt 2 → ℝ} (hφ : ContDiff ℝ n φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) : ContDiff ℝ n (mc φ h) := by
  have e : mc φ h = h ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] φ := funext fun x => mc_eq_conv φ h x
  rw [e]
  exact hφc.contDiff_convolution_right _ hh.locallyIntegrable hφ

lemma hasCompactSupport_sub_left {φ : Pt 2 → ℝ} (hφc : HasCompactSupport φ) (x : Pt 2) :
    HasCompactSupport (fun z => φ (x - z)) :=
  hφc.comp_homeomorph (Homeomorph.subLeft x)

/-- Moving a derivative from `h` onto the kernel: `φ ⋆ ∂ᵢh = (∂ᵢφ) ⋆ h`. -/
lemma mc_pd {φ h : Pt 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hh : ContDiff ℝ 1 h) (i : Fin 2) (x : Pt 2) :
    mc φ (pd i h) x = mc (pd i φ) h x := by
  rw [mc_eq_flip, mc_eq_flip]
  set f : Pt 2 → ℝ := fun z => φ (x - z) with hf
  have hfd : ∀ z, HasFDerivAt f (-(fderiv ℝ φ (x - z))) z := by
    intro z
    have h1 := ((hφ.differentiable one_ne_zero) (x - z)).hasFDerivAt
    have h2 : HasFDerivAt (fun z : Pt 2 => x - z) (-ContinuousLinearMap.id ℝ (Pt 2)) z := by
      simpa using (hasFDerivAt_const (𝕜 := ℝ) x z).sub (hasFDerivAt_id (𝕜 := ℝ) z)
    have := h1.comp z h2
    convert this using 1 <;> ext v <;> simp [hf]
  have hfdiff : Differentiable ℝ f := fun z => (hfd z).differentiableAt
  have hfder : ∀ z, fderiv ℝ f z (Pi.single i 1) = -pd i φ (x - z) := fun z => by
    rw [(hfd z).fderiv]; rfl
  have hfc : HasCompactSupport f := hasCompactSupport_sub_left hφc x
  have hfcont : Continuous f := hφ.continuous.comp (continuous_const.sub continuous_id)
  have hpφ : Continuous (pd i φ) := continuous_pd_of_C1 φ hφ i
  have hph : Continuous (pd i h) := continuous_pd_of_C1 h hh i
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f) (g := h)
    (v := Pi.single i 1) ?_ ?_ ?_ (fun z _ => hfdiff z)
      (fun z _ => hh.differentiable one_ne_zero z)
  · have e1 : (fun z => pd i h z * φ (x - z)) = fun z => f z * fderiv ℝ h z (Pi.single i 1) :=
      funext fun z => by simp only [hf, pd]; ring
    have e2 : (fun z => h z * pd i φ (x - z)) = fun z => -(fderiv ℝ f z (Pi.single i 1) * h z) :=
      funext fun z => by rw [hfder]; ring
    rw [e1, e2, key, integral_neg]
  · simp only [hfder]
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hpφ.comp (continuous_const.sub continuous_id)).neg).mul hh.continuous
    · exact ((hasCompactSupport_sub_left (hφc.fderiv_apply (𝕜 := ℝ) _) x).neg).mul_right
  · refine Continuous.integrable_of_hasCompactSupport (hfcont.mul hph) hfc.mul_right
  · exact Continuous.integrable_of_hasCompactSupport (hfcont.mul hh.continuous) hfc.mul_right

/-! ### Algebraic properties -/

lemma integrable_mc_integrand {φ h : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (x : Pt 2) : Integrable (fun y => φ y * h (x - y)) :=
  Continuous.integrable_of_hasCompactSupport (hφ.mul (hh.comp (continuous_const.sub continuous_id)))
    hφc.mul_right

lemma mc_add {φ h₁ h₂ : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (h1 : Continuous h₁) (h2 : Continuous h₂) (x : Pt 2) :
    mc φ (fun z => h₁ z + h₂ z) x = mc φ h₁ x + mc φ h₂ x := by
  unfold mc
  rw [← integral_add (integrable_mc_integrand hφ hφc h1 x) (integrable_mc_integrand hφ hφc h2 x)]
  congr 1; funext y; ring

lemma mc_sub {φ h₁ h₂ : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (h1 : Continuous h₁) (h2 : Continuous h₂) (x : Pt 2) :
    mc φ (fun z => h₁ z - h₂ z) x = mc φ h₁ x - mc φ h₂ x := by
  unfold mc
  rw [← integral_sub (integrable_mc_integrand hφ hφc h1 x) (integrable_mc_integrand hφ hφc h2 x)]
  congr 1; funext y; ring

lemma mc_const_mul (φ h : Pt 2 → ℝ) (c : ℝ) (x : Pt 2) :
    mc φ (fun z => c * h z) x = c * mc φ h x := by
  unfold mc
  rw [← integral_const_mul]
  congr 1; funext y; ring

lemma mc_neg (φ h : Pt 2 → ℝ) (x : Pt 2) : mc φ (fun z => -h z) x = -mc φ h x := by
  unfold mc
  rw [← integral_neg]
  congr 1; funext y; ring

lemma mc_sum {φ : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {ι : Type*}
    (s : Finset ι) (h : ι → Pt 2 → ℝ) (hh : ∀ i, Continuous (h i)) (x : Pt 2) :
    mc φ (fun z => ∑ i ∈ s, h i z) x = ∑ i ∈ s, mc φ (h i) x := by
  unfold mc
  rw [← integral_finset_sum _ (fun i _ => integrable_mc_integrand hφ hφc (hh i) x)]
  congr 1; funext y; rw [Finset.mul_sum]

lemma isPeriodic_mc (φ : Pt 2 → ℝ) {h : Pt 2 → ℝ} (hp : IsPeriodic h) : IsPeriodic (mc φ h) := by
  intro x n
  unfold mc
  congr 1; funext y
  rw [show x + intVec n - y = (x - y) + intVec n by abel, hp]

/-! ### Estimates -/

/-- A probability kernel average of a function bounded by `c` on the support is bounded by `c`. -/
lemma abs_integral_kernel_le {φ F : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1) {c : ℝ}
    (hc : ∀ y, φ y ≠ 0 → |F y| ≤ c) : |∫ y, φ y * F y| ≤ c := by
  have hint : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have := norm_integral_le_of_norm_le (f := fun y => φ y * F y) (hint.const_mul c)
    (Eventually.of_forall fun y => ?_)
  · rw [integral_const_mul, hφ1, mul_one] at this
    exact this
  · by_cases hy : φ y = 0
    · simp [hy]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 y), mul_comm c]
      exact mul_le_mul_of_nonneg_left (hc y hy) (hφ0 y)

lemma abs_mc_le {φ h : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1) {c : ℝ}
    (hc : ∀ z, |h z| ≤ c) (x : Pt 2) : |mc φ h x| ≤ c :=
  abs_integral_kernel_le hφ hφc hφ0 hφ1 fun _ _ => hc _

/-- Mollification error: `|φ ⋆ h (x) - h(x)| ≤ c` if `h` oscillates by at most `c` on the
support of `φ` around `x`. -/
lemma abs_mc_sub_le {φ h : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1) (hh : Continuous h) {c : ℝ} (x : Pt 2)
    (hc : ∀ y, φ y ≠ 0 → |h (x - y) - h x| ≤ c) : |mc φ h x - h x| ≤ c := by
  have hint : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have e : mc φ h x - h x = ∫ y, φ y * (h (x - y) - h x) := by
    unfold mc
    rw [show (fun y => φ y * (h (x - y) - h x)) = fun y => φ y * h (x - y) - φ y * h x from
      funext fun y => by ring, integral_sub (integrable_mc_integrand hφ hφc hh x)
      (hint.mul_const _), integral_mul_const, hφ1, one_mul]
  rw [e]
  exact abs_integral_kernel_le hφ hφc hφ0 hφ1 hc

/-- Commutator estimate: `|a(x) (φ ⋆ h)(x) - φ ⋆ (a h)(x)| ≤ c`. -/
lemma abs_commutator_le {φ a h : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1) (ha : Continuous a) (hh : Continuous h)
    {c : ℝ} (x : Pt 2) (hc : ∀ y, φ y ≠ 0 → |(a x - a (x - y)) * h (x - y)| ≤ c) :
    |a x * mc φ h x - mc φ (fun z => a z * h z) x| ≤ c := by
  have e : a x * mc φ h x - mc φ (fun z => a z * h z) x =
      ∫ y, φ y * ((a x - a (x - y)) * h (x - y)) := by
    unfold mc
    rw [← integral_const_mul, ← integral_sub ((integrable_mc_integrand hφ hφc hh x).const_mul _)
      (integrable_mc_integrand (h := fun z => a z * h z) hφ hφc (ha.mul hh) x)]
    congr 1; funext y; ring
  rw [e]
  exact abs_integral_kernel_le hφ hφc hφ0 hφ1 hc

/-! ### Dependence on a time parameter -/

/-- Differentiation in time under the mollification. -/
lemma hasDerivAt_mc_time {φ : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {u u' : ℝ → Pt 2 → ℝ} {t₀ r B : ℝ} (hr : 0 < r)
    (hu : ∀ s ∈ Metric.ball t₀ r, Continuous (u s)) (hu' : Continuous (u' t₀))
    (hd : ∀ s ∈ Metric.ball t₀ r, ∀ z, HasDerivAt (fun s => u s z) (u' s z) s)
    (hB : ∀ s ∈ Metric.ball t₀ r, ∀ z, |u' s z| ≤ B) (x : Pt 2) :
    HasDerivAt (fun s => mc φ (u s) x) (mc φ (u' t₀) x) t₀ := by
  have hint : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hs : Continuous fun y : Pt 2 => x - y := continuous_const.sub continuous_id
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun s y => φ y * u s (x - y)) (F' := fun s y => φ y * u' s (x - y))
    (bound := fun y => |φ y| * B) (Metric.ball_mem_nhds t₀ hr) ?_ ?_ ?_ ?_
    (hint.abs.mul_const B) ?_
  · exact this.2
  · filter_upwards [Metric.ball_mem_nhds t₀ hr] with s hs'
    exact (hφ.mul ((hu s hs').comp hs)).aestronglyMeasurable
  · exact integrable_mc_integrand hφ hφc (hu t₀ (Metric.mem_ball_self hr)) x
  · exact (hφ.mul (hu'.comp hs)).aestronglyMeasurable
  · refine Eventually.of_forall fun y s hs' => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB s hs' _) (abs_nonneg _)
  · exact Eventually.of_forall fun y s hs' => (hd s hs' (x - y)).const_mul (φ y)

/-- Joint continuity of a mollified time-dependent function. -/
lemma continuousOn_mc {φ : Pt 2 → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {u : ℝ → Pt 2 → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2) (Icc a b ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Pt 2 => mc φ (u p.1) p.2) (Icc a b ×ˢ univ) := by
  set u' : ℝ → Pt 2 → ℝ := fun s z => u (projIcc a b hab s) z with hu'def
  have hu'c : Continuous (fun p : ℝ × Pt 2 => u' p.1 p.2) := by
    have : Continuous (fun p : ℝ × Pt 2 => ((projIcc a b hab p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
    exact hu.comp_continuous this (fun p => ⟨Subtype.mem _, mem_univ _⟩)
  set K := tsupport φ
  have hK : IsCompact K := hφc.isCompact
  have hF : Continuous (Function.uncurry fun (p : ℝ × Pt 2) (y : Pt 2) => φ y * u' p.1 (p.2 - y)) := by
    refine (hφ.comp continuous_snd).mul ?_
    exact hu'c.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).sub continuous_snd))
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hF hK
  refine hc.continuousOn.congr fun p hp => ?_
  simp only [mc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_]
  · simp only [hu'def, projIcc_of_mem hab hp.1]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-! ### Existence of mollifiers -/

/-- Smooth probability kernels supported in the ball of radius `ε`. -/
lemma exists_mollifier {ε : ℝ} (hε : 0 < ε) : ∃ φ : Pt 2 → ℝ, ContDiff ℝ ∞ φ ∧
    HasCompactSupport φ ∧ (∀ y, 0 ≤ φ y) ∧ (∫ y, φ y = 1) ∧ ∀ y, φ y ≠ 0 → ‖y‖ < ε := by
  let f : ContDiffBump (0 : Pt 2) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, f.nonneg_normed,
    f.integral_normed, fun y hy => ?_⟩
  have : y ∈ Function.support (f.normed volume) := hy
  rw [f.support_normed_eq, mem_ball_zero_iff] at this
  exact this

end AnomDiss
