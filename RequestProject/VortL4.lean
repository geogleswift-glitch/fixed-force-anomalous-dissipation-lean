module

public import RequestProject.VortEnergy

/-!
# `L⁴` estimates for the vorticity of classical 2D Navier–Stokes solutions

For a classical solution `(v,p)` on `[0,1]` with force `g` and vorticity `ϖ = curl v`:

* (inviscid form) if `|curl g| ≤ A` on `[a,b]`, then `‖ϖ(b)‖₄ ≤ ‖ϖ(a)‖₄ + A (b - a)`;
* (viscous form) if `|g| ≤ B` on `[a,b]`, then `‖ϖ(b)‖₄² ≤ ‖ϖ(a)‖₄² + 3B²(b - a)/ν`.

The vorticity equation is used only through spatial mollification, so no regularity beyond the
classical `C^{1,2}` regularity of the solution is required.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace AnomDiss

/-- The vorticity `L⁴` functional `∫ (curl u)⁴`. -/
def vort4 (u : Pt 2 → Pt 2) : ℝ := ∫ x in cell 2, curl2 u x ^ 4

lemma vort4_nonneg (u : Pt 2 → Pt 2) : 0 ≤ vort4 u :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity

lemma pd_curl2 (u : Pt 2 → Pt 2) (hu : ContDiff ℝ 2 u) (j : Fin 2) (z : Pt 2) :
    pd j (curl2 u) z = pd j (pd 0 u) z 1 - pd j (pd 1 u) z 0 := by
  have hd : ∀ i, Differentiable ℝ (pd i u) := fun i =>
    (contDiff_pd_of_C2 u hu i).differentiable one_ne_zero
  show pd j (fun y => pd 0 u y 1 - pd 1 u y 0) z = _
  rw [pd_sub' (fun y => pd 0 u y 1) (fun y => pd 1 u y 0) z (differentiableAt_pi.1 (hd 0 z) 1)
    (differentiableAt_pi.1 (hd 1 z) 0), pd_component (pd 0 u) z (hd 0 z),
    pd_component (pd 1 u) z (hd 1 z)]

lemma abs_apply_le_norm (w : Pt 2) (k : Fin 2) : |w k| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w k

lemma continuous_curl2 {u : Pt 2 → Pt 2} (hu : ContDiff ℝ 2 u) : Continuous (curl2 u) := by
  have h1 : ∀ i, Continuous (pd i u) := fun i => continuous_pd_of_C1 u (hu.of_le (by norm_num)) i
  exact ((continuous_apply 1).comp (h1 0)).sub ((continuous_apply 0).comp (h1 1))

lemma contDiff_curl2 {u : Pt 2 → Pt 2} (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (curl2 u) := by
  have h1 : ∀ i, ContDiff ℝ 1 (pd i u) := fun i => contDiff_pd_of_C2 u hu i
  exact ((contDiff_apply ℝ ℝ 1).comp (h1 0)).sub ((contDiff_apply ℝ ℝ 0).comp (h1 1))

lemma isPeriodic_curl2 {u : Pt 2 → Pt 2} (hp : IsPeriodic u) : IsPeriodic (curl2 u) := by
  intro x n
  simp only [curl2, isPeriodic_pd u hp 0 x n, isPeriodic_pd u hp 1 x n]

/-! ### Uniform bounds for a classical solution -/

/-- Uniform bounds on the first and second spatial derivatives of a `C^{1,2}` field. -/
lemma parabolic_deriv_bounds {β : ℝ} {v : ℝ → Pt 2 → Pt 2} (reg : IsParabolicC12 1 β v) :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧ (∀ t ∈ Icc (0 : ℝ) 1, ∀ i x, ‖pd i (v t) x‖ ≤ B₁) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j x, ‖pd i (pd j (v t)) x‖ ≤ B₂ := by
  choose C1 hC1 using reg.bdd_d1
  choose C2 hC2 using reg.bdd_d2
  refine ⟨∑ i, |C1 i|, ∑ i, ∑ j, |C2 i j|, by positivity, by positivity,
    fun t ht i x => (hC1 i t ht x).trans ?_, fun t ht i j x => (hC2 i j t ht x).trans ?_⟩
  · exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |C1 i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  · calc C2 i j ≤ |C2 i j| := le_abs_self _
      _ ≤ ∑ j', |C2 i j'| := Finset.single_le_sum (f := fun j' => |C2 i j'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', |C2 i' j'| := Finset.single_le_sum (f := fun i' => ∑ j', |C2 i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-! ### The mollified vorticity of a classical solution -/

section moll

variable {ν : ℝ} {v₀ : Pt 2 → Pt 2} {g : ℝ → Pt 2 → Pt 2} {v : ℝ → Pt 2 → Pt 2}
  {p : ℝ → Pt 2 → ℝ}

/-- The mollified vorticity `W(t) = φ ⋆ curl v(t)`. -/
def mvort (φ : Pt 2 → ℝ) (v : ℝ → Pt 2 → Pt 2) (t : ℝ) (x : Pt 2) : ℝ := mc φ (curl2 (v t)) x

/-- Its time derivative, `curl (φ ⋆ ∂ₜv)` with the derivative on the kernel. -/
def mvortT (φ : Pt 2 → ℝ) (v : ℝ → Pt 2 → Pt 2) (t : ℝ) (x : Pt 2) : ℝ :=
  mc (pd 0 φ) (cmp (dt 1 v t) 1) x - mc (pd 1 φ) (cmp (dt 1 v t) 0) x

lemma mvort_eq {φ : Pt 2 → ℝ} (k : IsKer φ) {β : ℝ} (reg : IsParabolicC12 1 β v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Pt 2) :
    mvort φ v t x = mc (pd 0 φ) (cmp (v t) 1) x - mc (pd 1 φ) (cmp (v t) 0) x :=
  mc_curl2 k ((reg.smooth_x t ht).of_le (by norm_num)) x

lemma continuousOn_cmp {β : ℝ} (reg : IsParabolicC12 1 β v) (j : Fin 2) :
    ContinuousOn (fun q : ℝ × Pt 2 => cmp (v q.1) j q.2) (Icc 0 1 ×ˢ univ) :=
  (continuous_apply j).comp_continuousOn reg.continuousOn

lemma continuousOn_mvort {φ : Pt 2 → ℝ} (k : IsKer φ) {β : ℝ} (reg : IsParabolicC12 1 β v) :
    ContinuousOn (fun q : ℝ × Pt 2 => mvort φ v q.1 q.2) (Icc 0 1 ×ˢ univ) := by
  refine (((continuousOn_mc (u := fun s z => cmp (v s) 1 z) (k.pd 0).cont (k.pd 0).2 zero_le_one
    (continuousOn_cmp reg 1)).sub (continuousOn_mc (u := fun s z => cmp (v s) 0 z) (k.pd 1).cont
    (k.pd 1).2 zero_le_one (continuousOn_cmp reg 0)))).congr
    fun q hq => ?_
  exact mvort_eq k reg hq.1 q.2

lemma continuousOn_mvortT {φ : Pt 2 → ℝ} (k : IsKer φ) {β : ℝ} (hβ : 0 < β)
    (reg : IsParabolicC12 1 β v) :
    ContinuousOn (fun q : ℝ × Pt 2 => mvortT φ v q.1 q.2) (Icc 0 1 ×ˢ univ) := by
  have hc := reg.holder_dt.continuousOn hβ
  have hcj : ∀ j : Fin 2, ContinuousOn (fun q : ℝ × Pt 2 => cmp (dt 1 v q.1) j q.2)
      (Icc 0 1 ×ˢ univ) := fun j => (continuous_apply j).comp_continuousOn hc
  exact (continuousOn_mc (u := fun s z => cmp (dt 1 v s) 1 z) (k.pd 0).cont (k.pd 0).2
    zero_le_one (hcj 1)).sub (continuousOn_mc (u := fun s z => cmp (dt 1 v s) 0 z) (k.pd 1).cont
    (k.pd 1).2 zero_le_one (hcj 0))

lemma continuous_dt_slice {β : ℝ} (hβ : 0 < β) (reg : IsParabolicC12 1 β v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : Continuous (dt 1 v t) := by
  have hc := reg.holder_dt.continuousOn hβ
  exact continuousOn_univ.1 (hc.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
    fun x _ => ⟨ht, mem_univ _⟩)

lemma hasDerivAt_mvort {φ : Pt 2 → ℝ} (k : IsKer φ) {β : ℝ} (hβ : 0 < β)
    (reg : IsParabolicC12 1 β v) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Pt 2) :
    HasDerivAt (fun s => mvort φ v s x) (mvortT φ v t x) t := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo t ht
  obtain ⟨Cd, hCd⟩ := reg.bdd_dt
  have hsub : ∀ s ∈ Metric.ball t r, s ∈ Icc (0 : ℝ) 1 := fun s hs =>
    Ioo_subset_Icc_self (hball hs)
  have hcont : ∀ s ∈ Metric.ball t r, ∀ j : Fin 2, Continuous (cmp (v s) j) := fun s hs j =>
    (continuous_apply j).comp (reg.smooth_x s (hsub s hs)).continuous
  have hcont' : ∀ j : Fin 2, Continuous (cmp (dt 1 v t) j) := fun j =>
    (continuous_apply j).comp (continuous_dt_slice hβ reg (Ioo_subset_Icc_self ht))
  have hd : ∀ s ∈ Metric.ball t r, ∀ j : Fin 2, ∀ z,
      HasDerivAt (fun s => cmp (v s) j z) (cmp (dt 1 v s) j z) s := by
    intro s hs j z
    have hs' := hball hs
    have h := (reg.diff_t z s (Ioo_subset_Icc_self hs')).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hs'.1 hs'.2)
    exact hasDerivAt_pi.1 h j
  have hB : ∀ s ∈ Metric.ball t r, ∀ j : Fin 2, ∀ z, |cmp (dt 1 v s) j z| ≤ Cd := fun s hs j z =>
    (abs_apply_le_norm _ j).trans (hCd s (hsub s hs) z)
  have h1 := hasDerivAt_mc_time (k.pd 0).cont (k.pd 0).2 hr (fun s hs => hcont s hs 1) (hcont' 1)
    (fun s hs => hd s hs 1) (fun s hs => hB s hs 1) x
  have h0 := hasDerivAt_mc_time (k.pd 1).cont (k.pd 1).2 hr (fun s hs => hcont s hs 0) (hcont' 0)
    (fun s hs => hd s hs 0) (fun s hs => hB s hs 0) x
  refine (h1.sub h0).congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds t hr] with s hs
  exact mvort_eq k reg (hsub s hs) x

/-- The mollified vorticity equation `∂ₜW = -v·∇W + νΔW + G + R`. -/
lemma mvortT_eq {φ : Pt 2 → ℝ} (k : IsKer φ) (hv : IsClassicalNS 1 ν v₀ g v p) {β : ℝ}
    (reg : IsParabolicC12 1 β v) (regp : IsParabolicC01 1 β p) (hg : ∀ t, Continuous (g t))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : Pt 2) :
    mvortT φ v t x = -conv (v t) (mvort φ v t) x + ν * lap (mvort φ v t) x +
      ((mc (pd 0 φ) (cmp (g t) 1) x - mc (pd 1 φ) (cmp (g t) 0) x) +
        (conv (v t) (mvort φ v t) x - mc φ (conv (v t) (curl2 (v t))) x)) := by
  have hid := moll_vort_identity k ν (reg.smooth_x t ht) (hv.div_free t ht)
    (regp.smooth_x t ht) (hg t) (F := dt 1 v t) (fun z => hv.eqn t ht z) x
  unfold mvortT
  rw [hid, show mvort φ v t = mc φ (curl2 (v t)) from rfl]
  ring

end moll

/-! ### Uniform constants -/

section consts

variable {v : ℝ → Pt 2 → Pt 2} {B₁ B₂ : ℝ}

lemma cmp_lip (hv2 : ContDiff ℝ 2 (v t)) (hB₁ : ∀ i x, ‖pd i (v t) x‖ ≤ B₁) (j : Fin 2)
    (x y : Pt 2) : |v t x j - v t y j| ≤ 2 * B₁ * ‖x - y‖ := by
  have := lip_of_pd_bound (v t) (hv2.differentiable (by norm_num)) hB₁ x y
  exact (abs_apply_le_norm (v t x - v t y) j).trans this

lemma curl2_abs_le (hB₁ : ∀ i x, ‖pd i (v t) x‖ ≤ B₁) (x : Pt 2) :
    |curl2 (v t) x| ≤ 2 * B₁ := by
  unfold curl2
  have h0 := (abs_apply_le_norm (pd 0 (v t) x) 1).trans (hB₁ 0 x)
  have h1 := (abs_apply_le_norm (pd 1 (v t) x) 0).trans (hB₁ 1 x)
  calc |pd 0 (v t) x 1 - pd 1 (v t) x 0| ≤ |pd 0 (v t) x 1| + |pd 1 (v t) x 0| := abs_sub _ _
    _ ≤ 2 * B₁ := by linarith

lemma pd_curl2_abs_le (hv2 : ContDiff ℝ 2 (v t)) (hB₂ : ∀ i j x, ‖pd i (pd j (v t)) x‖ ≤ B₂)
    (j : Fin 2) (z : Pt 2) : |pd j (curl2 (v t)) z| ≤ 2 * B₂ := by
  rw [pd_curl2 _ hv2]
  have h0 := (abs_apply_le_norm (pd j (pd 0 (v t)) z) 1).trans (hB₂ j 0 z)
  have h1 := (abs_apply_le_norm (pd j (pd 1 (v t)) z) 0).trans (hB₂ j 1 z)
  calc |pd j (pd 0 (v t)) z 1 - pd j (pd 1 (v t)) z 0| ≤
        |pd j (pd 0 (v t)) z 1| + |pd j (pd 1 (v t)) z 0| := abs_sub _ _
    _ ≤ 2 * B₂ := by linarith

lemma curl2_lip (hv2 : ContDiff ℝ 2 (v t)) (hB₂ : ∀ i j x, ‖pd i (pd j (v t)) x‖ ≤ B₂)
    (x y : Pt 2) : |curl2 (v t) x - curl2 (v t) y| ≤ 2 * (2 * B₂) * ‖x - y‖ :=
  abs_lip_of_pd_bound _ ((contDiff_curl2 hv2).differentiable one_ne_zero)
    (pd_curl2_abs_le hv2 hB₂) x y

end consts

/-! ### A limiting argument -/

lemma limit_root {Ya Yb c d K K' : ℝ} {n : ℕ} (hn : 0 < n)
    (H : ∀ ε : ℝ, 0 < ε → ∃ Fa Fb : ℝ, 0 ≤ Fa ∧ 0 ≤ Fb ∧ |Fa - Ya| ≤ K * ε ∧ |Fb - Yb| ≤ K * ε ∧
      Fb ^ (1 / n : ℝ) ≤ Fa ^ (1 / n : ℝ) + (c + K' * ε) * d) :
    Yb ^ (1 / n : ℝ) ≤ Ya ^ (1 / n : ℝ) + c * d := by
  have hp0 : (0 : ℝ) ≤ 1 / n := by positivity
  choose Fa Fb hFa hFb hA hB hle using fun m : ℕ => H (1 / ((m : ℝ) + 1)) (by positivity)
  have he : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have conv : ∀ (F : ℕ → ℝ) (Y : ℝ), (∀ m, |F m - Y| ≤ K * (1 / ((m : ℝ) + 1))) →
      Tendsto F atTop (𝓝 Y) := by
    intro F Y hF
    have hK : Tendsto (fun m : ℕ => K * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using he.const_mul K
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m => norm_nonneg _) (fun m => by rw [Real.norm_eq_abs]; exact hF m) hK
  have hcont := Real.continuous_rpow_const hp0
  have hLa := (hcont.tendsto Ya).comp (conv Fa Ya hA)
  have hLb := (hcont.tendsto Yb).comp (conv Fb Yb hB)
  have hR : Tendsto (fun m : ℕ => Fa m ^ (1 / n : ℝ) + (c + K' * (1 / ((m : ℝ) + 1))) * d) atTop
      (𝓝 (Ya ^ (1 / n : ℝ) + (c + K' * 0) * d)) :=
    hLa.add (((tendsto_const_nhds.add (he.const_mul K')).mul_const d))
  rw [mul_zero, add_zero] at hR
  exact le_of_tendsto_of_tendsto' hLb hR hle

lemma abs_four_sub_le {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a ^ 4 - b ^ 4| ≤ 4 * M ^ 3 * |a - b| := by
  have hM : 0 ≤ M := (abs_nonneg _).trans ha
  have e : a ^ 4 - b ^ 4 = (a - b) * ((a + b) * (a ^ 2 + b ^ 2)) := by ring
  rw [e, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_mul]
  have h1 : |a + b| ≤ 2 * M := (abs_add_le _ _).trans (by linarith)
  have h2 : |a ^ 2 + b ^ 2| ≤ 2 * M ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have : a ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs a, abs_nonneg a]
    have : b ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
    linarith
  calc |a + b| * |a ^ 2 + b ^ 2| ≤ (2 * M) * (2 * M ^ 2) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 4 * M ^ 3 := by ring

end AnomDiss
