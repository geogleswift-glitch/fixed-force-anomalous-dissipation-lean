module

public import RequestProject.PulseCalc

/-!
# Energy estimates for perturbed Navier–Stokes flows

Generic tools used in the proof of the single-stage stability estimate (Lemma 5.3): a Grönwall
inequality in integral form, the time-integrated energy identity, the spatial energy inequality
for a perturbation of a Navier–Stokes flow, and the triangle inequality for the `L²` norm.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- Grönwall's inequality in integral form, with a continuous rate. -/
lemma gronwall_of_integral {a b : ℝ} (hab : a ≤ b) {f h g : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, h s)
    (hh : ContinuousOn h (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hle : ∀ s ∈ Ioo a b, h s ≤ 2 * g s * f s) :
    ∀ t ∈ Icc a b, f t ≤ f a * Real.exp (2 * ∫ s in a..t, g s) := by
  set G : ℝ → ℝ := fun t => ∫ s in a..t, g s with hG
  set F : ℝ → ℝ := fun t => f t * Real.exp (-(2 * G t)) with hF
  have hprim : ∀ {k : ℝ → ℝ}, ContinuousOn k (Icc a b) →
      ContinuousOn (fun t => ∫ s in a..t, k s) (Icc a b) := by
    intro k hk
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := k) (a := a)
      (b := b) (by rw [uIcc_of_le hab]; exact hk.integrableOn_compact isCompact_Icc)
    rwa [uIcc_of_le hab] at this
  have hderiv : ∀ {k : ℝ → ℝ}, ContinuousOn k (Icc a b) → ∀ t ∈ Ioo a b,
      HasDerivAt (fun t => ∫ s in a..t, k s) (k t) t := by
    intro k hk t ht
    have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ (hk.continuousAt hnhds)
    · exact (hk.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
    · exact (hk.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hfc : ContinuousOn f (Icc a b) :=
    (continuousOn_const.add (hprim hh)).congr fun t ht => hf t ht
  have hfd : ∀ t ∈ Ioo a b, HasDerivAt f (h t) t := by
    intro t ht
    refine ((hderiv hh t ht).const_add (f a)).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs using hf s hs
  have hFd : ∀ t ∈ Ioo a b, HasDerivAt F
      (h t * Real.exp (-(2 * G t)) + f t * (Real.exp (-(2 * G t)) * (-(2 * g t)))) t := by
    intro t ht
    exact (hfd t ht).mul (((hderiv hg t ht).const_mul 2).neg.exp)
  have hFc : ContinuousOn F (Icc a b) :=
    hfc.mul ((continuousOn_const.mul (hprim hg)).neg.rexp)
  have hanti : AntitoneOn F (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hFc ?_ ?_
    · rw [interior_Icc]; exact fun t ht => (hFd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hFd t ht).deriv]
      have := hle t ht
      have he := Real.exp_pos (-(2 * G t))
      nlinarith
  intro t ht
  have h1 := hanti ⟨le_rfl, hab⟩ ht ht.1
  simp only [hF, hG, intervalIntegral.integral_same, mul_zero, neg_zero, Real.exp_zero,
    mul_one] at h1
  have he := Real.exp_pos (2 * ∫ s in a..t, g s)
  calc f t = f t * Real.exp (-(2 * ∫ s in a..t, g s)) * Real.exp (2 * ∫ s in a..t, g s) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ f a * Real.exp (2 * ∫ s in a..t, g s) := by gcongr

/-- Integrals over the cell of jointly continuous functions depend continuously on time. -/
lemma continuousOn_integral_cell' {a b : ℝ} (hab : a ≤ b) (G : ℝ → Pt 2 → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Pt 2 => G p.1 p.2) (Icc a b ×ˢ univ)) :
    ContinuousOn (fun s => ∫ x in cell 2, G s x) (Icc a b) := by
  set G' : ℝ → Pt 2 → ℝ := fun s x => G (projIcc a b hab s) x
  have hG' : Continuous (Function.uncurry G') := by
    have : Continuous (fun p : ℝ × Pt 2 => ((projIcc a b hab p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
    exact hG.comp_continuous this (fun p => ⟨Subtype.mem _, mem_univ _⟩)
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hG' (isCompact_Icc
    (a := (0 : Pt 2)) (b := 1))
  refine hc.continuousOn.congr fun s hs => ?_
  simp only [G', projIcc_of_mem hab hs]
  rfl

/-- The time-integrated energy identity `‖u(t)‖₂² = ‖u(a)‖₂² + ∫ₐᵗ ∫ 2 u·∂ₜu`, together with
the continuity of the energy rate. -/
lemma l2sqV_integral_form {a b : ℝ} (hab : a ≤ b) (u u' : ℝ → Pt 2 → Pt 2)
    (hu : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2) (Icc a b ×ˢ univ))
    (hu' : ContinuousOn (fun p : ℝ × Pt 2 => u' p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => u r x) (u' s x) s) :
    (∀ t ∈ Icc a b, l2sqV (u t) = l2sqV (u a) +
      ∫ s in a..t, ∫ x in cell 2, 2 * dot (u s x) (u' s x)) ∧
    ContinuousOn (fun s => ∫ x in cell 2, 2 * dot (u s x) (u' s x)) (Icc a b) := by
  set F : ℝ → Pt 2 → ℝ := fun s x => 2 * dot (u s x) (u' s x) with hF
  have hcomp : ∀ k : Fin 2, ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2 k) (Icc a b ×ˢ univ) :=
    fun k => (continuous_apply k).comp_continuousOn hu
  have hcomp' : ∀ k : Fin 2, ContinuousOn (fun p : ℝ × Pt 2 => u' p.1 p.2 k)
      (Icc a b ×ˢ univ) := fun k => (continuous_apply k).comp_continuousOn hu'
  have hFc : ContinuousOn (fun p : ℝ × Pt 2 => F p.1 p.2) (Icc a b ×ˢ univ) := by
    simp only [hF, dot]
    exact continuousOn_const.mul (continuousOn_finset_sum _ fun k _ => (hcomp k).mul (hcomp' k))
  have hEc : ContinuousOn (fun p : ℝ × Pt 2 => ∑ k, u p.1 p.2 k ^ 2) (Icc a b ×ˢ univ) :=
    continuousOn_finset_sum _ fun k _ => (hcomp k).pow 2
  refine ⟨fun t ht => ?_, continuousOn_integral_cell' hab F hFc⟩
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hline : ∀ x, ∀ {G : ℝ → Pt 2 → ℝ},
      ContinuousOn (fun p : ℝ × Pt 2 => G p.1 p.2) (Icc a b ×ˢ univ) →
      ContinuousOn (fun s => G s x) (Icc a t) := fun x G hG =>
    hG.comp (Continuous.prodMk continuous_id continuous_const).continuousOn
      (fun s hs => ⟨hsub hs, mem_univ _⟩)
  have step1 : ∀ x, ∑ k, u t x k ^ 2 - ∑ k, u a x k ^ 2 = ∫ s in a..t, F s x := by
    intro x
    symm
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hline x (G := fun s x => ∑ k, u s x k ^ 2) hEc) (fun s hs => ?_) ?_
    · have hsb : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
      have hdk : ∀ k, HasDerivAt (fun r => u r x k) (u' s x k) s := fun k =>
        hasDerivAt_pi.1 (hd s hsb x) k
      refine HasDerivAt.hasDerivWithinAt ?_
      have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hdk k).pow 2
      convert this using 1
      simp only [hF, dot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp; ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1]
      exact hline x hFc
  have hcont : ∀ s ∈ Icc a b, Continuous (fun x => ∑ k, u s x k ^ 2) := by
    intro s hs
    have : Continuous fun x : Pt 2 => ((s, x) : ℝ × Pt 2) := Continuous.prodMk continuous_const
      continuous_id
    exact hEc.comp_continuous this fun x => ⟨hs, mem_univ _⟩
  have step2 : l2sqV (u t) - l2sqV (u a) = ∫ x in cell 2, ∫ s in a..t, F s x := by
    rw [l2sqV, l2sqV, ← integral_sub (integrableOn_cell_of_continuous (hcont t ht))
      (integrableOn_cell_of_continuous (hcont a ⟨le_rfl, hab⟩))]
    exact setIntegral_congr_fun measurableSet_Icc fun x _ => step1 x
  have step3 : ∫ x in cell 2, ∫ s in a..t, F s x = ∫ s in a..t, ∫ x in cell 2, F s x := by
    simp only [intervalIntegral.integral_of_le ht.1]
    refine integral_integral_swap ?_
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : ContinuousOn (fun q : Pt 2 × ℝ => F q.2 q.1) (cell 2 ×ˢ Icc a t) :=
      hFc.comp continuous_swap.continuousOn (fun q hq => ⟨hsub hq.2, mem_univ _⟩)
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono subset_rfl Ioc_subset_Icc_self)
  linarith

lemma abs_dot_le (u v : Pt 2) : |dot u v| ≤ euclNorm u * euclNorm v := by
  have := abs_real_inner_le_norm (toE u) (toE v)
  rw [← euclNorm_eq, ← euclNorm_eq] at this
  convert this using 2
  simp [toE, dot, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
lemma euclNorm_apply_le (A : Pt 2 →L[ℝ] Pt 2) (e : Pt 2) : euclNorm (A e) ≤ eucOp A * euclNorm e := by
  by_cases he : euclNorm e = 0
  · have : e = 0 := (euclNorm_eq_zero_iff' e).1 he
    subst this; simp [euclNorm]
  · have hpos : 0 < euclNorm e := lt_of_le_of_ne (euclNorm_nonneg _) (Ne.symm he)
    have h1 : euclNorm ((euclNorm e)⁻¹ • e) = 1 := by
      rw [euclNorm_smul, abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ he]
    have := le_eucOp A _ h1
    rw [map_smul, euclNorm_smul, abs_of_pos (inv_pos.2 hpos)] at this
    rw [inv_mul_le_iff₀ hpos] at this
    linarith

lemma lap_component (w : Pt 2 → Pt 2) (hw : ContDiff ℝ 2 w) (k : Fin 2) (x : Pt 2) :
    lap (fun y => w y k) x = lap w x k := by
  have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have h1 : ∀ i, pd i (fun y => w y k) = fun y => pd i w y k := fun i => funext fun y =>
    pd_component w y (hd y) i k
  unfold lap
  simp only [h1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact pd_component (pd i w) x (((contDiff_pd_of_C2 w hw i).differentiable (by norm_num)) x) i k

lemma conv_component (u w : Pt 2 → Pt 2) (hw : Differentiable ℝ w) (k : Fin 2) (x : Pt 2) :
    conv u (fun y => w y k) x = conv u w x k := by
  unfold conv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pd_component w x (hw x) j k]

lemma conv_eq_fderiv (w B : Pt 2 → Pt 2) (x : Pt 2) :
    conv w B x = fderiv ℝ B x (w x) := by
  unfold conv pd
  conv_rhs => rw [show w x = ∑ j, w x j • (Pi.single j 1 : Pt 2) by
    ext i; simp [Pi.single_apply]]
  simp [map_smul]

/-- Spatial energy inequality for a perturbation `w` of a Navier–Stokes flow:
if `W' + u·∇w + w·∇B + ∇pr = νΔw` then `∫ 2 w·W' ≤ 2G‖w‖₂²` when `‖∇B‖_op ≤ G`. -/
lemma spatial_energy_le (ν G : ℝ) (hν : 0 ≤ ν) (u w B W' : Pt 2 → Pt 2) (pr : Pt 2 → ℝ)
    (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u) (hudiv : ∀ x, divergence u x = 0)
    (hw : ContDiff ℝ 2 w) (hwp : IsPeriodic w) (hwdiv : ∀ x, divergence w x = 0)
    (hpr : ContDiff ℝ 1 pr) (hprp : IsPeriodic pr)
    (hB : ContDiff ℝ 1 B) (hBG : ∀ x, eucOp (fderiv ℝ B x) ≤ G)
    (heq : ∀ x, W' x + conv u w x + conv w B x + grad pr x = ν • lap w x) :
    ∫ x in cell 2, 2 * dot (w x) (W' x) ≤ 2 * G * l2sqV w := by
  have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hwk : ∀ k : Fin 2, ContDiff ℝ 2 (fun y => w y k) := fun k => (contDiff_apply ℝ ℝ k).comp hw
  have hwk1 : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => w y k) := fun k => (hwk k).of_le (by norm_num)
  have hwkp : ∀ k : Fin 2, IsPeriodic (fun y => w y k) := fun k x n => by simp [hwp x n]
  set S1 : Pt 2 → ℝ := fun x => ∑ k, w x k * lap (fun y => w y k) x
  set S2 : Pt 2 → ℝ := fun x => ∑ k, w x k * conv u (fun y => w y k) x
  set S3 : Pt 2 → ℝ := fun x => dot (w x) (fderiv ℝ B x (w x))
  set S4 : Pt 2 → ℝ := fun x => ∑ k, w x k * pd k pr x
  have e : ∀ x, 2 * dot (w x) (W' x) = 2 * ν * S1 x - 2 * S2 x - 2 * S4 x - 2 * S3 x := by
    intro x
    have hW : W' x = ν • lap w x - conv u w x - conv w B x - grad pr x := by
      rw [← heq x]; abel
    simp only [S1, S2, S3, S4, hW, dot, conv_eq_fderiv w B x, lap_component w hw,
      conv_component u w hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, grad, Fin.sum_univ_two]
    ring
  have cw : Continuous w := hw.continuous
  have c1 : Continuous S1 := continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp cw).mul (continuous_lap_of_C2 _ (hwk k))
  have c2 : Continuous S2 := continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp cw).mul (continuous_conv_of_C1 u hu.continuous _ (hwk1 k))
  have c3 : Continuous S3 := by
    have : Continuous fun x => fderiv ℝ B x (w x) := (hB.continuous_fderiv one_ne_zero).clm_apply cw
    simp only [S3, dot]
    exact continuous_finset_sum _ fun k _ => ((continuous_apply k).comp cw).mul
      ((continuous_apply k).comp this)
  have c4 : Continuous S4 := continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp cw).mul (continuous_pd_of_C1 pr hpr k)
  have i := fun {F : Pt 2 → ℝ} (hF : Continuous F) => integrableOn_cell_of_continuous hF
  have i2 : ∀ (c : ℝ) {F : Pt 2 → ℝ}, Continuous F → IntegrableOn (fun x => c * F x) (cell 2) :=
    fun c F hF => i (continuous_const.mul hF)
  rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc fun x _ => e x,
    integral_sub (f := fun x => 2 * ν * S1 x - 2 * S2 x - 2 * S4 x) (g := fun x => 2 * S3 x)
      (((i2 _ c1).sub (i2 _ c2)).sub (i2 _ c4)) (i2 _ c3),
    integral_sub (f := fun x => 2 * ν * S1 x - 2 * S2 x) (g := fun x => 2 * S4 x)
      ((i2 _ c1).sub (i2 _ c2)) (i2 _ c4),
    integral_sub (f := fun x => 2 * ν * S1 x) (g := fun x => 2 * S2 x) (i2 _ c1) (i2 _ c2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  -- the four integrals
  have I1 : ∫ x in cell 2, S1 x ≤ 0 := by
    simp only [S1]
    rw [integral_finset_sum (f := fun k x => w x k * lap (fun y => w y k) x) _
      fun k _ => i (((continuous_apply k).comp cw).mul (continuous_lap_of_C2 _ (hwk k)))]
    refine Finset.sum_nonpos fun k _ => ?_
    rw [integral_mul_lap _ (hwk k) (hwkp k), neg_nonpos]
    exact setIntegral_nonneg measurableSet_Icc fun x _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
  have I2 : ∫ x in cell 2, S2 x = 0 := by
    simp only [S2]
    rw [integral_finset_sum (f := fun k x => w x k * conv u (fun y => w y k) x) _
      fun k _ => i (((continuous_apply k).comp cw).mul
        (continuous_conv_of_C1 u hu.continuous _ (hwk1 k)))]
    exact Finset.sum_eq_zero fun k _ => integral_mul_conv u hu hup hudiv _ (hwk1 k) (hwkp k)
  have I4 : ∫ x in cell 2, S4 x = 0 := by
    simp only [S4]
    rw [integral_finset_sum (f := fun k x => w x k * pd k pr x) _
      fun k _ => i (((continuous_apply k).comp cw).mul (continuous_pd_of_C1 pr hpr k))]
    simp only [fun k => integral_mul_pd (fun y => w y k) pr (hwk1 k) hpr (hwkp k) hprp k]
    rw [Finset.sum_neg_distrib, ← integral_finset_sum (f := fun k x => pd k (fun y => w y k) x * pr x)
      _ fun k _ => i ((continuous_pd_of_C1 _ (hwk1 k) k).mul hpr.continuous)]
    have : ∀ x, ∑ k : Fin 2, pd k (fun y => w y k) x * pr x = 0 := by
      intro x
      rw [← Finset.sum_mul]
      have := hwdiv x
      unfold divergence at this
      simp only [← pd_component w x (hd x)] at this
      rw [this, zero_mul]
    simp [this]
  have I3 : -(G * l2sqV w) ≤ ∫ x in cell 2, S3 x := by
    rw [l2sqV, ← integral_const_mul, ← integral_neg]
    refine setIntegral_mono_on (i (continuous_const.mul ?_)).neg (i c3) measurableSet_Icc
      fun x _ => ?_
    · exact continuous_finset_sum _ fun k _ => ((continuous_apply k).comp cw).pow 2
    have h1 := abs_dot_le (w x) (fderiv ℝ B x (w x))
    have h2 := euclNorm_apply_le (fderiv ℝ B x) (w x)
    have h3 : euclNorm (w x) ^ 2 = ∑ k, w x k ^ 2 := by rw [euclNorm_sq, Fin.sum_univ_two]
    have h0 := euclNorm_nonneg (w x)
    have hG := hBG x
    have hE := eucOp_nonneg (fderiv ℝ B x)
    have : |S3 x| ≤ G * ∑ k, w x k ^ 2 := by
      rw [← h3]
      calc |S3 x| ≤ euclNorm (w x) * euclNorm (fderiv ℝ B x (w x)) := h1
        _ ≤ euclNorm (w x) * (eucOp (fderiv ℝ B x) * euclNorm (w x)) := by gcongr
        _ ≤ G * euclNorm (w x) ^ 2 := by nlinarith
    linarith [neg_abs_le (S3 x)]
  rw [I2, I4]
  nlinarith

lemma l2sqV_add_smul (a b : Pt 2 → Pt 2) (ha : Continuous a) (hb : Continuous b) (r : ℝ) :
    l2sqV (fun x => a x + r • b x) =
      l2sqV a + 2 * r * (∫ x in cell 2, dot (a x) (b x)) + r ^ 2 * l2sqV b := by
  have i := fun {F : Pt 2 → ℝ} (hF : Continuous F) => integrableOn_cell_of_continuous hF
  have cA : Continuous fun x => ∑ k, a x k ^ 2 :=
    continuous_finset_sum _ fun k _ => ((continuous_apply k).comp ha).pow 2
  have cB : Continuous fun x => ∑ k, b x k ^ 2 :=
    continuous_finset_sum _ fun k _ => ((continuous_apply k).comp hb).pow 2
  have cC : Continuous fun x => dot (a x) (b x) :=
    continuous_finset_sum _ fun k _ => ((continuous_apply k).comp ha).mul
      ((continuous_apply k).comp hb)
  have e : ∀ x, ∑ k, (a x + r • b x) k ^ 2 =
      (∑ k, a x k ^ 2 + 2 * r * dot (a x) (b x)) + r ^ 2 * ∑ k, b x k ^ 2 := by
    intro x; simp [dot, Fin.sum_univ_two]; ring
  unfold l2sqV
  rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc fun x _ => e x,
    integral_add (f := fun x => ∑ k, a x k ^ 2 + 2 * r * dot (a x) (b x))
      (g := fun x => r ^ 2 * ∑ k, b x k ^ 2) ((i cA).add (i (continuous_const.mul cC)))
      (i (continuous_const.mul cB)),
    integral_add (f := fun x => ∑ k, a x k ^ 2) (g := fun x => 2 * r * dot (a x) (b x)) (i cA)
      (i (continuous_const.mul cC)), integral_const_mul, integral_const_mul]

lemma sqrt_l2sqV_add_le (a b : Pt 2 → Pt 2) (ha : Continuous a) (hb : Continuous b) :
    Real.sqrt (l2sqV (fun x => a x + b x)) ≤ Real.sqrt (l2sqV a) + Real.sqrt (l2sqV b) := by
  set A := l2sqV a
  set B := l2sqV b
  set C := ∫ x in cell 2, dot (a x) (b x)
  have hA : 0 ≤ A := setIntegral_nonneg measurableSet_Icc fun x _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ B := setIntegral_nonneg measurableSet_Icc fun x _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq : ∀ r : ℝ, 0 ≤ B * (r * r) + 2 * C * r + A := by
    intro r
    have := l2sqV_add_smul a b ha hb r
    have h0 : 0 ≤ l2sqV (fun x => a x + r • b x) := setIntegral_nonneg measurableSet_Icc
      fun x _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hC : C ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_mul hA]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have e1 := l2sqV_add_smul a b ha hb 1
  simp only [one_smul, mul_one, one_pow, one_mul] at e1
  rw [e1]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have := Real.sq_sqrt hA
  have := Real.sq_sqrt hB
  nlinarith


/-- Energy estimate for a perturbation `w` of a Navier–Stokes flow on `[a,b]`: if
`∂ₜw + u·∇w + w·∇B + ∇π = νΔw` with `‖∇B(s)‖_{L^∞,op} ≤ g(s)`, then
`‖w(t)‖₂² ≤ ‖w(a)‖₂² exp(2∫ₐᵗ g)`. -/
lemma perturbation_energy {a b : ℝ} (hab : a ≤ b) (ν : ℝ) (hν : 0 ≤ ν)
    (u w W' B : ℝ → Pt 2 → Pt 2) (pr : ℝ → Pt 2 → ℝ) (g : ℝ → ℝ)
    (hwc : ContinuousOn (fun p : ℝ × Pt 2 => w p.1 p.2) (Icc a b ×ˢ univ))
    (hW'c : ContinuousOn (fun p : ℝ × Pt 2 => W' p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => w r x) (W' s x) s)
    (hreg : ∀ s ∈ Ioo a b, ContDiff ℝ 1 (u s) ∧ IsPeriodic (u s) ∧
      (∀ x, divergence (u s) x = 0) ∧ ContDiff ℝ 2 (w s) ∧ IsPeriodic (w s) ∧
      (∀ x, divergence (w s) x = 0) ∧ ContDiff ℝ 1 (pr s) ∧ IsPeriodic (pr s) ∧
      ContDiff ℝ 1 (B s) ∧ ∀ x, eucOp (fderiv ℝ (B s) x) ≤ g s)
    (heq : ∀ s ∈ Ioo a b, ∀ x,
      W' s x + conv (u s) (w s) x + conv (w s) (B s) x + grad (pr s) x = ν • lap (w s) x)
    (hg : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b, l2sqV (w t) ≤ l2sqV (w a) * Real.exp (2 * ∫ s in a..t, g s) := by
  obtain ⟨hform, hcont⟩ := l2sqV_integral_form hab w W' hwc hW'c hd
  refine gronwall_of_integral hab hform hcont hg fun s hs => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hreg s hs
  exact spatial_energy_le ν (g s) hν (u s) (w s) (B s) (W' s) (pr s) h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 (heq s hs)


/-- Scalar version of `l2sqV_integral_form`. -/
lemma l2sq_integral_form {a b : ℝ} (hab : a ≤ b) (u u' : ℝ → Pt 2 → ℝ)
    (hu : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2) (Icc a b ×ˢ univ))
    (hu' : ContinuousOn (fun p : ℝ × Pt 2 => u' p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => u r x) (u' s x) s) :
    (∀ t ∈ Icc a b, l2sq (u t) = l2sq (u a) +
      ∫ s in a..t, ∫ x in cell 2, 2 * u s x * u' s x) ∧
    ContinuousOn (fun s => ∫ x in cell 2, 2 * u s x * u' s x) (Icc a b) := by
  set F : ℝ → Pt 2 → ℝ := fun s x => 2 * u s x * u' s x with hF
  have hFc : ContinuousOn (fun p : ℝ × Pt 2 => F p.1 p.2) (Icc a b ×ˢ univ) :=
    (continuousOn_const.mul hu).mul hu'
  have hEc : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2 ^ 2) (Icc a b ×ˢ univ) := hu.pow 2
  refine ⟨fun t ht => ?_, continuousOn_integral_cell' hab F hFc⟩
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hline : ∀ x, ∀ {G : ℝ → Pt 2 → ℝ},
      ContinuousOn (fun p : ℝ × Pt 2 => G p.1 p.2) (Icc a b ×ˢ univ) →
      ContinuousOn (fun s => G s x) (Icc a t) := fun x G hG =>
    hG.comp (Continuous.prodMk continuous_id continuous_const).continuousOn
      (fun s hs => ⟨hsub hs, mem_univ _⟩)
  have step1 : ∀ x, u t x ^ 2 - u a x ^ 2 = ∫ s in a..t, F s x := by
    intro x
    symm
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hline x (G := fun s x => u s x ^ 2) hEc) (fun s hs => ?_) ?_
    · have hsb : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
      refine HasDerivAt.hasDerivWithinAt ?_
      convert (hd s hsb x).pow 2 using 1
      simp only [hF]; ring
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1]
      exact hline x hFc
  have hcont : ∀ s ∈ Icc a b, Continuous (fun x => u s x ^ 2) := by
    intro s hs
    have : Continuous fun x : Pt 2 => ((s, x) : ℝ × Pt 2) := Continuous.prodMk continuous_const
      continuous_id
    exact hEc.comp_continuous this fun x => ⟨hs, mem_univ _⟩
  have step2 : l2sq (u t) - l2sq (u a) = ∫ x in cell 2, ∫ s in a..t, F s x := by
    rw [l2sq, l2sq, ← integral_sub (integrableOn_cell_of_continuous (hcont t ht))
      (integrableOn_cell_of_continuous (hcont a ⟨le_rfl, hab⟩))]
    exact setIntegral_congr_fun measurableSet_Icc fun x _ => step1 x
  have step3 : ∫ x in cell 2, ∫ s in a..t, F s x = ∫ s in a..t, ∫ x in cell 2, F s x := by
    simp only [intervalIntegral.integral_of_le ht.1]
    refine integral_integral_swap ?_
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : ContinuousOn (fun q : Pt 2 × ℝ => F q.2 q.1) (cell 2 ×ˢ Icc a t) :=
      hFc.comp continuous_swap.continuousOn (fun q hq => ⟨hsub hq.2, mem_univ _⟩)
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono subset_rfl Ioc_subset_Icc_self)
  linarith

/-- The vector field `u` applied to the gradient of `z`: `|u·∇z| ≤ |u| |∇z|`. -/
lemma conv_sq_le (u : Pt 2 → Pt 2) (z : Pt 2 → ℝ) (x : Pt 2) :
    conv u z x ^ 2 ≤ (∑ k, u x k ^ 2) * gradSq z x := by
  unfold conv gradSq
  simp only [Fin.sum_univ_two, smul_eq_mul]
  nlinarith [sq_nonneg (u x 0 * pd 1 z x - u x 1 * pd 0 z x)]

/-- Young's inequality in the form used for the transfer estimate. -/
lemma young_aux {ν M θ c g U : ℝ} (hν : 0 < ν) (hθ : |θ| ≤ M) (hc : c ^ 2 ≤ U * g)
    (hU : 0 ≤ U) (hg : 0 ≤ g) : 2 * (θ * c) ≤ 2 * ν * g + M ^ 2 / (2 * ν) * U := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hθ
  have h1 : 2 * (θ * c) ≤ 2 * (M * |c|) := by
    have := abs_mul θ c
    nlinarith [le_abs_self (θ * c), abs_nonneg c, abs_nonneg θ]
  have key : 4 * ν * (M * |c|) ≤ 4 * ν ^ 2 * g + M ^ 2 * U := by
    rcases hU.lt_or_eq with hU' | hU'
    · have hc' : |c| ^ 2 ≤ U * g := by rw [sq_abs]; exact hc
      have : U * (4 * ν * (M * |c|)) ≤ U * (4 * ν ^ 2 * g + M ^ 2 * U) := by
        nlinarith [sq_nonneg (M * U - 2 * ν * |c|), abs_nonneg c]
      exact le_of_mul_le_mul_left this hU'
    · subst hU'
      have : c = 0 := by nlinarith [sq_nonneg c]
      subst this; simp; positivity
  have h2 : 2 * (M * |c|) ≤ 2 * ν * g + M ^ 2 / (2 * ν) * U := by
    rw [div_mul_eq_mul_div, ← sub_nonneg]
    have : 2 * ν * g + M ^ 2 * U / (2 * ν) - 2 * (M * |c|) =
        (4 * ν ^ 2 * g + M ^ 2 * U - 4 * ν * (M * |c|)) / (2 * ν) := by field_simp; ring
    rw [this]; exact div_nonneg (by linarith) (by positivity)
  linarith

/-- Spatial energy inequality for the difference `z` of two scalars:
if `Z' + D·∇z + u·∇θ = νΔz` with `div u = div D = 0` and `|θ| ≤ M`, then
`∫ 2 z Z' ≤ (M²/(2ν)) ‖u‖₂²`. -/
lemma scalar_diff_energy_le (ν M : ℝ) (hν : 0 < ν) (D u : Pt 2 → Pt 2) (θ z Z' : Pt 2 → ℝ)
    (hD : ContDiff ℝ 1 D) (hDp : IsPeriodic D) (hDdiv : ∀ x, divergence D x = 0)
    (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u) (hudiv : ∀ x, divergence u x = 0)
    (hθ : ContDiff ℝ 1 θ) (hθp : IsPeriodic θ) (hθM : ∀ x, |θ x| ≤ M)
    (hz : ContDiff ℝ 2 z) (hzp : IsPeriodic z)
    (heq : ∀ x, Z' x + conv D z x + conv u θ x = ν * lap z x) :
    ∫ x in cell 2, 2 * z x * Z' x ≤ M ^ 2 / (2 * ν) * l2sqV u := by
  have hz1 : ContDiff ℝ 1 z := hz.of_le (by norm_num)
  have i := fun {F : Pt 2 → ℝ} (hF : Continuous F) => integrableOn_cell_of_continuous hF
  have huj : ∀ j : Fin 2, ContDiff ℝ 1 (fun y => u y j) := fun j => (contDiff_apply ℝ ℝ j).comp hu
  have hujp : ∀ j : Fin 2, IsPeriodic (fun y => u y j) := fun j x n => by simp [hup x n]
  have cl := continuous_lap_of_C2 z hz
  have cDz := continuous_conv_of_C1 D hD.continuous z hz1
  have cuθ := continuous_conv_of_C1 u hu.continuous θ hθ
  have cuz := continuous_conv_of_C1 u hu.continuous z hz1
  have cz := hz1.continuous
  have cθ := hθ.continuous
  -- integration by parts: `∫ z (u·∇θ) = -∫ θ (u·∇z)`
  have hibp : ∫ x in cell 2, z x * conv u θ x = -∫ x in cell 2, θ x * conv u z x := by
    have hzθ : ContDiff ℝ 1 (fun y => z y * θ y) := hz1.mul hθ
    have hF : ∀ j : Fin 2, ContDiff ℝ 1 (fun y => u y j * (z y * θ y)) := fun j => (huj j).mul hzθ
    have hpt : ∀ x, z x * conv u θ x + θ x * conv u z x =
        ∑ j : Fin 2, pd j (fun y => u y j * (z y * θ y)) x := by
      intro x
      have hd := hudiv x
      unfold divergence at hd
      simp only [← pd_component u x (hu.differentiable one_ne_zero x)] at hd
      have e : ∀ j : Fin 2, pd j (fun y => u y j * (z y * θ y)) x =
          pd j (fun y => u y j) x * (z x * θ x) + u x j * (pd j z x * θ x + z x * pd j θ x) := by
        intro j
        rw [pd_mul' _ _ x ((huj j).differentiable one_ne_zero x) (hzθ.differentiable one_ne_zero x),
          pd_mul' _ _ x (hz1.differentiable one_ne_zero x) (hθ.differentiable one_ne_zero x)]
      simp only [e, conv, smul_eq_mul, Fin.sum_univ_two] at hd ⊢
      linear_combination (-(z x * θ x)) * hd
    have h0 : ∫ x in cell 2, ∑ j : Fin 2, pd j (fun y => u y j * (z y * θ y)) x = 0 := by
      rw [integral_finset_sum (f := fun j x => pd j (fun y => u y j * (z y * θ y)) x) _
        fun j _ => i (continuous_pd_of_C1 _ (hF j) j)]
      exact Finset.sum_eq_zero fun j _ => integral_pd_periodic _ (hF j)
        (isPeriodic_mul _ _ (hujp j) (isPeriodic_mul _ _ hzp hθp)) j
    rw [← setIntegral_congr_fun (s := cell 2) measurableSet_Icc fun x _ => hpt x,
      integral_add (f := fun x => z x * conv u θ x) (g := fun x => θ x * conv u z x)
        (i (cz.mul cuθ)) (i (cθ.mul cuz))] at h0
    linarith
  have hlap := integral_mul_lap z hz hzp
  have hconv := integral_mul_conv D hD hDp hDdiv z hz1 hzp
  have e : ∀ x, 2 * z x * Z' x =
      2 * ν * (z x * lap z x) - 2 * (z x * conv D z x) - 2 * (z x * conv u θ x) := by
    intro x
    have := heq x
    have hZ : Z' x = ν * lap z x - conv D z x - conv u θ x := by linarith
    rw [hZ]; ring
  rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc fun x _ => e x,
    integral_sub (f := fun x => 2 * ν * (z x * lap z x) - 2 * (z x * conv D z x))
      (g := fun x => 2 * (z x * conv u θ x))
      ((i (continuous_const.mul (cz.mul cl))).sub (i (continuous_const.mul (cz.mul cDz))))
      (i (continuous_const.mul (cz.mul cuθ))),
    integral_sub (f := fun x => 2 * ν * (z x * lap z x)) (g := fun x => 2 * (z x * conv D z x))
      (i (continuous_const.mul (cz.mul cl))) (i (continuous_const.mul (cz.mul cDz))),
    integral_const_mul, integral_const_mul, integral_const_mul, hlap, hconv, hibp]
  -- Young's inequality
  have cg : Continuous (gradSq z) := continuous_finset_sum _ fun k _ =>
    (continuous_pd_of_C1 z hz1 k).pow 2
  have cU : Continuous fun x => ∑ k, u x k ^ 2 := continuous_finset_sum _ fun k _ =>
    ((continuous_apply k).comp hu.continuous).pow 2
  have hY : ∫ x in cell 2, 2 * (θ x * conv u z x) ≤
      ∫ x in cell 2, (2 * ν * gradSq z x + M ^ 2 / (2 * ν) * ∑ k, u x k ^ 2) := by
    refine setIntegral_mono_on (i (continuous_const.mul (cθ.mul cuz)))
      (i ((continuous_const.mul cg).add (continuous_const.mul cU))) measurableSet_Icc
      fun x _ => ?_
    exact young_aux hν (hθM x) (conv_sq_le u z x)
      (Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  rw [integral_add (f := fun x => 2 * ν * gradSq z x)
      (g := fun x => M ^ 2 / (2 * ν) * ∑ k, u x k ^ 2) (i (continuous_const.mul cg))
      (i (continuous_const.mul cU)), integral_const_mul, integral_const_mul,
    integral_const_mul] at hY
  unfold l2sqV
  linarith

end AnomDiss
