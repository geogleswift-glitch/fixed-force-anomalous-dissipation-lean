module

public import RequestProject.ScalarSchauderSpatial
public import RequestProject.HeatDuhamelClassical
public import RequestProject.HeatHolderFirstOrder

/-!
# Time Hölder continuity of the actual heat Duhamel Hessian

The genuine evolution cocycle separates an old heat-evolved Hessian from
the new source interval. Spatial Schauder regularity controls the first
increment, and the cancelled Hessian bound controls the second. No time
Hölder regularity or time derivative of the source is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- The new source interval in the true cocycle is a Duhamel term for the
time-shifted original source. -/
theorem heatDuhamel_cocycle_shifted_source {ν t h : ℝ}
    (hν : 0 ≤ ν) (ht : 0 ≤ t) (hh : 0 ≤ h)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    {C : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C) :
    heatDuhamel ν F (t + h) = fun x =>
      heatOp (Real.toNNReal (2 * ν * h)) (heatDuhamel ν F t) x +
        heatDuhamel ν (fun r => F (t + r)) h x := by
  funext x
  rw [heatDuhamel_cocycle hν ht hh hF hC, heatDuhamel_short_interval_eq]
  rfl

/-- The short source interval has a Hessian bounded by its cancelled
integrable heat singularity. -/
theorem norm_pd2_heatDuhamel_holder_le {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i j : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    ‖pd i (pd j (heatDuhamel ν F t)) x‖ ≤
      (2 * duhamelSpaceDerivativeScale ν H β / β) * t ^ (β / 2) := by
  have he : pd j (heatDuhamel ν F t) = duhamelComponent ν F j t :=
    funext (pd_heatDuhamel_eq_duhamelComponent hν hF hp hC ht j)
  rw [he]
  calc
    ‖pd i (duhamelComponent ν F j t) x‖ =
        ‖fderiv ℝ (duhamelComponent ν F j t) x (Pi.single i 1)‖ := rfl
    _ ≤ ‖fderiv ℝ (duhamelComponent ν F j t) x‖ * ‖(Pi.single i 1 : Pt 2)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (duhamelComponent ν F j t) x‖ := by simp [Pi.norm_single]
    _ ≤ _ := norm_fderiv_duhamelComponent_holder_le hν hF hp hC hH hβ hholder j ht x

lemma pd2_add_fun_C2 (f g : Pt 2 → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (i j : Fin 2) :
    pd i (pd j (fun x => f x + g x)) =
      fun x => pd i (pd j f) x + pd i (pd j g) x := by
  rw [pd_add_fun f g j (hf.differentiable (by norm_num))
    (hg.differentiable (by norm_num))]
  exact pd_add_fun _ _ i ((contDiff_pd_of_C2 f hf j).differentiable one_ne_zero)
    ((contDiff_pd_of_C2 g hg j).differentiable one_ne_zero)

def duhamelHessianTimeHolderScale (ν H β : ℝ) : ℝ :=
  2 * (4 * duhamelSpaceDerivativeScale ν H β / β +
    2 * duhamelThirdDerivativeScale ν H β / (1 - β)) *
      gmom β * (2 * ν) ^ (β / 2) + 2 * duhamelSpaceDerivativeScale ν H β / β

/-- The actual Hessian has the parabolic time increment bound, uniformly
over all nonnegative base times and increments. -/
theorem pd2_heatDuhamel_time_increment_holder_le {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i j : Fin 2) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (x : Pt 2) :
    ‖pd i (pd j (heatDuhamel ν F (t + h))) x - pd i (pd j (heatDuhamel ν F t)) x‖ ≤
      duhamelHessianTimeHolderScale ν H β * h ^ (β / 2) := by
  let G : ℝ → Pt 2 → ℂ := fun r => F (t + r)
  let v := Real.toNNReal (2 * ν * h)
  let K := 4 * duhamelSpaceDerivativeScale ν H β / β +
    2 * duhamelThirdDerivativeScale ν H β / (1 - β)
  have hG : Continuous (Function.uncurry G) := hF.comp
    (by fun_prop : Continuous (fun p : ℝ × Pt 2 => (t + p.1, p.2)))
  have hGp : ∀ r, IsPeriodic (G r) := fun r => hp (t + r)
  have hGC : ∀ r y, ‖G r y‖ ≤ C := fun r y => hC (t + r) y
  have hGH : ∀ r y z, ‖G r y - G r z‖ ≤ H * ‖y - z‖ ^ β :=
    fun r y z => hholder (t + r) y z
  have ht2 : ContDiff ℝ 2 (heatDuhamel ν F t) :=
    contDiff_two_heatDuhamel_holder hν hF hp hC hH hβ0 hholder ht
  have hh2 : ContDiff ℝ 2 (heatDuhamel ν G h) :=
    contDiff_two_heatDuhamel_holder hν hG hGp hGC hH hβ0 hGH hh
  have htp : IsPeriodic (heatDuhamel ν F t) := heatDuhamel_periodic ν hp t
  have hheat2 : ContDiff ℝ 2 (heatOp v (heatDuhamel ν F t)) :=
    contDiff_heatOp (isQP_zero_iff.2 htp) ht2 v
  have he : pd i (pd j (heatDuhamel ν F (t + h))) x =
      heatOp v (pd i (pd j (heatDuhamel ν F t))) x +
        pd i (pd j (heatDuhamel ν G h)) x := by
    rw [heatDuhamel_cocycle_shifted_source hν.le ht hh hF hC,
      pd2_add_fun_C2 _ _ hheat2 hh2 i j]
    dsimp only
    rw [pd2_heatOp (isQP_zero_iff.2 htp) ht2 v i j x]
  have hscale := duhamelSpaceDerivativeScale_nonneg hν.le hH (β := β)
  have hthird := duhamelThirdDerivativeScale_nonneg hν.le hH (β := β)
  have hK : 0 ≤ K := add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hscale) hβ0.le)
    (div_nonneg (mul_nonneg (by norm_num) hthird) (by linarith))
  have hc : Continuous (pd i (pd j (heatDuhamel ν F t))) :=
    continuous_pd_of_C1 _ (contDiff_pd_of_C2 _ ht2 j) i
  have hper : IsPeriodic (pd i (pd j (heatDuhamel ν F t))) :=
    isPeriodic_pd _ (isPeriodic_pd _ htp j) i
  obtain ⟨B, hB⟩ := (isQP_zero_iff.2 hper).bdd hc
  have herror := heatOp_holder_initial_error hc hB hβ0 hK
    (fun y z => pd2_heatDuhamel_spatial_schauder hν hF hp hC hH hβ0 hβ1
      hholder i j ht y z) v x
  have hv : (v : ℝ) = (2 * ν) * h := by
    change (Real.toNNReal (2 * ν * h) : ℝ) = _
    rw [Real.coe_toNNReal _ (by positivity)]
  rw [hv, Real.mul_rpow (by positivity : 0 ≤ 2 * ν) hh] at herror
  have hshort := norm_pd2_heatDuhamel_holder_le hν hG hGp hGC hH hβ0 hGH i j hh x
  rw [he]
  calc
    ‖heatOp v (pd i (pd j (heatDuhamel ν F t))) x +
        pd i (pd j (heatDuhamel ν G h)) x - pd i (pd j (heatDuhamel ν F t)) x‖
        = ‖(heatOp v (pd i (pd j (heatDuhamel ν F t))) x -
          pd i (pd j (heatDuhamel ν F t)) x) + pd i (pd j (heatDuhamel ν G h)) x‖ := by
      congr 1
      abel
    _ ≤ ‖heatOp v (pd i (pd j (heatDuhamel ν F t))) x -
          pd i (pd j (heatDuhamel ν F t)) x‖ + ‖pd i (pd j (heatDuhamel ν G h)) x‖ :=
      norm_add_le _ _
    _ ≤ 2 * K * gmom β * ((2 * ν) ^ (β / 2) * h ^ (β / 2)) +
        (2 * duhamelSpaceDerivativeScale ν H β / β) * h ^ (β / 2) :=
      add_le_add herror hshort
    _ = _ := by unfold duhamelHessianTimeHolderScale; dsimp [K]; ring

/-- Every actual heat Duhamel Hessian entry is `β/2`-Hölder in time on
the complete closed time slab, uniformly in space. -/
theorem timeHolder_pd2_heatDuhamel_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (T : ℝ) (i j : Fin 2) :
    TimeHolder T (β / 2) (fun t => pd i (pd j (heatDuhamel ν F t))) := by
  refine ⟨duhamelHessianTimeHolderScale ν H β, fun t ht s hs x => ?_⟩
  rcases le_total s t with hst | hts
  · have he : s + (t - s) = t := by ring
    have hb := pd2_heatDuhamel_time_increment_holder_le hν hF hp hC hH hβ0 hβ1
      hholder i j hs.1 (sub_nonneg.2 hst) x
    simpa only [he, abs_of_nonneg (sub_nonneg.2 hst)] using hb
  · have he : t + (s - t) = s := by ring
    calc
      ‖pd i (pd j (heatDuhamel ν F t)) x - pd i (pd j (heatDuhamel ν F s)) x‖ =
          ‖pd i (pd j (heatDuhamel ν F s)) x - pd i (pd j (heatDuhamel ν F t)) x‖ :=
        norm_sub_rev _ _
      _ ≤ duhamelHessianTimeHolderScale ν H β * (s - t) ^ (β / 2) := by
        simpa only [he] using pd2_heatDuhamel_time_increment_holder_le hν hF hp hC hH hβ0 hβ1
          hholder i j ht.1 (sub_nonneg.2 hts) x
      _ = _ := by rw [abs_sub_comm t s, abs_of_nonneg (sub_nonneg.2 hts)]

lemma integral_gradient_holder_rpow {β t : ℝ} (hβ : 0 < β) :
    (∫ r in (0 : ℝ)..t, r ^ ((β - 1) / 2)) =
      2 / (β + 1) * t ^ ((β + 1) / 2) := by
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < (β - 1) / 2))]
  have he : (β - 1) / 2 + 1 = (β + 1) / 2 := by ring
  rw [he, Real.zero_rpow (by positivity : (β + 1) / 2 ≠ (0 : ℝ)), sub_zero]
  field_simp

/-- The gradient of the new source interval gains the time power
`(1+β)/2` from spatial source cancellation. -/
theorem norm_pd_heatDuhamel_holder_le {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (x : Pt 2) :
    ‖pd i (heatDuhamel ν F t) x‖ ≤
      (4 * H * gmom (β + 1) * (2 * ν) ^ ((β - 1) / 2) / (β + 1)) *
        t ^ ((β + 1) / 2) := by
  rw [pd_heatDuhamel_eq_duhamelComponent hν hF hp hC ht i x,
    duhamelComponent_eq_lagged]
  let A := 2 * H * gmom (β + 1) * (2 * ν) ^ ((β - 1) / 2)
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t)
    (show (-1 : ℝ) < (β - 1) / 2 by linarith)).const_mul A
  have hbound : ∀ r, 0 < r →
      ‖laggedDuhamelKernel ν F i (t, x) r‖ ≤ A * r ^ ((β - 1) / 2) := by
    intro r hr
    have hfc : Continuous (F (t - r)) := hF.comp (continuous_const.prodMk continuous_id)
    have hv : 0 < (Real.toNNReal (2 * ν * r) : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity)]
      positivity
    have hb := norm_heatGradientKernel_holder_le hfc (hC (t - r)) hH hβ
      (hholder (t - r)) hv i x
    unfold laggedDuhamelKernel
    apply hb.trans_eq
    rw [Real.coe_toNNReal _ (by positivity), Real.mul_rpow (by positivity : 0 ≤ 2 * ν) hr.le]
    dsimp [A]
    ring
  calc
    ‖∫ r in (0 : ℝ)..t, laggedDuhamelKernel ν F i (t, x) r‖ ≤
        ∫ r in (0 : ℝ)..t, A * r ^ ((β - 1) / 2) :=
      intervalIntegral.norm_integral_le_of_norm_le ht
        (Eventually.of_forall fun r hr => hbound r hr.1) hi
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_gradient_holder_rpow hβ]
      dsimp [A]
      ring

def duhamelGradientTimeHolderScale (ν H β : ℝ) : ℝ :=
  4 * (4 * duhamelSpaceDerivativeScale ν H β / β +
    2 * duhamelThirdDerivativeScale ν H β / (1 - β)) *
      gmom (1 + β) * (2 * ν) ^ ((1 + β) / 2) +
    4 * H * gmom (1 + β) * (2 * ν) ^ ((β - 1) / 2) / (1 + β)

/-- The true gradient cocycle gains the larger time exponent `(1+β)/2`
through first-order Gaussian cancellation of the old spatial gradient. -/
theorem pd_heatDuhamel_time_increment_holder_le {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i : Fin 2) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (x : Pt 2) :
    ‖pd i (heatDuhamel ν F (t + h)) x - pd i (heatDuhamel ν F t) x‖ ≤
      duhamelGradientTimeHolderScale ν H β * h ^ ((1 + β) / 2) := by
  let G : ℝ → Pt 2 → ℂ := fun r => F (t + r)
  let v := Real.toNNReal (2 * ν * h)
  let K := 4 * duhamelSpaceDerivativeScale ν H β / β +
    2 * duhamelThirdDerivativeScale ν H β / (1 - β)
  have hG : Continuous (Function.uncurry G) := hF.comp
    (by fun_prop : Continuous (fun p : ℝ × Pt 2 => (t + p.1, p.2)))
  have hGp : ∀ r, IsPeriodic (G r) := fun r => hp (t + r)
  have hGC : ∀ r y, ‖G r y‖ ≤ C := fun r y => hC (t + r) y
  have hGH : ∀ r y z, ‖G r y - G r z‖ ≤ H * ‖y - z‖ ^ β :=
    fun r y z => hholder (t + r) y z
  have ht2 : ContDiff ℝ 2 (heatDuhamel ν F t) :=
    contDiff_two_heatDuhamel_holder hν hF hp hC hH hβ0 hholder ht
  have hh2 : ContDiff ℝ 2 (heatDuhamel ν G h) :=
    contDiff_two_heatDuhamel_holder hν hG hGp hGC hH hβ0 hGH hh
  have htp : IsPeriodic (heatDuhamel ν F t) := heatDuhamel_periodic ν hp t
  have hheat2 : ContDiff ℝ 2 (heatOp v (heatDuhamel ν F t)) :=
    contDiff_heatOp (isQP_zero_iff.2 htp) ht2 v
  have he : pd i (heatDuhamel ν F (t + h)) x =
      heatOp v (pd i (heatDuhamel ν F t)) x + pd i (heatDuhamel ν G h) x := by
    rw [heatDuhamel_cocycle_shifted_source hν.le ht hh hF hC,
      pd_add_fun _ _ i (hheat2.differentiable (by norm_num))
        (hh2.differentiable (by norm_num))]
    dsimp only
    rw [pd_heatOp_C1 (isQP_zero_iff.2 htp) (ht2.of_le (by norm_num)) v i x]
  have hscale := duhamelSpaceDerivativeScale_nonneg hν.le hH (β := β)
  have hthird := duhamelThirdDerivativeScale_nonneg hν.le hH (β := β)
  have hK : 0 ≤ K := add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hscale) hβ0.le)
    (div_nonneg (mul_nonneg (by norm_num) hthird) (by linarith))
  have hc1 : ContDiff ℝ 1 (pd i (heatDuhamel ν F t)) := contDiff_pd_of_C2 _ ht2 i
  have hper : IsPeriodic (pd i (heatDuhamel ν F t)) := isPeriodic_pd _ htp i
  obtain ⟨B, hB⟩ := (isQP_zero_iff.2 hper).bdd hc1.continuous
  have herror := heatOp_C1_holder_initial_error hc1 hB hK hβ0.le
    (fun k y z => pd2_heatDuhamel_spatial_schauder hν hF hp hC hH hβ0 hβ1
      hholder k i ht y z) v x
  have hv : (v : ℝ) = (2 * ν) * h := by
    change (Real.toNNReal (2 * ν * h) : ℝ) = _
    rw [Real.coe_toNNReal _ (by positivity)]
  rw [hv, Real.mul_rpow (by positivity : 0 ≤ 2 * ν) hh] at herror
  have hshort : ‖pd i (heatDuhamel ν G h) x‖ ≤
      (4 * H * gmom (1 + β) * (2 * ν) ^ ((β - 1) / 2) / (1 + β)) *
        h ^ ((1 + β) / 2) := by
    simpa only [add_comm β 1] using
      norm_pd_heatDuhamel_holder_le hν hG hGp hGC hH hβ0 hGH i hh x
  rw [he]
  calc
    ‖heatOp v (pd i (heatDuhamel ν F t)) x + pd i (heatDuhamel ν G h) x -
        pd i (heatDuhamel ν F t) x‖ =
        ‖(heatOp v (pd i (heatDuhamel ν F t)) x - pd i (heatDuhamel ν F t) x) +
          pd i (heatDuhamel ν G h) x‖ := by congr 1; abel
    _ ≤ ‖heatOp v (pd i (heatDuhamel ν F t)) x - pd i (heatDuhamel ν F t) x‖ +
        ‖pd i (heatDuhamel ν G h) x‖ := norm_add_le _ _
    _ ≤ 4 * K * gmom (1 + β) * ((2 * ν) ^ ((1 + β) / 2) * h ^ ((1 + β) / 2)) +
        (4 * H * gmom (1 + β) * (2 * ν) ^ ((β - 1) / 2) / (1 + β)) *
          h ^ ((1 + β) / 2) := add_le_add herror hshort
    _ = _ := by unfold duhamelGradientTimeHolderScale; dsimp [K]; ring

/-- Every actual heat Duhamel spatial gradient component has time Hölder
exponent `(1+β)/2`, uniformly in space on the whole closed slab. -/
theorem timeHolder_pd_heatDuhamel_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (T : ℝ) (i : Fin 2) :
    TimeHolder T ((1 + β) / 2) (fun t => pd i (heatDuhamel ν F t)) := by
  refine ⟨duhamelGradientTimeHolderScale ν H β, fun t ht s hs x => ?_⟩
  rcases le_total s t with hst | hts
  · have he : s + (t - s) = t := by ring
    have hb := pd_heatDuhamel_time_increment_holder_le hν hF hp hC hH hβ0 hβ1
      hholder i hs.1 (sub_nonneg.2 hst) x
    simpa only [he, abs_of_nonneg (sub_nonneg.2 hst)] using hb
  · have he : t + (s - t) = s := by ring
    calc
      ‖pd i (heatDuhamel ν F t) x - pd i (heatDuhamel ν F s) x‖ =
          ‖pd i (heatDuhamel ν F s) x - pd i (heatDuhamel ν F t) x‖ := norm_sub_rev _ _
      _ ≤ duhamelGradientTimeHolderScale ν H β * (s - t) ^ ((1 + β) / 2) := by
        simpa only [he] using pd_heatDuhamel_time_increment_holder_le hν hF hp hC hH hβ0 hβ1
          hholder i ht.1 (sub_nonneg.2 hts) x
      _ = _ := by rw [abs_sub_comm t s, abs_of_nonneg (sub_nonneg.2 hts)]

end AnomDiss
