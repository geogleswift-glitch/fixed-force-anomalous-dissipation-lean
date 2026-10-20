module

public import RequestProject.KernelDrift

/-!
# Heat decay of Fourier coefficients

For a classical solution of the heat equation `∂ₜu = νΔu` on `[0,T] × 𝕋²`, every Fourier
coefficient is multiplied by `e^{-4π²ν|m|²T}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- Time-integrated form of `d/dt ∫ U(t) = ∫ ∂ₜU(t)` on the cell. -/
lemma cell_integral_form {a b : ℝ} (hab : a ≤ b) (U U' : ℝ → Pt 2 → ℝ)
    (hU : ContinuousOn (fun p : ℝ × Pt 2 => U p.1 p.2) (Icc a b ×ˢ univ))
    (hU' : ContinuousOn (fun p : ℝ × Pt 2 => U' p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => U r x) (U' s x) s) :
    ∀ t ∈ Icc a b, ∫ x in cell 2, U t x =
      (∫ x in cell 2, U a x) + ∫ s in a..t, ∫ x in cell 2, U' s x := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hline : ∀ x, ∀ {G : ℝ → Pt 2 → ℝ},
      ContinuousOn (fun p : ℝ × Pt 2 => G p.1 p.2) (Icc a b ×ˢ univ) →
      ContinuousOn (fun s => G s x) (Icc a t) := fun x G hG =>
    hG.comp (Continuous.prodMk continuous_id continuous_const).continuousOn
      (fun s hs => ⟨hsub hs, mem_univ _⟩)
  have step1 : ∀ x, U t x - U a x = ∫ s in a..t, U' s x := by
    intro x
    symm
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hline x hU) (fun s hs => ?_) ?_
    · exact (hd s ⟨hs.1, hs.2.trans_le ht.2⟩ x).hasDerivWithinAt
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1]
      exact hline x hU'
  have hcont : ∀ s ∈ Icc a b, Continuous (fun x => U s x) := by
    intro s hs
    have : Continuous fun x : Pt 2 => ((s, x) : ℝ × Pt 2) := Continuous.prodMk continuous_const
      continuous_id
    exact hU.comp_continuous this fun x => ⟨hs, mem_univ _⟩
  have step2 : (∫ x in cell 2, U t x) - ∫ x in cell 2, U a x =
      ∫ x in cell 2, ∫ s in a..t, U' s x := by
    rw [← integral_sub (integrableOn_cell_of_continuous (hcont t ht))
      (integrableOn_cell_of_continuous (hcont a ⟨le_rfl, hab⟩))]
    exact setIntegral_congr_fun measurableSet_Icc fun x _ => step1 x
  have step3 : ∫ x in cell 2, ∫ s in a..t, U' s x = ∫ s in a..t, ∫ x in cell 2, U' s x := by
    simp only [intervalIntegral.integral_of_le ht.1]
    refine integral_integral_swap ?_
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : ContinuousOn (fun q : Pt 2 × ℝ => U' q.2 q.1) (cell 2 ×ˢ Icc a t) :=
      hU'.comp continuous_swap.continuousOn (fun q hq => ⟨hsub hq.2, mem_univ _⟩)
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono subset_rfl Ioc_subset_Icc_self)
  linarith

/-- The linear integral equation `a(t) = a(0) - k ∫₀ᵗ a` forces `a(T) = e^{-kT} a(0)`. -/
lemma ode_exp_decay {T k : ℝ} (hT : 0 ≤ T) {a : ℝ → ℝ} (hc : ContinuousOn a (Icc 0 T))
    (h : ∀ t ∈ Icc 0 T, a t = a 0 + ∫ s in (0 : ℝ)..t, -k * a s) :
    a T = Real.exp (-k * T) * a 0 := by
  have hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt a (-k * a t) t := by
    intro t ht
    have hk : ContinuousOn (fun s => -k * a s) (Icc 0 T) := continuousOn_const.mul hc
    have hnhds : Icc 0 T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hI := intervalIntegral.integral_hasDerivAt_right
      ((hk.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      ((hk.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hk.continuousAt hnhds)
    refine (hI.const_add (a 0)).congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with s hs using h s hs
  set φ : ℝ → ℝ := fun t => Real.exp (k * t) * a t with hφ
  have hφc : ContinuousOn φ (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hc
  have hφd : ∀ t ∈ Ioo 0 T, HasDerivAt φ 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Real.exp (k * t)) (Real.exp (k * t) * k) t := by
      simpa using ((hasDerivAt_id t).const_mul k).exp
    convert h1.mul (hderiv t ht) using 1
    ring
  have hdiff : DifferentiableOn ℝ φ (interior (Icc 0 T)) := by
    rw [interior_Icc]; exact fun t ht => (hφd t ht).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hφc hdiff (by
    rw [interior_Icc]; intro t ht; rw [(hφd t ht).deriv])
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hφc hdiff (by
    rw [interior_Icc]; intro t ht; rw [(hφd t ht).deriv])
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTm : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have heq : φ T = φ 0 := le_antisymm (hanti h0 hTm hT) (hmono h0 hTm hT)
  simp only [hφ, mul_zero, Real.exp_zero, one_mul] at heq
  calc a T = Real.exp (-k * T) * (Real.exp (k * T) * a T) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ = _ := by rw [heq]

/-- `∫ g Δu = ∫ (Δg) u` for `C²` periodic functions. -/
lemma integral_mul_lap_symm (g u : Pt 2 → ℝ) (hg : ContDiff ℝ 2 g) (hu : ContDiff ℝ 2 u)
    (hgp : IsPeriodic g) (hup : IsPeriodic u) :
    ∫ x in cell 2, g x * lap u x = ∫ x in cell 2, lap g x * u x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  unfold lap
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum (f := fun i x => g x * pd i (pd i u) x) _
      (fun i _ => integrableOn_cell_of_continuous (hg1.continuous.mul (continuous_pd_of_C1 _ (contDiff_pd_of_C2 u hu i) i))),
    integral_finset_sum (f := fun i x => pd i (pd i g) x * u x) _
      (fun i _ => integrableOn_cell_of_continuous
      ((continuous_pd_of_C1 _ (contDiff_pd_of_C2 g hg i) i).mul hu1.continuous))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_pd g (pd i u) hg1 (contDiff_pd_of_C2 u hu i) hgp (isPeriodic_pd u hup i)]
  have := integral_mul_pd (pd i g) u (contDiff_pd_of_C2 g hg i) hu1 (isPeriodic_pd g hgp i) hup i
  have e : ∫ x in cell 2, pd i g x * pd i u x = -∫ x in cell 2, pd i (pd i g) x * u x := this
  rw [e, neg_neg]

/-- A real eigenfunction `Δg = -λg` tested against a heat solution decays like `e^{-νλt}`. -/
lemma heat_test_decay {T ν lam : ℝ} (hT : 0 ≤ T) (h : Pt 2 → ℝ) (u : ℝ → Pt 2 → ℝ)
    (hu : IsClassicalScalar T ν (fun _ _ => 0) h u) (g : Pt 2 → ℝ) (hg : ContDiff ℝ 2 g)
    (hgp : IsPeriodic g) (hlap : ∀ x, lap g x = -lam * g x) :
    ∫ x in cell 2, u T x * g x = Real.exp (-(ν * lam) * T) * ∫ x in cell 2, h x * g x := by
  obtain ⟨β, hβ0, -, reg⟩ := hu.regular
  set a : ℝ → ℝ := fun t => ∫ x in cell 2, u t x * g x with ha
  have hUc : ContinuousOn (fun p : ℝ × Pt 2 => u p.1 p.2 * g p.2) (Icc 0 T ×ˢ univ) :=
    reg.continuousOn.mul (hg.continuous.comp continuous_snd).continuousOn
  have hU'c : ContinuousOn (fun p : ℝ × Pt 2 => dt T u p.1 p.2 * g p.2) (Icc 0 T ×ˢ univ) :=
    (reg.holder_dt.continuousOn hβ0).mul (hg.continuous.comp continuous_snd).continuousOn
  have hd : ∀ s ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => u r x * g x) (dt T u s x * g x) s := by
    intro s hs x
    have h1 : HasDerivAt (fun r => u r x) (dt T u s x) s :=
      (reg.diff_t x s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)
    exact h1.mul_const _
  have hform := cell_integral_form hT _ _ hUc hU'c hd
  have hrate : ∀ s ∈ Icc 0 T, ∫ x in cell 2, dt T u s x * g x = -(ν * lam) * a s := by
    intro s hs
    have he : ∀ x, dt T u s x = ν * lap (u s) x := by
      intro x
      have := hu.eqn s hs x
      simp only [conv, smul_eq_mul] at this
      simpa [Pi.zero_apply] using this
    simp only [he]
    have hsym := integral_mul_lap_symm g (u s) hg (reg.smooth_x s hs) hgp (hu.periodic s hs)
    calc ∫ x in cell 2, ν * lap (u s) x * g x
        = ν * ∫ x in cell 2, g x * lap (u s) x := by
          rw [← integral_const_mul]; congr 1; funext x; ring
      _ = ν * ∫ x in cell 2, lap g x * u s x := by rw [hsym]
      _ = -(ν * lam) * a s := by
          simp only [hlap, ha]
          rw [← integral_const_mul, ← integral_const_mul]; congr 1; funext x; ring
  have hac : ContinuousOn a (Icc 0 T) := continuousOn_integral_cell hT _ hUc
  have hint : ∀ t ∈ Icc 0 T, a t = a 0 + ∫ s in (0 : ℝ)..t, -(ν * lam) * a s := by
    intro t ht
    show (∫ x in cell 2, u t x * g x) = (∫ x in cell 2, u 0 x * g x) + _
    rw [hform t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    exact hrate s ⟨hs.1, hs.2.trans ht.2⟩
  have := ode_exp_decay hT hac hint
  simp only [ha, hu.init] at this
  exact this

lemma pd_expChar (ξ : Pt 2) (i : Fin 2) (x : Pt 2) :
    pd i (expChar ξ) x = (2 * π * Complex.I * ξ i) * expChar ξ x := by
  have hd : DifferentiableAt ℝ (expChar ξ) (x + (0 : ℝ) • eb i) :=
    (contDiff_expChar ξ).differentiable (by simp) _
  have h1 := hasDerivAt_line (expChar ξ) x i 0 hd
  simp only [zero_smul, add_zero] at h1
  have e : (fun r : ℝ => expChar ξ (x + r • eb i)) =
      fun r : ℝ => expChar ξ x * Complex.exp (2 * π * Complex.I * ξ i * r) := by
    funext r
    rw [expChar_add_right]
    congr 1
    unfold expChar
    congr 1
    simp only [dot, eb, Fin.sum_univ_two]
    fin_cases i <;> simp <;> ring
  rw [e] at h1
  have h2 : HasDerivAt (fun r : ℝ => expChar ξ x * Complex.exp (2 * π * Complex.I * ξ i * r))
      (expChar ξ x * (Complex.exp (2 * π * Complex.I * ξ i * (0:ℝ)) * (2 * π * Complex.I * ξ i)))
      0 := by
    have h3 : HasDerivAt (fun r : ℝ => (2 * π * Complex.I * ξ i) * (r : ℂ))
        (2 * π * Complex.I * ξ i) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).const_mul (2 * π * Complex.I * ξ i)
    exact (h3.cexp).const_mul _
  rw [h1.unique h2]
  simp; ring

lemma pd_mul_const_complex (f : Pt 2 → ℂ) (c : ℂ) (i : Fin 2) (hf : Differentiable ℝ f) :
    pd i (fun y => c * f y) = fun x => c * pd i f x := by
  have := pd_clm_fun (ContinuousLinearMap.mul ℝ ℂ c) f i hf
  simpa using this

lemma pd_pd_expChar (ξ : Pt 2) (i : Fin 2) :
    pd i (pd i (expChar ξ)) = fun x => (2 * π * Complex.I * ξ i) ^ 2 * expChar ξ x := by
  have e1 : pd i (expChar ξ) = fun x => (2 * π * Complex.I * ξ i) * expChar ξ x :=
    funext (pd_expChar ξ i)
  rw [e1, pd_mul_const_complex _ _ i ((contDiff_expChar ξ).differentiable (by simp))]
  funext x; rw [pd_expChar]; ring

lemma lap_re_expChar (m : Fin 2 → ℤ) (L : ℂ →L[ℝ] ℝ) (x : Pt 2) :
    lap (fun y => L (expChar (intVec m) y)) x =
      -(4 * π ^ 2 * euclNorm (intVec m) ^ 2) * L (expChar (intVec m) x) := by
  have hd : Differentiable ℝ (expChar (intVec m)) := (contDiff_expChar _).differentiable (by simp)
  have hd2 : ∀ i, Differentiable ℝ (pd i (expChar (intVec m))) := fun i =>
    differentiable_pd ((contDiff_expChar _).of_le (by norm_cast)) i
  have h1 : ∀ i, pd i (fun y => L (expChar (intVec m) y)) =
      fun y => L (pd i (expChar (intVec m)) y) := fun i => pd_clm_fun L _ i hd
  have h2 : ∀ i, pd i (pd i (fun y => L (expChar (intVec m) y))) =
      fun y => L (pd i (pd i (expChar (intVec m))) y) := fun i => by
    rw [h1 i]; exact pd_clm_fun L _ i (hd2 i)
  unfold lap
  simp only [h2, pd_pd_expChar, Fin.sum_univ_two]
  have hn : euclNorm (intVec m) ^ 2 = (m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2 := by
    unfold euclNorm
    rw [Real.sq_sqrt (by positivity), Fin.sum_univ_two]; simp [intVec]
  rw [hn]
  have hc : ∀ i : Fin 2, (2 * π * Complex.I * (intVec m i : ℂ)) ^ 2 =
      ((-(4 * π ^ 2 * (m i : ℝ) ^ 2) : ℝ) : ℂ) := by
    intro i
    simp only [intVec]
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  rw [hc 0, hc 1]
  have hL : ∀ (r : ℝ) (z : ℂ), L ((r : ℂ) * z) = r * L z := fun r z => by
    rw [← Complex.real_smul, map_smul, smul_eq_mul]
  rw [hL, hL]; ring

/-- For a classical solution of the heat equation on `[0,T]`, each Fourier coefficient decays by
the factor `e^{-4π²ν|m|²T}`. -/
lemma heat_fourier {T ν : ℝ} (hT : 0 ≤ T) (h : Pt 2 → ℝ) (u : ℝ → Pt 2 → ℝ)
    (hu : IsClassicalScalar T ν (fun _ _ => 0) h u) (m : Fin 2 → ℤ) :
    fc (fun x => (u T x : ℂ)) m =
      Real.exp (-(4 * π ^ 2 * ν * T * euclNorm (intVec m) ^ 2)) * fc (fun x => (h x : ℂ)) m := by
  obtain ⟨β, -, -, reg⟩ := hu.regular
  have huT : Continuous (u T) := (reg.smooth_x T ⟨hT, le_rfl⟩).continuous
  have hh : Continuous h := by
    rw [← hu.init]; exact (reg.smooth_x 0 ⟨le_rfl, hT⟩).continuous
  set lam := 4 * π ^ 2 * euclNorm (intVec m) ^ 2 with hlam
  have hdec : ∀ L : ℂ →L[ℝ] ℝ, ∫ x in cell 2, u T x * L (expChar (intVec m) x) =
      Real.exp (-(ν * lam) * T) * ∫ x in cell 2, h x * L (expChar (intVec m) x) := by
    intro L
    refine heat_test_decay hT h u hu _ (L.contDiff.comp ((contDiff_expChar _).of_le (by norm_cast)))
      (fun x n => by simp only [isPeriodic_expChar m x n]) (fun x => ?_)
    rw [lap_re_expChar]
  -- the Fourier coefficient in terms of the real and imaginary parts of the character
  have hfc : ∀ f : Pt 2 → ℝ, Continuous f → fc (fun x => (f x : ℂ)) m =
      ((∫ x in cell 2, f x * Complex.reCLM (expChar (intVec m) x) : ℝ) : ℂ) -
        Complex.I * ((∫ x in cell 2, f x * Complex.imCLM (expChar (intVec m) x) : ℝ) : ℂ) := by
    intro f hf
    have hconj : ∀ x, expChar (-intVec m) x =
        (Complex.reCLM (expChar (intVec m) x) : ℂ) -
          Complex.I * (Complex.imCLM (expChar (intVec m) x) : ℂ) := by
      intro x
      have : expChar (-intVec m) x = (starRingEnd ℂ) (expChar (intVec m) x) := by
        unfold expChar
        rw [← Complex.exp_conj]
        congr 1
        simp only [dot, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Pi.neg_apply,
          neg_mul, Finset.sum_neg_distrib]
        push_cast; ring
      rw [this]
      apply Complex.ext <;> simp
    unfold fc
    simp only [hconj]
    have hi1 : Integrable (fun x => ((f x * Complex.reCLM (expChar (intVec m) x) : ℝ) : ℂ))
        (volume.restrict (cell 2)) :=
      (Complex.continuous_ofReal.comp (hf.mul (Complex.reCLM.continuous.comp
        (continuous_expChar _)))).continuousOn.integrableOn_compact isCompact_Icc
    have hi2 : Integrable (fun x => Complex.I *
        ((f x * Complex.imCLM (expChar (intVec m) x) : ℝ) : ℂ)) (volume.restrict (cell 2)) :=
      ((continuous_const.mul (Complex.continuous_ofReal.comp (hf.mul (Complex.imCLM.continuous.comp
        (continuous_expChar _)))))).continuousOn.integrableOn_compact isCompact_Icc
    rw [show (fun x => (f x : ℂ) * ((Complex.reCLM (expChar (intVec m) x) : ℂ) -
        Complex.I * (Complex.imCLM (expChar (intVec m) x) : ℂ))) = fun x =>
        ((f x * Complex.reCLM (expChar (intVec m) x) : ℝ) : ℂ) -
          Complex.I * ((f x * Complex.imCLM (expChar (intVec m) x) : ℝ) : ℂ) from by
      funext x; push_cast; ring]
    rw [integral_sub hi1 hi2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  have : -(ν * lam) * T = -(4 * π ^ 2 * ν * T * euclNorm (intVec m) ^ 2) := by
    rw [hlam]; ring
  rw [hfc _ huT, hfc _ hh, hdec, hdec, this]
  push_cast; ring

end AnomDiss
