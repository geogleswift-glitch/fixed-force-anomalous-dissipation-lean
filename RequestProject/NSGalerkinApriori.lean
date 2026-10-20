module

public import RequestProject.NSGalerkinEnstrophy
public import RequestProject.NSClassicalEnergy

/-!
# A priori bounds from the two Galerkin test identities

No existence theorem is assumed. The input is a time curve and its actual time
derivative, together with the identities obtained by testing the projected
equation against the velocity and its negative Laplacian. The forcing enters
only through its squared `L²` norm, never through a norm of its curl.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

private lemma ns_curve_slice_continuous {a b : ℝ} {U : ℝ → Pt 2 → Pt 2}
    (hU : ContinuousOn (fun q : ℝ × Pt 2 => U q.1 q.2) (Icc a b ×ˢ univ))
    {s : ℝ} (hs : s ∈ Icc a b) : Continuous (U s) :=
  hU.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hs, mem_univ _⟩)

/-- Young's inequality for the Euclidean energy pairing. -/
lemma ns_dot_young (z w : Pt 2) :
    2 * dot z w ≤ (∑ k, z k ^ 2) + ∑ k, w k ^ 2 := by
  simp only [dot, Fin.sum_univ_two]
  nlinarith [sq_nonneg (z 0 - w 0), sq_nonneg (z 1 - w 1)]

/-- The viscosity-scaled Young bound used when testing against `-Δv`. -/
lemma ns_dot_young_viscous {ν : ℝ} (hν : 0 < ν) (z w : Pt 2) :
    -2 * dot z w ≤ ν * (∑ k, z k ^ 2) + (1 / ν) * ∑ k, w k ^ 2 := by
  have hscalar : ∀ x y : ℝ, -2 * x * y ≤ ν * x ^ 2 + (1 / ν) * y ^ 2 := by
    intro x y
    have hcancel : ((1 / ν) * y ^ 2) * ν = y ^ 2 := by field_simp
    have hmul : (-2 * x * y) * ν ≤ (ν * x ^ 2 + (1 / ν) * y ^ 2) * ν := by
      rw [add_mul, hcancel]
      nlinarith [sq_nonneg (ν * x + y)]
    exact le_of_mul_le_mul_right hmul hν
  simp only [dot, Fin.sum_univ_two]
  nlinarith [hscalar (z 0) (w 0), hscalar (z 1) (w 1)]

/-- The spatial force work is controlled solely by the two squared `L²` norms. -/
lemma ns_integral_dot_young (z w : Pt 2 → Pt 2) (hz : Continuous z) (hw : Continuous w) :
    2 * (∫ x in cell 2, dot (z x) (w x)) ≤ l2sqV z + l2sqV w := by
  have hdot : Continuous (fun x => dot (z x) (w x)) := by
    unfold dot
    exact continuous_finset_sum _ fun k _ =>
      ((continuous_apply k).comp hz).mul ((continuous_apply k).comp hw)
  have hsq : ∀ {U : Pt 2 → Pt 2}, Continuous U → Continuous (fun x => ∑ k, U x k ^ 2) :=
    fun hU => continuous_finset_sum _ fun k _ => ((continuous_apply k).comp hU).pow 2
  rw [← integral_const_mul, l2sqV, l2sqV,
    ← integral_add (integrableOn_cell_of_continuous (hsq hz))
      (integrableOn_cell_of_continuous (hsq hw))]
  exact setIntegral_mono_on
    (integrableOn_cell_of_continuous (continuous_const.mul hdot))
    (integrableOn_cell_of_continuous ((hsq hz).add (hsq hw))) measurableSet_Icc
    (fun x _ => ns_dot_young (z x) (w x))

/-- The `-Δv` force work is controlled by viscosity times its squared `L²` norm
and inverse viscosity times the squared `L²` norm of the force. -/
lemma ns_integral_dot_young_viscous {ν : ℝ} (hν : 0 < ν)
    (z w : Pt 2 → Pt 2) (hz : Continuous z) (hw : Continuous w) :
    -2 * (∫ x in cell 2, dot (z x) (w x)) ≤ ν * l2sqV z + (1 / ν) * l2sqV w := by
  have hdot : Continuous (fun x => dot (z x) (w x)) := by
    unfold dot
    exact continuous_finset_sum _ fun k _ =>
      ((continuous_apply k).comp hz).mul ((continuous_apply k).comp hw)
  have hsq : ∀ {U : Pt 2 → Pt 2}, Continuous U → Continuous (fun x => ∑ k, U x k ^ 2) :=
    fun hU => continuous_finset_sum _ fun k _ => ((continuous_apply k).comp hU).pow 2
  rw [← integral_const_mul, l2sqV, l2sqV, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (f := fun x => ν * ∑ k, z x k ^ 2)
      (g := fun x => (1 / ν) * ∑ k, w x k ^ 2)
      (integrableOn_cell_of_continuous (continuous_const.mul (hsq hz)))
      (integrableOn_cell_of_continuous (continuous_const.mul (hsq hw)))]
  exact setIntegral_mono_on
    (integrableOn_cell_of_continuous (continuous_const.mul hdot))
    (integrableOn_cell_of_continuous
      ((continuous_const.mul (hsq hz)).add (continuous_const.mul (hsq hw))))
    measurableSet_Icc (fun x _ => ns_dot_young_viscous hν (z x) (w x))

private lemma ns_source_gronwall {a b : ℝ} (hab : a ≤ b) {E R G : ℝ → ℝ}
    (hform : ∀ t ∈ Icc a b, E t = E a + ∫ s in a..t, R s)
    (hR : ContinuousOn R (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hGa : ∀ s ∈ Icc a b, 0 ≤ G s) (hEa : 0 ≤ E a)
    (hle : ∀ s ∈ Ioo a b, R s ≤ E s + G s) :
    ∀ t ∈ Icc a b, E t ≤ (E a + ∫ s in a..b, G s) * exp (b - a) := by
  let F : ℝ → ℝ := fun t => E t + ∫ s in t..b, G s
  have htail : ∀ t ∈ Icc a b, 0 ≤ ∫ s in t..b, G s := fun t ht =>
    intervalIntegral.integral_nonneg ht.2 (fun s hs => hGa s ⟨ht.1.trans hs.1, hs.2⟩)
  have hFform : ∀ t ∈ Icc a b, F t = F a + ∫ s in a..t, (R s - G s) := by
    intro t ht
    have hGat' : IntervalIntegrable G volume a t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1]
      exact hG.mono (Icc_subset_Icc_right ht.2)
    have hGtb' : IntervalIntegrable G volume t b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.2]
      exact hG.mono (Icc_subset_Icc_left ht.1)
    have hRat : IntervalIntegrable R volume a t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1]
      exact hR.mono (Icc_subset_Icc_right ht.2)
    dsimp [F]
    rw [hform t ht, intervalIntegral.integral_sub hRat hGat']
    have hadd := intervalIntegral.integral_add_adjacent_intervals hGat' hGtb'
    linarith
  have hFbound := gronwall_of_integral (f := F) (h := fun s => R s - G s)
    (g := fun _ => (1 / 2 : ℝ)) hab hFform (hR.sub hG)
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc a b))
    (fun s hs => by
      dsimp [F]
      norm_num
      have h := hle s hs
      have htail' := htail s (Ioo_subset_Icc_self hs)
      nlinarith)
  have hK : 0 ≤ E a + ∫ s in a..b, G s :=
    add_nonneg hEa (intervalIntegral.integral_nonneg hab hGa)
  intro t ht
  have h := hFbound t ht
  dsimp [F] at h
  have hconstant : (2 : ℝ) * (∫ s in a..t, (1 / 2 : ℝ)) = t - a := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hconstant] at h
  calc
    E t ≤ E t + ∫ s in t..b, G s := le_add_of_nonneg_right (htail t ht)
    _ ≤ (E a + ∫ s in a..b, G s) * exp (t - a) := by nlinarith
    _ ≤ (E a + ∫ s in a..b, G s) * exp (b - a) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (sub_le_sub_right ht.2 a)) hK

private lemma ns_integrated_source_bound {a b ν c : ℝ}
    {E R L G : ℝ → ℝ}
    (hform : ∀ t ∈ Icc a b, E t = E a + ∫ s in a..t, R s)
    (hR : ContinuousOn R (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hG : ContinuousOn G (Icc a b))
    (hle : ∀ s ∈ Ioo a b, R s + ν * L s ≤ c * G s) :
    ∀ t ∈ Icc a b, E t + ν * (∫ s in a..t, L s) ≤ E a + c * (∫ s in a..t, G s) := by
  intro t ht
  have hi : ∀ {U : ℝ → ℝ}, ContinuousOn U (Icc a b) → IntervalIntegrable U volume a t := by
    intro U hU
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hU.mono (Icc_subset_Icc_right ht.2)
  have h := intervalIntegral.integral_mono_on_of_le_Ioo ht.1
    ((hi hR).add ((hi hL).const_mul ν)) ((hi hG).const_mul c)
    (fun s hs => hle s ⟨hs.1, hs.2.trans_le ht.2⟩)
  rw [intervalIntegral.integral_add (hi hR) ((hi hL).const_mul ν),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  linarith [hform t ht]

/-- Uniform kinetic-energy bound for a differentiable curve satisfying the
velocity test identity of the Galerkin equation. -/
theorem ns_galerkin_energy_bound {a b ν : ℝ} (hab : a ≤ b) (hν : 0 < ν)
    (v V' g : ℝ → Pt 2 → Pt 2)
    (hv : ContinuousOn (fun q : ℝ × Pt 2 => v q.1 q.2) (Icc a b ×ˢ univ))
    (hV' : ContinuousOn (fun q : ℝ × Pt 2 => V' q.1 q.2) (Icc a b ×ˢ univ))
    (hg : ContinuousOn (fun q : ℝ × Pt 2 => g q.1 q.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun t => v t x) (V' s x) s)
    (htest : ∀ s ∈ Ioo a b,
      (∫ x in cell 2, dot (v s x) (V' s x)) + ν * (∫ x in cell 2, gradSqV (v s) x) =
        (∫ x in cell 2, dot (v s x) (g s x))) :
    ∀ t ∈ Icc a b, l2sqV (v t) ≤
      (l2sqV (v a) + ∫ s in a..b, l2sqV (g s)) * exp (b - a) := by
  obtain ⟨hform, hR⟩ := l2sqV_integral_form hab v V' hv hV' hd
  have hG : ContinuousOn (fun s => l2sqV (g s)) (Icc a b) := by
    refine continuousOn_integral_cell' hab _ ?_
    exact continuousOn_finset_sum _ fun k _ => ((continuous_apply k).comp_continuousOn hg).pow 2
  apply ns_source_gronwall hab hform hR hG
    (fun s _ => setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity)
    (setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity)
  intro s hs
  have hy := ns_integral_dot_young (v s) (g s)
    (ns_curve_slice_continuous hv (Ioo_subset_Icc_self hs))
    (ns_curve_slice_continuous hg (Ioo_subset_Icc_self hs))
  have ht := htest s hs
  have hD : 0 ≤ ∫ x in cell 2, gradSqV (v s) x :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => by unfold gradSqV; positivity
  rw [integral_const_mul]
  nlinarith

/-- Uniform `H¹` and integrated `H²` estimates from the negative-Laplacian
Galerkin test identity. The only forcing norm is `l2sqV (g s)`.

The temporal derivative evidence for the curl is actual calculus data of the
finite-dimensional curve, not a replacement PDE existence assumption. -/
theorem ns_galerkin_enstrophy_bound {a b ν : ℝ} (hab : a ≤ b) (hν : 0 < ν)
    (v V' g : ℝ → Pt 2 → Pt 2)
    (hω : ContinuousOn (fun q : ℝ × Pt 2 => curl2 (v q.1) q.2) (Icc a b ×ˢ univ))
    (hω' : ContinuousOn (fun q : ℝ × Pt 2 => curl2 (V' q.1) q.2) (Icc a b ×ˢ univ))
    (hlap : ContinuousOn (fun q : ℝ × Pt 2 => lap (v q.1) q.2) (Icc a b ×ˢ univ))
    (hg : ContinuousOn (fun q : ℝ × Pt 2 => g q.1 q.2) (Icc a b ×ˢ univ))
    (hsp : ∀ s ∈ Icc a b, ContDiff ℝ 2 (v s) ∧ IsPeriodic (v s) ∧
      (∀ x, divergence (v s) x = 0) ∧ ContDiff ℝ 1 (V' s) ∧ IsPeriodic (V' s))
    (hdω : ∀ s ∈ Ioo a b, ∀ x,
      HasDerivAt (fun t => curl2 (v t) x) (curl2 (V' s) x) s)
    (htest : ∀ s ∈ Ioo a b,
      -(∫ x in cell 2, dot (lap (v s) x) (V' s x)) + ν * l2sqV (lap (v s)) =
        -(∫ x in cell 2, dot (lap (v s) x) (g s x))) :
    (∀ t ∈ Icc a b,
      (∫ x in cell 2, gradSqV (v t) x) + ν * (∫ s in a..t, l2sqV (lap (v s))) ≤
        (∫ x in cell 2, gradSqV (v a) x) + (1 / ν) * (∫ s in a..t, l2sqV (g s))) ∧
    (∀ t ∈ Icc a b,
      (∫ x in cell 2, gradSqV (v t) x) ≤
        (∫ x in cell 2, gradSqV (v a) x) + (1 / ν) * (∫ s in a..b, l2sqV (g s))) ∧
    ν * (∫ s in a..b, l2sqV (lap (v s))) ≤
      (∫ x in cell 2, gradSqV (v a) x) + (1 / ν) * (∫ s in a..b, l2sqV (g s)) := by
  obtain ⟨hform, hR⟩ := l2sq_integral_form hab (fun s => curl2 (v s))
    (fun s => curl2 (V' s)) hω hω' hdω
  have hcont : ∀ {U : ℝ → Pt 2 → Pt 2},
      ContinuousOn (fun q : ℝ × Pt 2 => U q.1 q.2) (Icc a b ×ˢ univ) →
      ContinuousOn (fun s => l2sqV (U s)) (Icc a b) := by
    intro U hU
    refine continuousOn_integral_cell' hab _ ?_
    exact continuousOn_finset_sum _ fun k _ => ((continuous_apply k).comp_continuousOn hU).pow 2
  have hL := hcont (U := fun s => lap (v s)) hlap
  have hG := hcont (U := g) hg
  have hgrad : ∀ s ∈ Icc a b, l2sq (curl2 (v s)) = ∫ x in cell 2, gradSqV (v s) x := by
    intro s hs
    obtain ⟨hs2, hsp, hsdiv, -, -⟩ := hsp s hs
    exact (ns_gradient_eq_enstrophy (v s) hs2 hsp hsdiv).symm
  have hbound := ns_integrated_source_bound (ν := ν) (c := 1 / ν) hform hR hL hG
    (fun s hs => by
      obtain ⟨hs2, hsper, hsdiv, hsV', hsV'per⟩ := hsp s (Ioo_subset_Icc_self hs)
      have hpair := ns_enstrophy_force_identity (v s) (V' s) hs2 hsper hsdiv hsV' hsV'per
      have hy := ns_integral_dot_young_viscous hν (lap (v s)) (g s)
        (ns_curve_slice_continuous (U := fun r => lap (v r)) hlap (Ioo_subset_Icc_self hs))
        (ns_curve_slice_continuous hg (Ioo_subset_Icc_self hs))
      have ht := htest s hs
      rw [show (fun x => 2 * curl2 (v s) x * curl2 (V' s) x) =
        fun x => 2 * (curl2 (v s) x * curl2 (V' s) x) by funext x; ring,
        integral_const_mul, hpair]
      nlinarith)
  have hbound' : ∀ t ∈ Icc a b,
      (∫ x in cell 2, gradSqV (v t) x) + ν * (∫ s in a..t, l2sqV (lap (v s))) ≤
        (∫ x in cell 2, gradSqV (v a) x) + (1 / ν) * (∫ s in a..t, l2sqV (g s)) := by
    intro t ht
    simpa only [hgrad t ht, hgrad a ⟨le_rfl, hab⟩] using hbound t ht
  refine ⟨hbound', fun t ht => ?_, ?_⟩
  · have hL0 : 0 ≤ ∫ s in a..t, l2sqV (lap (v s)) :=
      intervalIntegral.integral_nonneg ht.1 fun _ _ =>
        setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity
    have hGmono : (∫ s in a..t, l2sqV (g s)) ≤ ∫ s in a..b, l2sqV (g s) := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      · exact Eventually.of_forall fun _ =>
          setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity
      · exact hG.intervalIntegrable_of_Icc hab
    have hscaled := mul_le_mul_of_nonneg_left hGmono (by positivity : 0 ≤ 1 / ν)
    nlinarith [hbound' t ht]
  · have hEb : 0 ≤ ∫ x in cell 2, gradSqV (v b) x :=
      setIntegral_nonneg measurableSet_Icc fun _ _ => by unfold gradSqV; positivity
    nlinarith [hbound' b ⟨hab, le_rfl⟩]

end AnomDiss
