module

public import RequestProject.VortL4

/-!
# Spatial identities for the two-dimensional Galerkin construction

These identities apply to smooth periodic divergence-free fields without any
Navier–Stokes existence assumption. They supply the nonlinear cancellation in
the enstrophy estimate and identify enstrophy with the squared gradient norm.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- Integration by parts and symmetry of mixed derivatives exchange the two
mixed gradient pairings on the periodic cell. -/
lemma ns_mixed_gradient_pairing (a b : Pt 2 → ℝ)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hap : IsPeriodic a) (hbp : IsPeriodic b) :
    (∫ x in cell 2, pd 0 a x * pd 1 b x) =
      (∫ x in cell 2, pd 1 a x * pd 0 b x) := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hfirst := integral_mul_pd (pd 1 b) a (contDiff_pd_of_C2 b hb 1) ha1
    (isPeriodic_pd b hbp 1) hap 0
  have hsecond := integral_mul_pd a (pd 0 b) ha1 (contDiff_pd_of_C2 b hb 0)
    hap (isPeriodic_pd b hbp 0) 1
  have heq : (∫ x in cell 2, pd 0 a x * pd 1 b x) =
      -(∫ x in cell 2, a x * pd 1 (pd 0 b) x) := by
    calc
      (∫ x in cell 2, pd 0 a x * pd 1 b x) =
          (∫ x in cell 2, pd 1 b x * pd 0 a x) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x _
        ring
      _ = -(∫ x in cell 2, pd 0 (pd 1 b) x * a x) := hfirst
      _ = -(∫ x in cell 2, a x * pd 1 (pd 0 b) x) := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro x _
        dsimp only
        rw [pd_pd_comm b hb 0 1 x]
        ring
  linarith

/-- For a divergence-free two-dimensional periodic field, enstrophy equals the
squared `L²` norm of its gradient. -/
theorem ns_gradient_eq_enstrophy (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v)
    (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) :
    (∫ x in cell 2, gradSqV v x) = (∫ x in cell 2, curl2 v x ^ 2) := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hk : ∀ k : Fin 2, ContDiff ℝ 2 (cmp v k) := contDiff_cmp hv
  have hkp : ∀ k : Fin 2, IsPeriodic (cmp v k) := fun k x n => by
    simp [cmp, hp x n]
  have hcross := ns_mixed_gradient_pairing (cmp v 0) (cmp v 1)
    (hk 0) (hk 1) (hkp 0) (hkp 1)
  have hd : ∀ k i, Continuous (pd i (cmp v k)) := fun k i =>
    continuous_pd_of_C1 _ ((hk k).of_le (by norm_num)) i
  have hc : Continuous (fun x => curl2 v x ^ 2) := (continuous_curl2 hv).pow 2
  have hbc : Continuous (fun x => pd 0 (cmp v 1) x * pd 1 (cmp v 0) x) :=
    (hd 1 0).mul (hd 0 1)
  have had : Continuous (fun x => pd 0 (cmp v 0) x * pd 1 (cmp v 1) x) :=
    (hd 0 0).mul (hd 1 1)
  have heq : ∀ x, gradSqV v x = curl2 v x ^ 2 +
      2 * (pd 0 (cmp v 1) x * pd 1 (cmp v 0) x -
        pd 0 (cmp v 0) x * pd 1 (cmp v 1) x) := by
    intro x
    have hdiv' := hdiv x
    simp only [divergence, Fin.sum_univ_two,
      ← pd_component v x (hv1.differentiable one_ne_zero x)] at hdiv'
    have hdiag : pd 0 (cmp v 0) x = -pd 1 (cmp v 1) x := by
      exact eq_neg_of_add_eq_zero_left hdiv'
    simp only [gradSqV, Fin.sum_univ_two, curl2,
      ← pd_component v x (hv1.differentiable one_ne_zero x)]
    change pd 0 (cmp v 0) x ^ 2 + pd 0 (cmp v 1) x ^ 2 +
        (pd 1 (cmp v 0) x ^ 2 + pd 1 (cmp v 1) x ^ 2) = _
    rw [hdiag]
    ring
  rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc (fun x _ => heq x),
    integral_add (f := fun x => curl2 v x ^ 2)
      (g := fun x => 2 * (pd 0 (cmp v 1) x * pd 1 (cmp v 0) x -
        pd 0 (cmp v 0) x * pd 1 (cmp v 1) x))
      (integrableOn_cell_of_continuous hc)
      (((integrableOn_cell_of_continuous hbc).sub
        (integrableOn_cell_of_continuous had)).const_mul 2),
    integral_const_mul,
    integral_sub (f := fun x => pd 0 (cmp v 1) x * pd 1 (cmp v 0) x)
      (g := fun x => pd 0 (cmp v 0) x * pd 1 (cmp v 1) x)
      (integrableOn_cell_of_continuous hbc) (integrableOn_cell_of_continuous had)]
  have hcomm : (∫ x in cell 2, pd 0 (cmp v 1) x * pd 1 (cmp v 0) x) =
      (∫ x in cell 2, pd 1 (cmp v 0) x * pd 0 (cmp v 1) x) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    ring
  rw [hcomm, ← hcross]
  ring

/-- Vorticity advection does not change the spatial enstrophy. This cancellation
does not require a solution of the evolution equation. -/
theorem ns_vorticity_advection_cancellation (v : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) :
    (∫ x in cell 2, curl2 v x * conv v (curl2 v) x) = 0 :=
  integral_mul_conv v (hv.of_le (by norm_num)) hp hdiv
    (curl2 v) (contDiff_curl2 hv) (isPeriodic_curl2 hp)

/-- The curl form of the nonlinear enstrophy cancellation, expressed directly
through the two components of the convective term. -/
theorem ns_curl_convection_cancellation (v : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) :
    (∫ x in cell 2, curl2 v x *
      (pd 0 (conv v (cmp v 1)) x - pd 1 (conv v (cmp v 0)) x)) = 0 := by
  simp only [curl_conv_identity v hv hdiv]
  exact ns_vorticity_advection_cancellation v hv hp hdiv

/-- Divergence-free fields recover their Laplacian from the first derivatives
of the scalar vorticity. -/
lemma ns_laplacian_from_vorticity (v : Pt 2 → Pt 2) (hv : ContDiff ℝ 2 v)
    (hdiv : ∀ x, divergence v x = 0) (x : Pt 2) :
    pd 1 (curl2 v) x = -lap (cmp v 0) x ∧
      pd 0 (curl2 v) x = lap (cmp v 1) x := by
  have hk : ∀ k : Fin 2, ContDiff ℝ 2 (cmp v k) := contDiff_cmp hv
  have hdk : ∀ i k, Differentiable ℝ (pd i (cmp v k)) := fun i k =>
    (contDiff_pd_of_C2 _ (hk k) i).differentiable one_ne_zero
  have hfun : (fun y => pd 0 (cmp v 0) y + pd 1 (cmp v 1) y) = fun _ => 0 := by
    funext y
    have h := hdiv y
    simpa only [divergence, Fin.sum_univ_two,
      ← pd_component v y (hv.differentiable (by norm_num) y)] using h
  have hdd : ∀ i : Fin 2, pd i (pd 0 (cmp v 0)) x + pd i (pd 1 (cmp v 1)) x = 0 := by
    intro i
    have h := congrArg (fun f : Pt 2 → ℝ => pd i f x) hfun
    rw [pd_add' _ _ x (hdk 0 0 x) (hdk 1 1 x)] at h
    simpa [pd] using h
  have hcurl : curl2 v = fun y => pd 0 (cmp v 1) y - pd 1 (cmp v 0) y :=
    funext (curl2_eq_cmp v (hv.differentiable (by norm_num)))
  have h0 := hdd 0
  have h1 := hdd 1
  have hs0 := pd_pd_comm (cmp v 0) (hk 0) 0 1 x
  have hs1 := pd_pd_comm (cmp v 1) (hk 1) 0 1 x
  constructor
  · rw [hcurl, pd_sub' _ _ x (hdk 0 1 x) (hdk 1 0 x)]
    simp only [lap, Fin.sum_univ_two]
    linarith
  · rw [hcurl, pd_sub' _ _ x (hdk 0 1 x) (hdk 1 0 x)]
    simp only [lap, Fin.sum_univ_two]
    linarith

/-- In the enstrophy balance, the force is paired with the velocity Laplacian.
This allows a bound by the `L²` norm of the force without controlling its curl. -/
theorem ns_enstrophy_force_identity (v g : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 2 v) (hvp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0)
    (hg : ContDiff ℝ 1 g) (hgp : IsPeriodic g) :
    (∫ x in cell 2, curl2 v x * curl2 g x) =
      -(∫ x in cell 2, dot (lap v x) (g x)) := by
  have hgk : ∀ k : Fin 2, ContDiff ℝ 1 (cmp g k) := contDiff_cmp hg
  have hgkp : ∀ k : Fin 2, IsPeriodic (cmp g k) := fun k x n => by
    simp [cmp, hgp x n]
  have hc := contDiff_curl2 hv
  have hp := isPeriodic_curl2 hvp
  have hI0 := integral_mul_pd (curl2 v) (cmp g 0) hc (hgk 0) hp (hgkp 0) 1
  have hI1 := integral_mul_pd (curl2 v) (cmp g 1) hc (hgk 1) hp (hgkp 1) 0
  have hsplit : (∫ x in cell 2, curl2 v x * curl2 g x) =
      (∫ x in cell 2, curl2 v x * pd 0 (cmp g 1) x) -
        (∫ x in cell 2, curl2 v x * pd 1 (cmp g 0) x) := by
    have heq : ∀ x, curl2 v x * curl2 g x =
        curl2 v x * pd 0 (cmp g 1) x - curl2 v x * pd 1 (cmp g 0) x := by
      intro x
      rw [curl2_eq_cmp g (hg.differentiable one_ne_zero) x]
      ring
    rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc (fun x _ => heq x),
      integral_sub (f := fun x => curl2 v x * pd 0 (cmp g 1) x)
        (g := fun x => curl2 v x * pd 1 (cmp g 0) x)
        (integrableOn_cell_of_continuous (hc.continuous.mul (continuous_pd_of_C1 _ (hgk 1) 0)))
        (integrableOn_cell_of_continuous (hc.continuous.mul (continuous_pd_of_C1 _ (hgk 0) 1)))]
  have hrot0 : (∫ x in cell 2, pd 1 (curl2 v) x * cmp g 0 x) =
      -(∫ x in cell 2, lap (cmp v 0) x * cmp g 0 x) := by
    have heq : ∀ x, pd 1 (curl2 v) x * cmp g 0 x =
        -(lap (cmp v 0) x * cmp g 0 x) := by
      intro x
      rw [(ns_laplacian_from_vorticity v hv hdiv x).1]
      ring
    rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc (fun x _ => heq x), integral_neg]
  have hrot1 : (∫ x in cell 2, pd 0 (curl2 v) x * cmp g 1 x) =
      (∫ x in cell 2, lap (cmp v 1) x * cmp g 1 x) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    dsimp only
    rw [(ns_laplacian_from_vorticity v hv hdiv x).2]
  have hlap : (∫ x in cell 2, dot (lap v x) (g x)) =
      (∫ x in cell 2, lap (cmp v 0) x * cmp g 0 x) +
        (∫ x in cell 2, lap (cmp v 1) x * cmp g 1 x) := by
    have heq : ∀ x, dot (lap v x) (g x) =
        lap (cmp v 0) x * cmp g 0 x + lap (cmp v 1) x * cmp g 1 x := by
      intro x
      simp only [dot, Fin.sum_univ_two, cmp, lap_component v hv]
    rw [setIntegral_congr_fun (s := cell 2) measurableSet_Icc (fun x _ => heq x),
      integral_add (f := fun x => lap (cmp v 0) x * cmp g 0 x)
      (g := fun x => lap (cmp v 1) x * cmp g 1 x)
      (integrableOn_cell_of_continuous
        ((continuous_lap_of_C2 _ (contDiff_cmp hv 0)).mul (hgk 0).continuous))
      (integrableOn_cell_of_continuous
        ((continuous_lap_of_C2 _ (contDiff_cmp hv 1)).mul (hgk 1).continuous))]
  rw [hsplit, hI1, hI0, hrot1, hrot0, hlap]
  ring

/-- The form of nonlinear cancellation used after testing the Galerkin equation
against `-Δv`. -/
theorem ns_laplacian_convection_cancellation (v : Pt 2 → Pt 2)
    (hv : ContDiff ℝ 2 v) (hp : IsPeriodic v) (hdiv : ∀ x, divergence v x = 0) :
    (∫ x in cell 2, dot (lap v x) (conv v v x)) = 0 := by
  let B : Pt 2 → Pt 2 := conv v v
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hBk : ∀ k : Fin 2, cmp B k = conv v (cmp v k) := fun k =>
    funext fun x => (conv_component v v hd k x).symm
  have hB : ContDiff ℝ 1 B := by
    apply contDiff_pi.mpr
    intro k
    change ContDiff ℝ 1 (cmp B k)
    rw [hBk k]
    exact contDiff_conv_cmp hv k
  have hBp : IsPeriodic B := by
    intro x n
    change (∑ j, v (x + intVec n) j • pd j v (x + intVec n)) =
      ∑ j, v x j • pd j v x
    simp only [hp x n, fun j => isPeriodic_pd v hp j x n]
  have hcancel : (∫ x in cell 2, curl2 v x * curl2 B x) = 0 := by
    simp only [curl2_eq_cmp B (hB.differentiable one_ne_zero), hBk]
    exact ns_curl_convection_cancellation v hv hp hdiv
  have hidentity := ns_enstrophy_force_identity v B hv hp hdiv hB hBp
  rw [hcancel] at hidentity
  change (∫ x in cell 2, dot (lap v x) (B x)) = 0
  linarith

end AnomDiss
