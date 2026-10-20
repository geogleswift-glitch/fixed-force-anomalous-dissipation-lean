module

public import RequestProject.Mollify
public import RequestProject.Linfty

/-!
# The mollified vorticity equation

For a classical solution of the two-dimensional Navier–Stokes equations the vorticity
`ϖ = curl v` is only `C¹` in space and need not be differentiable in time.  Its mollification
`W = φ ⋆ ϖ` is smooth in space and differentiable in time, and it satisfies

  `∂ₜW + v·∇W = νΔW + G + R`,

where `G = curl (φ ⋆ g)` and the commutator `R = v·∇(φ ⋆ ϖ) - φ ⋆ (v·∇ϖ)` is small when the
support of `φ` is small.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace AnomDiss

section symm
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pd_pd_eq_fderiv2 (h : Pt d → E) (hh : ContDiff ℝ 2 h) (i j : Fin d) (x : Pt d) :
    pd i (pd j h) x = fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single j 1) := by
  unfold pd
  have hd : DifferentiableAt ℝ (fderiv ℝ h) x :=
    ((hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- Symmetry of second partial derivatives of a `C²` function. -/
lemma pd_pd_comm (h : Pt d → E) (hh : ContDiff ℝ 2 h) (i j : Fin d) (x : Pt d) :
    pd i (pd j h) x = pd j (pd i h) x := by
  have hs := (hh.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  rw [pd_pd_eq_fderiv2 h hh, pd_pd_eq_fderiv2 h hh, hs]

lemma pd_add' (f g : Pt d → E) (x : Pt d) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  unfold pd; rw [fderiv_fun_add hf hg]; rfl

lemma pd_sub' (f g : Pt d → E) (x : Pt d) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  unfold pd; rw [fderiv_fun_sub hf hg]; rfl

end symm

/-- The components `uₖ` of a vector field. -/
abbrev cmp (u : Pt 2 → Pt 2) (k : Fin 2) : Pt 2 → ℝ := fun y => u y k

lemma contDiff_cmp {n : WithTop ℕ∞} {u : Pt 2 → Pt 2} (hu : ContDiff ℝ n u) (k : Fin 2) :
    ContDiff ℝ n (cmp u k) := (contDiff_apply ℝ ℝ k).comp hu

lemma curl2_eq_cmp (u : Pt 2 → Pt 2) (hu : Differentiable ℝ u) (x : Pt 2) :
    curl2 u x = pd 0 (cmp u 1) x - pd 1 (cmp u 0) x := by
  unfold curl2; rw [pd_component u x (hu x), pd_component u x (hu x)]

lemma conv_two (u : Pt 2 → Pt 2) (h : Pt 2 → ℝ) (x : Pt 2) :
    conv u h x = u x 0 * pd 0 h x + u x 1 * pd 1 h x := by
  simp [conv, Fin.sum_univ_two]

/-- In two dimensions, `curl (u·∇u) = u·∇(curl u)` for divergence-free `C²` fields. -/
lemma curl_conv_identity (u : Pt 2 → Pt 2) (hu : ContDiff ℝ 2 u)
    (hdiv : ∀ x, divergence u x = 0) (x : Pt 2) :
    pd 0 (conv u (cmp u 1)) x - pd 1 (conv u (cmp u 0)) x = conv u (curl2 u) x := by
  have hd : ∀ k, Differentiable ℝ (cmp u k) := fun k =>
    (contDiff_cmp hu k).differentiable (by norm_num)
  have hd1 : ∀ k j, Differentiable ℝ (pd j (cmp u k)) := fun k j =>
    (contDiff_pd_of_C2 _ (contDiff_cmp hu k) j).differentiable (by norm_num)
  have hc : ∀ k, conv u (cmp u k) = fun y => cmp u 0 y * pd 0 (cmp u k) y +
      cmp u 1 y * pd 1 (cmp u k) y := fun k => funext fun y => conv_two u _ y
  have hcurl : curl2 u = fun y => pd 0 (cmp u 1) y - pd 1 (cmp u 0) y :=
    funext fun y => curl2_eq_cmp u (hu.differentiable (by norm_num)) y
  have hdv : pd 0 (cmp u 0) x + pd 1 (cmp u 1) x = 0 := by
    have := hdiv x
    simp only [divergence, Fin.sum_univ_two] at this
    rwa [← pd_component u x ((hu.differentiable (by norm_num)) x),
      ← pd_component u x ((hu.differentiable (by norm_num)) x)] at this
  have hsym : ∀ k, pd 0 (pd 1 (cmp u k)) x = pd 1 (pd 0 (cmp u k)) x := fun k =>
    pd_pd_comm _ (contDiff_cmp hu k) 0 1 x
  have hprod : ∀ j k i, pd i (fun y => cmp u j y * pd j (cmp u k) y) x =
      pd i (cmp u j) x * pd j (cmp u k) x + cmp u j x * pd i (pd j (cmp u k)) x :=
    fun j k i => pd_mul' _ _ x (hd j x) (hd1 k j x) i
  rw [hc 1, hc 0, conv_two, hcurl,
    pd_add' (fun y => cmp u 0 y * pd 0 (cmp u 1) y) (fun y => cmp u 1 y * pd 1 (cmp u 1) y) x
      ((hd 0 x).mul (hd1 1 0 x)) ((hd 1 x).mul (hd1 1 1 x)),
    pd_add' (fun y => cmp u 0 y * pd 0 (cmp u 0) y) (fun y => cmp u 1 y * pd 1 (cmp u 0) y) x
      ((hd 0 x).mul (hd1 0 0 x)) ((hd 1 x).mul (hd1 0 1 x)),
    hprod, hprod, hprod, hprod,
    pd_sub' (pd 0 (cmp u 1)) (pd 1 (cmp u 0)) x (hd1 1 0 x) (hd1 0 1 x),
    pd_sub' (pd 0 (cmp u 1)) (pd 1 (cmp u 0)) x (hd1 1 0 x) (hd1 0 1 x)]
  simp only [cmp] at hsym hdv ⊢
  have h1 := hsym 0
  have h2 := hsym 1
  linear_combination (pd 0 (fun y => u y 1) x - pd 1 (fun y => u y 0) x) * hdv +
    u x 1 * h2 + u x 0 * h1

/-! ### Kernels -/

/-- Smooth compactly supported kernels. -/
def IsKer (ψ : Pt 2 → ℝ) : Prop := ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ

lemma IsKer.pd {ψ : Pt 2 → ℝ} (h : IsKer ψ) (i : Fin 2) : IsKer (pd i ψ) :=
  ⟨(h.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    by exact h.2.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)⟩

lemma IsKer.c1 {ψ : Pt 2 → ℝ} (h : IsKer ψ) : ContDiff ℝ 1 ψ := h.1.of_le (by simp)

lemma IsKer.c2 {ψ : Pt 2 → ℝ} (h : IsKer ψ) : ContDiff ℝ 2 ψ := h.1.of_le (by norm_cast)

lemma IsKer.cont {ψ : Pt 2 → ℝ} (h : IsKer ψ) : Continuous ψ := h.1.continuous

lemma pd_mc_sub {ψ₁ ψ₂ h₁ h₂ : Pt 2 → ℝ} (k₁ : IsKer ψ₁) (k₂ : IsKer ψ₂)
    (c₁ : Continuous h₁) (c₂ : Continuous h₂) (i : Fin 2) :
    pd i (fun y => mc ψ₁ h₁ y - mc ψ₂ h₂ y) = fun y => mc (pd i ψ₁) h₁ y - mc (pd i ψ₂) h₂ y := by
  funext y
  rw [pd_sub' _ _ y (differentiable_mc k₁.c1 k₁.2 c₁ y) (differentiable_mc k₂.c1 k₂.2 c₂ y),
    pd_mc k₁.c1 k₁.2 c₁, pd_mc k₂.c1 k₂.2 c₂]

/-- The mollified vorticity with the derivative moved onto the kernel. -/
lemma mc_curl2 {φ : Pt 2 → ℝ} (k : IsKer φ) {u : Pt 2 → Pt 2} (hu : ContDiff ℝ 1 u) (x : Pt 2) :
    mc φ (curl2 u) x = mc (pd 0 φ) (cmp u 1) x - mc (pd 1 φ) (cmp u 0) x := by
  have hc : ∀ j, ContDiff ℝ 1 (cmp u j) := fun j => contDiff_cmp hu j
  rw [show curl2 u = fun y => pd 0 (cmp u 1) y - pd 1 (cmp u 0) y from
    funext fun y => curl2_eq_cmp u (hu.differentiable one_ne_zero) y,
    mc_sub k.cont k.2 (continuous_pd_of_C1 _ (hc 1) 0) (continuous_pd_of_C1 _ (hc 0) 1),
    mc_pd k.c1 k.2 (hc 1), mc_pd k.c1 k.2 (hc 0)]

lemma mc_lap {ψ : Pt 2 → ℝ} (k : IsKer ψ) {h : Pt 2 → ℝ} (hh : ContDiff ℝ 2 h) (x : Pt 2) :
    mc ψ (lap h) x = mc (pd 0 (pd 0 ψ)) h x + mc (pd 1 (pd 1 ψ)) h x := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hp : ∀ i, ContDiff ℝ 1 (pd i h) := fun i => contDiff_pd_of_C2 h hh i
  rw [show lap h = fun y => pd 0 (pd 0 h) y + pd 1 (pd 1 h) y from
    funext fun y => by simp [lap, Fin.sum_univ_two],
    mc_add k.cont k.2 (continuous_pd_of_C1 _ (hp 0) 0) (continuous_pd_of_C1 _ (hp 1) 1),
    mc_pd k.c1 k.2 (hp 0), mc_pd k.c1 k.2 (hp 1), mc_pd (k.pd 0).c1 (k.pd 0).2 h1,
    mc_pd (k.pd 1).c1 (k.pd 1).2 h1]

lemma contDiff_conv_cmp {u : Pt 2 → Pt 2} (hu : ContDiff ℝ 2 u) (k : Fin 2) :
    ContDiff ℝ 1 (conv u (cmp u k)) := by
  rw [show conv u (cmp u k) = fun y => cmp u 0 y * pd 0 (cmp u k) y + cmp u 1 y * pd 1 (cmp u k) y
    from funext fun y => conv_two u _ y]
  have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  exact ((contDiff_cmp h1 0).mul (contDiff_pd_of_C2 _ (contDiff_cmp hu k) 0)).add
    ((contDiff_cmp h1 1).mul (contDiff_pd_of_C2 _ (contDiff_cmp hu k) 1))

/-- **Mollified vorticity identity** (spatial part).  If `F = -u·∇u - ∇π + νΔu + f`, then
`curl (φ ⋆ F) = -φ ⋆ (u·∇ curl u) + ν Δ (φ ⋆ curl u) + curl (φ ⋆ f)`, all curls being
written with the derivative on the kernel. -/
lemma moll_vort_identity {φ : Pt 2 → ℝ} (k : IsKer φ) (ν : ℝ) {u : Pt 2 → Pt 2}
    (hu : ContDiff ℝ 2 u) (hdiv : ∀ x, divergence u x = 0) {pr : Pt 2 → ℝ}
    (hpr : ContDiff ℝ 1 pr) {f F : Pt 2 → Pt 2} (hf : Continuous f)
    (heq : ∀ z, F z + conv u u z + grad pr z = ν • lap u z + f z) (x : Pt 2) :
    mc (pd 0 φ) (cmp F 1) x - mc (pd 1 φ) (cmp F 0) x =
      -mc φ (conv u (curl2 u)) x + ν * lap (mc φ (curl2 u)) x +
        (mc (pd 0 φ) (cmp f 1) x - mc (pd 1 φ) (cmp f 0) x) := by
  have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hcu : ∀ j, ContDiff ℝ 2 (cmp u j) := fun j => contDiff_cmp hu j
  have hA : ∀ j, ContDiff ℝ 1 (conv u (cmp u j)) := fun j => contDiff_conv_cmp hu j
  -- componentwise form of the equation
  have hFk : ∀ j, cmp F j = fun z => ((-conv u (cmp u j) z - pd j pr z) + ν * lap (cmp u j) z) +
      cmp f j z := by
    intro j; funext z
    have := congrFun (heq z) j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [conv_component u u hud j z, lap_component u hu j z]
    simp only [grad] at this
    simp only [cmp]; linarith
  have cA : ∀ j, Continuous (conv u (cmp u j)) := fun j => (hA j).continuous
  have cP : ∀ j, Continuous (pd j pr) := fun j => continuous_pd_of_C1 pr hpr j
  have cL : ∀ j, Continuous (lap (cmp u j)) := fun j => continuous_lap_of_C2 _ (hcu j)
  have cf : ∀ j, Continuous (cmp f j) := fun j => (continuous_apply j).comp hf
  have expand : ∀ i j, mc (pd i φ) (cmp F j) x = ((-mc (pd i φ) (conv u (cmp u j)) x -
      mc (pd i φ) (pd j pr) x) + ν * mc (pd i φ) (lap (cmp u j)) x) + mc (pd i φ) (cmp f j) x := by
    intro i j
    have ki := k.pd i
    rw [hFk j, mc_add (h₁ := fun z => (-conv u (cmp u j) z - pd j pr z) + ν * lap (cmp u j) z)
      (h₂ := cmp f j) ki.cont ki.2 (((cA j).neg.sub (cP j)).add (continuous_const.mul (cL j)))
      (cf j), mc_add (h₁ := fun z => -conv u (cmp u j) z - pd j pr z)
      (h₂ := fun z => ν * lap (cmp u j) z) ki.cont ki.2 ((cA j).neg.sub (cP j))
      (continuous_const.mul (cL j)),
      mc_sub (h₁ := fun z => -conv u (cmp u j) z) (h₂ := pd j pr) ki.cont ki.2 (cA j).neg (cP j),
      mc_neg, mc_const_mul]
  rw [expand, expand]
  -- convection
  have hconv : mc (pd 0 φ) (conv u (cmp u 1)) x - mc (pd 1 φ) (conv u (cmp u 0)) x =
      mc φ (conv u (curl2 u)) x := by
    rw [← mc_pd k.c1 k.2 (hA 1), ← mc_pd k.c1 k.2 (hA 0), ← mc_sub k.cont k.2
      (continuous_pd_of_C1 _ (hA 1) 0) (continuous_pd_of_C1 _ (hA 0) 1)]
    congr 1; funext z; exact curl_conv_identity u hu hdiv z
  -- pressure
  have hpress : mc (pd 0 φ) (pd 1 pr) x - mc (pd 1 φ) (pd 0 pr) x = 0 := by
    rw [mc_pd (k.pd 0).c1 (k.pd 0).2 hpr, mc_pd (k.pd 1).c1 (k.pd 1).2 hpr,
      show pd 1 (pd 0 φ) = pd 0 (pd 1 φ) from funext fun z => pd_pd_comm φ k.c2 1 0 z, sub_self]
  -- viscosity
  have hvisc : mc (pd 0 φ) (lap (cmp u 1)) x - mc (pd 1 φ) (lap (cmp u 0)) x =
      lap (mc φ (curl2 u)) x := by
    have hW : mc φ (curl2 u) = fun y => mc (pd 0 φ) (cmp u 1) y - mc (pd 1 φ) (cmp u 0) y :=
      funext fun y => mc_curl2 k h1 y
    have cu : ∀ j, Continuous (cmp u j) := fun j => (hcu j).continuous
    rw [hW, mc_lap (k.pd 0) (hcu 1), mc_lap (k.pd 1) (hcu 0)]
    simp only [lap, Fin.sum_univ_two]
    rw [pd_mc_sub (k.pd 0) (k.pd 1) (cu 1) (cu 0), pd_mc_sub (k.pd 0) (k.pd 1) (cu 1) (cu 0),
      pd_mc_sub ((k.pd 0).pd 0) ((k.pd 1).pd 0) (cu 1) (cu 0),
      pd_mc_sub ((k.pd 0).pd 1) ((k.pd 1).pd 1) (cu 1) (cu 0)]
    ring
  linear_combination (-1 : ℝ) * hconv - hpress + ν * hvisc

/-! ### Lipschitz bounds and the commutator -/

lemma lip_of_pd_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Pt 2 → E)
    (hd : Differentiable ℝ h) {B : ℝ} (hB : ∀ i z, ‖pd i h z‖ ≤ B) (x y : Pt 2) :
    ‖h x - h y‖ ≤ 2 * B * ‖x - y‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hf : ∀ z, ‖fderiv ℝ h z‖ ≤ 2 * B := by
    intro z
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [fderiv_apply_eq_sum_pd, Fin.sum_univ_two]
    have h0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
    have h1 : ‖v 1‖ ≤ ‖v‖ := norm_le_pi_norm v 1
    calc ‖v 0 • pd 0 h z + v 1 • pd 1 h z‖ ≤ ‖v 0‖ * B + ‖v 1‖ * B := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
            exact mul_le_mul_of_nonneg_left (hB _ _) (norm_nonneg _)
      _ ≤ 2 * B * ‖v‖ := by nlinarith
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z) (fun z _ => hf z)
    (mem_univ y) (mem_univ x)
  simpa using this

lemma abs_lip_of_pd_bound (h : Pt 2 → ℝ) (hd : Differentiable ℝ h) {B : ℝ}
    (hB : ∀ i z, |pd i h z| ≤ B) (x y : Pt 2) : |h x - h y| ≤ 2 * B * ‖x - y‖ :=
  lip_of_pd_bound h hd hB x y

/-- Mollification error for a Lipschitz function. -/
lemma abs_mc_sub_le_lip {φ h : Pt 2 → ℝ} (k : IsKer φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hφ1 : ∫ y, φ y = 1) {ε : ℝ} (hφε : ∀ y, φ y ≠ 0 → ‖y‖ < ε) (hh : Continuous h) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) (x : Pt 2) :
    |mc φ h x - h x| ≤ L * ε := by
  refine abs_mc_sub_le k.cont k.2 hφ0 hφ1 hh x fun y hy => ?_
  calc |h (x - y) - h x| ≤ L * ‖x - y - x‖ := hL _ _
    _ = L * ‖y‖ := by rw [sub_sub_cancel_left, norm_neg]
    _ ≤ L * ε := mul_le_mul_of_nonneg_left (hφε y hy).le hL0

/-- The commutator `u·∇(φ ⋆ ϖ) - φ ⋆ (u·∇ϖ)` is `O(ε)`. -/
lemma commutator_bound {φ : Pt 2 → ℝ} (k : IsKer φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hφ1 : ∫ y, φ y = 1) {ε : ℝ} (hφε : ∀ y, φ y ≠ 0 → ‖y‖ < ε) {u : Pt 2 → Pt 2}
    (hu : Continuous u) {w : Pt 2 → ℝ} (hw : ContDiff ℝ 1 w) {L M : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ j x y, |u x j - u y j| ≤ L * ‖x - y‖) (hM : ∀ j z, |pd j w z| ≤ M) (x : Pt 2) :
    |conv u (mc φ w) x - mc φ (conv u w) x| ≤ 2 * (L * ε * M) := by
  have hpw : ∀ j, Continuous (pd j w) := fun j => continuous_pd_of_C1 w hw j
  have hu' : ∀ j, Continuous (cmp u j) := fun j => (continuous_apply j).comp hu
  have e1 : conv u (mc φ w) x = u x 0 * mc φ (pd 0 w) x + u x 1 * mc φ (pd 1 w) x := by
    rw [conv_two, pd_mc k.c1 k.2 hw.continuous, pd_mc k.c1 k.2 hw.continuous,
      mc_pd k.c1 k.2 hw, mc_pd k.c1 k.2 hw]
  have e2 : mc φ (conv u w) x = mc φ (fun z => cmp u 0 z * pd 0 w z) x +
      mc φ (fun z => cmp u 1 z * pd 1 w z) x := by
    rw [show conv u w = fun z => cmp u 0 z * pd 0 w z + cmp u 1 z * pd 1 w z from
      funext fun z => conv_two u w z]
    exact mc_add k.cont k.2 ((hu' 0).mul (hpw 0)) ((hu' 1).mul (hpw 1)) x
  have hj : ∀ j, |cmp u j x * mc φ (pd j w) x - mc φ (fun z => cmp u j z * pd j w z) x| ≤
      L * ε * M := by
    intro j
    refine abs_commutator_le k.cont k.2 hφ0 hφ1 (hu' j) (hpw j) x fun y hy => ?_
    rw [abs_mul]
    have h1 : |cmp u j x - cmp u j (x - y)| ≤ L * ε := by
      calc |cmp u j x - cmp u j (x - y)| ≤ L * ‖x - (x - y)‖ := hL j _ _
        _ = L * ‖y‖ := by rw [sub_sub_cancel]
        _ ≤ L * ε := mul_le_mul_of_nonneg_left (hφε y hy).le hL0
    exact mul_le_mul h1 (hM j _) (abs_nonneg _) ((abs_nonneg _).trans h1)
  rw [e1, e2]
  have a := hj 0
  have b := hj 1
  simp only [cmp] at a b
  calc |u x 0 * mc φ (pd 0 w) x + u x 1 * mc φ (pd 1 w) x -
        (mc φ (fun z => u z 0 * pd 0 w z) x + mc φ (fun z => u z 1 * pd 1 w z) x)|
      = |(u x 0 * mc φ (pd 0 w) x - mc φ (fun z => u z 0 * pd 0 w z) x) +
          (u x 1 * mc φ (pd 1 w) x - mc φ (fun z => u z 1 * pd 1 w z) x)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

end AnomDiss
