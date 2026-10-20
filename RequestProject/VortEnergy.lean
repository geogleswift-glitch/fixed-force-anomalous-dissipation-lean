module

public import RequestProject.VortEq

/-!
# `L⁴` energy inequalities for the mollified vorticity

Spatial part of the `L⁴` estimates: for a smooth periodic `W` with
`∂ₜW = -u·∇W + νΔW + G + R`, the rate `∫ 4W³∂ₜW` is controlled by the source terms.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace AnomDiss

lemma pd_sq_fun (W : Pt 2 → ℝ) (hW : Differentiable ℝ W) (i : Fin 2) (x : Pt 2) :
    pd i (fun y => W y ^ 2) x = 2 * W x * pd i W x := by
  rw [show (fun y => W y ^ 2) = fun y => W y * W y from funext fun y => sq _,
    pd_mul' _ _ x (hW x) (hW x)]
  ring

lemma pd_cube_fun (W : Pt 2 → ℝ) (hW : Differentiable ℝ W) (i : Fin 2) (x : Pt 2) :
    pd i (fun y => W y ^ 3) x = 3 * W x ^ 2 * pd i W x := by
  rw [show (fun y => W y ^ 3) = fun y => W y * W y ^ 2 from funext fun y => by ring,
    pd_mul' W (fun y => W y ^ 2) x (hW x) ((hW x).pow 2), pd_sq_fun W hW]
  ring

lemma isPeriodic_pow {W : Pt 2 → ℝ} (hp : IsPeriodic W) (n : ℕ) :
    IsPeriodic (fun y => W y ^ n) := fun x m => by simp [hp x m]

/-- Transport does not change `∫ W⁴`: `∫ W³ (u·∇W) = 0`. -/
lemma integral_cube_conv (u : Pt 2 → Pt 2) (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u)
    (hdiv : ∀ x, divergence u x = 0) (W : Pt 2 → ℝ) (hW : ContDiff ℝ 1 W) (hp : IsPeriodic W) :
    ∫ x in cell 2, W x ^ 3 * conv u W x = 0 := by
  have h := integral_mul_conv u hu hup hdiv (fun y => W y ^ 2) (hW.pow 2) (isPeriodic_pow hp 2)
  have e : ∀ x, conv u (fun y => W y ^ 2) x = 2 * W x * conv u W x := by
    intro x
    simp only [conv, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pd_sq_fun W (hW.differentiable one_ne_zero)]; ring
  simp only [e] at h
  have : ∫ x in cell 2, W x ^ 3 * conv u W x = (1 / 2) * ∫ x in cell 2, W x ^ 2 *
      (2 * W x * conv u W x) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [this, h, mul_zero]

/-- `∫ W³ ΔW = -3 ∫ W² |∇W|²`. -/
lemma integral_cube_lap (W : Pt 2 → ℝ) (hW : ContDiff ℝ 2 W) (hp : IsPeriodic W) :
    ∫ x in cell 2, W x ^ 3 * lap W x = -∫ x in cell 2, 3 * W x ^ 2 * gradSq W x := by
  have h1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  have hpd : ∀ i, ContDiff ℝ 1 (pd i W) := fun i => contDiff_pd_of_C2 W hW i
  have key : ∀ i : Fin 2, ∫ x in cell 2, W x ^ 3 * pd i (pd i W) x =
      -∫ x in cell 2, 3 * W x ^ 2 * pd i W x ^ 2 := by
    intro i
    rw [integral_mul_pd (fun y => W y ^ 3) (pd i W) (h1.pow 3) (hpd i) (isPeriodic_pow hp 3)
      (isPeriodic_pd W hp i) i]
    congr 2; funext x
    rw [pd_cube_fun W (h1.differentiable one_ne_zero)]; ring
  have c : ∀ i, Continuous (pd i W) := fun i => continuous_pd_of_C1 W h1 i
  have c2 : ∀ i, Continuous (pd i (pd i W)) := fun i => continuous_pd_of_C1 _ (hpd i) i
  have e1 : ∫ x in cell 2, W x ^ 3 * lap W x = ∑ i : Fin 2, ∫ x in cell 2, W x ^ 3 * pd i (pd i W) x := by
    rw [← integral_finset_sum (f := fun i x => W x ^ 3 * pd i (pd i W) x) _
      fun i _ => integrableOn_cell_of_continuous ((h1.continuous.pow 3).mul (c2 i))]
    congr 1; funext x; simp [lap]; ring
  have e2 : ∫ x in cell 2, 3 * W x ^ 2 * gradSq W x =
      ∑ i : Fin 2, ∫ x in cell 2, 3 * W x ^ 2 * pd i W x ^ 2 := by
    rw [← integral_finset_sum (f := fun i x => 3 * W x ^ 2 * pd i W x ^ 2) _
      fun i _ => integrableOn_cell_of_continuous
        ((continuous_const.mul (h1.continuous.pow 2)).mul ((c i).pow 2))]
    congr 1; funext x; simp [gradSq]; ring
  rw [e1, e2, Fin.sum_univ_two, Fin.sum_univ_two, key, key]; ring

/-- `∫ W³ ∂ᵢg = -3 ∫ W² ∂ᵢW g`. -/
lemma integral_cube_pd (W g : Pt 2 → ℝ) (hW : ContDiff ℝ 1 W) (hp : IsPeriodic W)
    (hg : ContDiff ℝ 1 g) (hgp : IsPeriodic g) (i : Fin 2) :
    ∫ x in cell 2, W x ^ 3 * pd i g x = -∫ x in cell 2, 3 * W x ^ 2 * pd i W x * g x := by
  rw [integral_mul_pd (fun y => W y ^ 3) g (hW.pow 3) hg (isPeriodic_pow hp 3) hgp i]
  congr 2; funext x
  rw [pd_cube_fun W (hW.differentiable one_ne_zero)]

lemma icell_add {f g : Pt 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x in cell 2, (f x + g x) = (∫ x in cell 2, f x) + ∫ x in cell 2, g x :=
  integral_add (integrableOn_cell_of_continuous hf) (integrableOn_cell_of_continuous hg)

lemma icell_sub {f g : Pt 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x in cell 2, (f x - g x) = (∫ x in cell 2, f x) - ∫ x in cell 2, g x :=
  integral_sub (integrableOn_cell_of_continuous hf) (integrableOn_cell_of_continuous hg)

lemma icell_mul (c : ℝ) (f : Pt 2 → ℝ) :
    ∫ x in cell 2, c * f x = c * ∫ x in cell 2, f x := integral_const_mul c f

lemma icell_mono {f g : Pt 2 → ℝ} (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≤ g x) :
    ∫ x in cell 2, f x ≤ ∫ x in cell 2, g x :=
  setIntegral_mono_on (integrableOn_cell_of_continuous hf) (integrableOn_cell_of_continuous hg)
    measurableSet_Icc fun x _ => h x

lemma integral_rate_split {u : Pt 2 → Pt 2} (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u)
    (hdiv : ∀ x, divergence u x = 0) {W Wt S : Pt 2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hp : IsPeriodic W) (hS : Continuous S) {ν : ℝ}
    (heq : ∀ x, Wt x = -conv u W x + ν * lap W x + S x) :
    ∫ x in cell 2, 2 * W x ^ 2 * (2 * W x * Wt x) =
      -(4 * ν) * (∫ x in cell 2, 3 * W x ^ 2 * gradSq W x) + ∫ x in cell 2, 4 * W x ^ 3 * S x := by
  have h1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  have cW := h1.continuous
  have cconv : Continuous (conv u W) := continuous_conv_of_C1 u hu.continuous W h1
  have clap : Continuous (lap W) := continuous_lap_of_C2 W hW
  have cA : Continuous fun x => W x ^ 3 * conv u W x := (cW.pow 3).mul cconv
  have cB : Continuous fun x => W x ^ 3 * lap W x := (cW.pow 3).mul clap
  have cC : Continuous fun x => 4 * W x ^ 3 * S x := (continuous_const.mul (cW.pow 3)).mul hS
  have e : ∫ x in cell 2, 2 * W x ^ 2 * (2 * W x * Wt x) =
      ∫ x in cell 2, ((-4 * (W x ^ 3 * conv u W x) + 4 * ν * (W x ^ 3 * lap W x)) +
        4 * W x ^ 3 * S x) := by
    congr 1; funext x; rw [heq]; ring
  have s1 : ∫ x in cell 2, ((-4 * (W x ^ 3 * conv u W x) + 4 * ν * (W x ^ 3 * lap W x)) +
      4 * W x ^ 3 * S x) = (∫ x in cell 2, (-4 * (W x ^ 3 * conv u W x) +
        4 * ν * (W x ^ 3 * lap W x))) + ∫ x in cell 2, 4 * W x ^ 3 * S x :=
    icell_add ((continuous_const.mul cA).add (continuous_const.mul cB)) cC
  have s2 : ∫ x in cell 2, (-4 * (W x ^ 3 * conv u W x) + 4 * ν * (W x ^ 3 * lap W x)) =
      (∫ x in cell 2, -4 * (W x ^ 3 * conv u W x)) + ∫ x in cell 2, 4 * ν * (W x ^ 3 * lap W x) :=
    icell_add (continuous_const.mul cA) (continuous_const.mul cB)
  rw [e, s1, s2, icell_mul, icell_mul, integral_cube_conv u hu hup hdiv W h1 hp,
    integral_cube_lap W hW hp]
  ring

lemma integral_cube_gradSq_nonneg (W : Pt 2 → ℝ) :
    0 ≤ ∫ x in cell 2, 3 * W x ^ 2 * gradSq W x :=
  setIntegral_nonneg measurableSet_Icc fun x _ => by unfold gradSq; positivity

/-- Inviscid rate bound: `∫ 4W³∂ₜW ≤ 4(a+κ)∫|W|³`. -/
lemma rate_inviscid {u : Pt 2 → Pt 2} (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u)
    (hdiv : ∀ x, divergence u x = 0) {W Wt G R : Pt 2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hp : IsPeriodic W) (hG : Continuous G) (hR : Continuous R) {ν a κ : ℝ} (hν : 0 ≤ ν)
    (heq : ∀ x, Wt x = -conv u W x + ν * lap W x + (G x + R x))
    (ha : ∀ x, |G x| ≤ a) (hκ : ∀ x, |R x| ≤ κ) :
    ∫ x in cell 2, 2 * W x ^ 2 * (2 * W x * Wt x) ≤ 4 * (a + κ) * ∫ x in cell 2, |W x| ^ 3 := by
  rw [integral_rate_split hu hup hdiv hW hp (S := fun x => G x + R x) (hG.add hR) heq]
  have hn := integral_cube_gradSq_nonneg W
  have cW := hW.continuous
  have hmono : ∫ x in cell 2, 4 * W x ^ 3 * (G x + R x) ≤
      ∫ x in cell 2, 4 * (a + κ) * |W x| ^ 3 := by
    refine icell_mono ((continuous_const.mul (cW.pow 3)).mul (hG.add hR))
      (continuous_const.mul (cW.abs.pow 3)) fun x => ?_
    have h3 : W x ^ 3 * (G x + R x) ≤ |W x| ^ 3 * (a + κ) := by
      calc W x ^ 3 * (G x + R x) ≤ |W x ^ 3 * (G x + R x)| := le_abs_self _
        _ = |W x| ^ 3 * |G x + R x| := by rw [abs_mul, abs_pow]
        _ ≤ |W x| ^ 3 * (a + κ) := mul_le_mul_of_nonneg_left
            ((abs_add_le _ _).trans (add_le_add (ha x) (hκ x))) (by positivity)
    nlinarith
  rw [icell_mul] at hmono
  nlinarith

/-- Viscous rate bound: with `G = ∂₀g₁ - ∂₁g₀` and `|gₖ| ≤ b`,
`∫ 4W³∂ₜW ≤ (6b²/ν)∫W² + 4κ∫|W|³`. -/
lemma rate_viscous {u : Pt 2 → Pt 2} (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u)
    (hdiv : ∀ x, divergence u x = 0) {W Wt g₀ g₁ R : Pt 2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hp : IsPeriodic W) (hg₀ : ContDiff ℝ 1 g₀) (hg₁ : ContDiff ℝ 1 g₁)
    (hg₀p : IsPeriodic g₀) (hg₁p : IsPeriodic g₁) (hR : Continuous R) {ν b κ : ℝ} (hν : 0 < ν)
    (heq : ∀ x, Wt x = -conv u W x + ν * lap W x + ((pd 0 g₁ x - pd 1 g₀ x) + R x))
    (hb₀ : ∀ x, |g₀ x| ≤ b) (hb₁ : ∀ x, |g₁ x| ≤ b) (hκ : ∀ x, |R x| ≤ κ) :
    ∫ x in cell 2, 2 * W x ^ 2 * (2 * W x * Wt x) ≤
      6 * b ^ 2 / ν * (∫ x in cell 2, W x ^ 2) + 4 * κ * ∫ x in cell 2, |W x| ^ 3 := by
  have h1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  have cW := hW.continuous
  have cp : ∀ i, Continuous (pd i W) := fun i => continuous_pd_of_C1 W h1 i
  have cg0 : ∀ i, Continuous (pd i g₀) := fun i => continuous_pd_of_C1 _ hg₀ i
  have cg1 : ∀ i, Continuous (pd i g₁) := fun i => continuous_pd_of_C1 _ hg₁ i
  have cS : Continuous fun x => (pd 0 g₁ x - pd 1 g₀ x) + R x := ((cg1 0).sub (cg0 1)).add hR
  rw [integral_rate_split hu hup hdiv hW hp cS heq]
  have cA : Continuous fun x => W x ^ 3 * pd 0 g₁ x := (cW.pow 3).mul (cg1 0)
  have cB : Continuous fun x => W x ^ 3 * pd 1 g₀ x := (cW.pow 3).mul (cg0 1)
  have cC : Continuous fun x => 4 * W x ^ 3 * R x := (continuous_const.mul (cW.pow 3)).mul hR
  have esplit : ∫ x in cell 2, 4 * W x ^ 3 * ((pd 0 g₁ x - pd 1 g₀ x) + R x) =
      4 * (∫ x in cell 2, W x ^ 3 * pd 0 g₁ x) - 4 * (∫ x in cell 2, W x ^ 3 * pd 1 g₀ x) +
        ∫ x in cell 2, 4 * W x ^ 3 * R x := by
    have e0 : ∫ x in cell 2, 4 * W x ^ 3 * ((pd 0 g₁ x - pd 1 g₀ x) + R x) =
        ∫ x in cell 2, ((4 * (W x ^ 3 * pd 0 g₁ x) - 4 * (W x ^ 3 * pd 1 g₀ x)) +
          4 * W x ^ 3 * R x) := by
      congr 1; funext x; ring
    have e1 : ∫ x in cell 2, ((4 * (W x ^ 3 * pd 0 g₁ x) - 4 * (W x ^ 3 * pd 1 g₀ x)) +
        4 * W x ^ 3 * R x) = (∫ x in cell 2, (4 * (W x ^ 3 * pd 0 g₁ x) -
          4 * (W x ^ 3 * pd 1 g₀ x))) + ∫ x in cell 2, 4 * W x ^ 3 * R x :=
      icell_add ((continuous_const.mul cA).sub (continuous_const.mul cB)) cC
    have e2 : ∫ x in cell 2, (4 * (W x ^ 3 * pd 0 g₁ x) - 4 * (W x ^ 3 * pd 1 g₀ x)) =
        (∫ x in cell 2, 4 * (W x ^ 3 * pd 0 g₁ x)) - ∫ x in cell 2, 4 * (W x ^ 3 * pd 1 g₀ x) :=
      icell_sub (continuous_const.mul cA) (continuous_const.mul cB)
    rw [e0, e1, e2, icell_mul, icell_mul]
  rw [esplit, integral_cube_pd W g₁ h1 hp hg₁ hg₁p 0, integral_cube_pd W g₀ h1 hp hg₀ hg₀p 1]
  have cgr : Continuous (gradSq W) := by
    unfold gradSq; exact continuous_finset_sum _ fun i _ => (cp i).pow 2
  have cX : Continuous fun x => 3 * W x ^ 2 * gradSq W x :=
    (continuous_const.mul (cW.pow 2)).mul cgr
  have cY1 : Continuous fun x => 3 * W x ^ 2 * pd 0 W x * g₁ x :=
    ((continuous_const.mul (cW.pow 2)).mul (cp 0)).mul hg₁.continuous
  have cY0 : Continuous fun x => 3 * W x ^ 2 * pd 1 W x * g₀ x :=
    ((continuous_const.mul (cW.pow 2)).mul (cp 1)).mul hg₀.continuous
  have hcomb : ∫ x in cell 2, (-(4 * ν) * (3 * W x ^ 2 * gradSq W x) -
      4 * (3 * W x ^ 2 * pd 0 W x * g₁ x) + 4 * (3 * W x ^ 2 * pd 1 W x * g₀ x)) ≤
      ∫ x in cell 2, 6 * b ^ 2 / ν * W x ^ 2 := by
    refine icell_mono (((continuous_const.mul cX).sub (continuous_const.mul cY1)).add
      (continuous_const.mul cY0)) (continuous_const.mul (cW.pow 2)) fun x => ?_
    have hg0 : g₀ x ^ 2 ≤ b ^ 2 := by
      have := hb₀ x; nlinarith [abs_nonneg (g₀ x), sq_abs (g₀ x)]
    have hg1 : g₁ x ^ 2 ≤ b ^ 2 := by
      have := hb₁ x; nlinarith [abs_nonneg (g₁ x), sq_abs (g₁ x)]
    simp only [gradSq, Fin.sum_univ_two]
    set p := pd 0 W x
    set q := pd 1 W x
    have key : -(12 * ν ^ 2) * (p ^ 2 + q ^ 2) - 12 * ν * (p * g₁ x) + 12 * ν * (q * g₀ x) ≤
        6 * b ^ 2 := by
      nlinarith [sq_nonneg (2 * ν * p + g₁ x), sq_nonneg (2 * ν * q - g₀ x)]
    have hW2 : 0 ≤ W x ^ 2 := sq_nonneg _
    rw [div_mul_eq_mul_div, le_div_iff₀ hν]
    nlinarith [mul_le_mul_of_nonneg_left key hW2]
  have l1 : ∫ x in cell 2, (-(4 * ν) * (3 * W x ^ 2 * gradSq W x) -
      4 * (3 * W x ^ 2 * pd 0 W x * g₁ x) + 4 * (3 * W x ^ 2 * pd 1 W x * g₀ x)) =
      (∫ x in cell 2, (-(4 * ν) * (3 * W x ^ 2 * gradSq W x) -
        4 * (3 * W x ^ 2 * pd 0 W x * g₁ x))) +
        ∫ x in cell 2, 4 * (3 * W x ^ 2 * pd 1 W x * g₀ x) :=
    icell_add ((continuous_const.mul cX).sub (continuous_const.mul cY1)) (continuous_const.mul cY0)
  have l2 : ∫ x in cell 2, (-(4 * ν) * (3 * W x ^ 2 * gradSq W x) -
      4 * (3 * W x ^ 2 * pd 0 W x * g₁ x)) =
      (∫ x in cell 2, -(4 * ν) * (3 * W x ^ 2 * gradSq W x)) -
        ∫ x in cell 2, 4 * (3 * W x ^ 2 * pd 0 W x * g₁ x) :=
    icell_sub (continuous_const.mul cX) (continuous_const.mul cY1)
  rw [l1, l2, icell_mul, icell_mul, icell_mul, icell_mul] at hcomb
  have hR' : ∫ x in cell 2, 4 * W x ^ 3 * R x ≤ ∫ x in cell 2, 4 * κ * |W x| ^ 3 := by
    refine icell_mono cC (continuous_const.mul (cW.abs.pow 3)) fun x => ?_
    have : W x ^ 3 * R x ≤ |W x| ^ 3 * κ := by
      calc W x ^ 3 * R x ≤ |W x ^ 3 * R x| := le_abs_self _
        _ = |W x| ^ 3 * |R x| := by rw [abs_mul, abs_pow]
        _ ≤ |W x| ^ 3 * κ := mul_le_mul_of_nonneg_left (hκ x) (by positivity)
    nlinarith
  rw [icell_mul] at hR'
  linarith

/-! ### Hölder-type bounds on the probability space `cell 2` -/

lemma icell_const (c : ℝ) : ∫ _x in cell 2, c = c := by
  rw [setIntegral_const, volume_real_cell2, one_smul]

lemma integral_abs_cube_le {W : Pt 2 → ℝ} (hW : Continuous W) {Z : ℝ} (hZ : 0 < Z)
    (h4 : ∫ x in cell 2, W x ^ 4 ≤ Z ^ 4) : ∫ x in cell 2, |W x| ^ 3 ≤ Z ^ 3 := by
  have hpt : ∀ x, 4 * Z * |W x| ^ 3 ≤ 3 * W x ^ 4 + Z ^ 4 := by
    intro x
    have ha := abs_nonneg (W x)
    have e : W x ^ 4 = |W x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [e]
    nlinarith [sq_nonneg (|W x| - Z), mul_nonneg (sq_nonneg (|W x| - Z))
      (add_nonneg (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sq_nonneg (|W x|)))
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha) hZ.le)) (sq_nonneg Z))]
  have hm : ∫ x in cell 2, 4 * Z * |W x| ^ 3 ≤ ∫ x in cell 2, (3 * W x ^ 4 + Z ^ 4) :=
    icell_mono (continuous_const.mul (hW.abs.pow 3))
      ((continuous_const.mul (hW.pow 4)).add continuous_const) hpt
  rw [icell_add (f := fun x => 3 * W x ^ 4) (g := fun _ => Z ^ 4)
    (continuous_const.mul (hW.pow 4)) continuous_const, icell_mul, icell_mul, icell_const] at hm
  have : 4 * Z * ∫ x in cell 2, |W x| ^ 3 ≤ 4 * Z * Z ^ 3 := by nlinarith
  nlinarith

lemma integral_sq_le_of_four {W : Pt 2 → ℝ} (hW : Continuous W) {Z : ℝ} (hZ : 0 < Z)
    (h4 : ∫ x in cell 2, W x ^ 4 ≤ Z ^ 2) : ∫ x in cell 2, W x ^ 2 ≤ Z := by
  have hpt : ∀ x, 2 * Z * W x ^ 2 ≤ W x ^ 4 + Z ^ 2 := fun x => by
    nlinarith [sq_nonneg (W x ^ 2 - Z)]
  have hm : ∫ x in cell 2, 2 * Z * W x ^ 2 ≤ ∫ x in cell 2, (W x ^ 4 + Z ^ 2) :=
    icell_mono (continuous_const.mul (hW.pow 2)) ((hW.pow 4).add continuous_const) hpt
  rw [icell_add (f := fun x => W x ^ 4) (g := fun _ => Z ^ 2) (hW.pow 4) continuous_const,
    icell_mul, icell_const] at hm
  nlinarith

lemma integral_abs_cube_le_sup {W : Pt 2 → ℝ} (hW : Continuous W) {M : ℝ}
    (hM : ∀ x, |W x| ≤ M) : ∫ x in cell 2, |W x| ^ 3 ≤ M * ∫ x in cell 2, W x ^ 2 := by
  rw [← icell_mul]
  refine icell_mono (hW.abs.pow 3) (continuous_const.mul (hW.pow 2)) fun x => ?_
  have : |W x| ^ 3 = |W x| * W x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
  rw [this]
  exact mul_le_mul_of_nonneg_right (hM x) (sq_nonneg _)

/-! ### An ODE comparison for roots -/

/-- If `f ≥ 0` has derivative `h` with `h ≤ n c Z^{n-1}` whenever `f ≤ Zⁿ`, then
`f^{1/n}` grows at most linearly with slope `c`. -/
lemma root_growth {a b c : ℝ} (hab : a ≤ b) {f h : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hf : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, h s) (hh : ContinuousOn h (Icc a b))
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hle : ∀ s ∈ Ioo a b, ∀ Z : ℝ, 0 < Z → f s ≤ Z ^ n → h s ≤ n * c * Z ^ (n - 1)) :
    f b ^ (1 / n : ℝ) ≤ f a ^ (1 / n : ℝ) + c * (b - a) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ 1 / n := by positivity
  -- derivative of `f`
  have hprim : ContinuousOn (fun t => ∫ s in a..t, h s) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := h) (a := a)
      (b := b) (by rw [uIcc_of_le hab]; exact hh.integrableOn_compact isCompact_Icc)
    rwa [uIcc_of_le hab] at this
  have hfc : ContinuousOn f (Icc a b) :=
    (continuousOn_const.add hprim).congr fun t ht => hf t ht
  have hfd : ∀ t ∈ Ioo a b, HasDerivAt f (h t) t := by
    intro t ht
    have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hd : HasDerivAt (fun t => ∫ s in a..t, h s) (h t) t := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ (hh.continuousAt hnhds)
      · exact (hh.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
      · exact (hh.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
    refine (hd.const_add (f a)).congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with s hs using hf s hs
  -- the bound for each `δ > 0`
  have key : ∀ δ : ℝ, 0 < δ → f b ^ (1 / n : ℝ) ≤ (f a + δ) ^ (1 / n : ℝ) + c * (b - a) := by
    intro δ hδ
    set g : ℝ → ℝ := fun t => (f t + δ) ^ (1 / n : ℝ) with hg
    have hpos : ∀ t ∈ Icc a b, 0 < f t + δ := fun t ht => by linarith [hf0 t ht]
    have hgc : ContinuousOn g (Icc a b) :=
      (hfc.add continuousOn_const).rpow_const fun t _ => Or.inr hp0
    have hgd : ∀ t ∈ Ioo a b, HasDerivAt g (h t * (1 / n) * (f t + δ) ^ ((1 / n : ℝ) - 1)) t :=
      fun t ht => ((hfd t ht).add_const δ).rpow_const
        (Or.inl (hpos t (Ioo_subset_Icc_self ht)).ne')
    have hgle : ∀ t ∈ Ioo a b, h t * (1 / n) * (f t + δ) ^ ((1 / n : ℝ) - 1) ≤ c := by
      intro t ht
      have hP := hpos t (Ioo_subset_Icc_self ht)
      set Z := g t with hZ
      have hZpos : 0 < Z := Real.rpow_pos_of_pos hP _
      have hZn : Z ^ n = f t + δ := by
        rw [hZ, hg, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
        field_simp; simp
      have hb := hle t ht Z hZpos (by rw [hZn]; linarith)
      have hpow : (f t + δ) ^ ((1 / n : ℝ) - 1) = 1 / Z ^ (n - 1) := by
        rw [Real.rpow_sub hP, Real.rpow_one, show (f t + δ) ^ (1 / (n : ℝ)) = Z from rfl, ← hZn]
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have : Z ^ (m + 1) = Z ^ m * Z := pow_succ _ _
        rw [this]
        have hZm : 0 < Z ^ m := pow_pos hZpos m
        field_simp
      rw [hpow]
      have hZm : 0 < Z ^ (n - 1) := pow_pos hZpos _
      rw [show h t * (1 / n) * (1 / Z ^ (n - 1)) = h t / (n * Z ^ (n - 1)) by field_simp,
        div_le_iff₀ (by positivity)]
      nlinarith
    have hanti : AntitoneOn (fun t => g t - c * t) (Icc a b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a b) (hgc.sub (continuousOn_const.mul
        continuousOn_id)) ?_ ?_
      · rw [interior_Icc]
        exact fun t ht => ((hgd t ht).sub ((hasDerivAt_id' t).const_mul c)).differentiableAt
          |>.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        have hd : HasDerivAt (fun t => g t - c * t)
            (h t * (1 / n) * (f t + δ) ^ ((1 / n : ℝ) - 1) - c * 1) t :=
          (hgd t ht).sub ((hasDerivAt_id' t).const_mul c)
        rw [hd.deriv]
        have := hgle t ht
        linarith
    have h1 := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simp only [hg] at h1
    have h2 : f b ^ (1 / n : ℝ) ≤ (f b + δ) ^ (1 / n : ℝ) :=
      Real.rpow_le_rpow (hf0 b ⟨hab, le_rfl⟩) (by linarith) hp0
    linarith
  -- let `δ → 0`
  have hlim : Tendsto (fun δ : ℝ => (f a + δ) ^ (1 / n : ℝ) + c * (b - a)) (𝓝[>] 0)
      (𝓝 (f a ^ (1 / n : ℝ) + c * (b - a))) := by
    have hc : Continuous fun δ : ℝ => (f a + δ) ^ (1 / n : ℝ) + c * (b - a) :=
      ((continuous_const.add continuous_id).rpow_const fun _ => Or.inr hp0).add continuous_const
    have := hc.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)

end AnomDiss
