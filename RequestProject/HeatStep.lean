module

public import RequestProject.Fourier
public import RequestProject.TaylorHolder

/-!
# Gaussian moments and one heat step

Moments of the Gaussian law `gauss2 v` on `ℝ²`, basic properties of the heat operator
`heatOp v`, and the second-order expansion of one heat step applied to `f ∘ ψ` when `ψ` is close
to the identity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

instance gauss2_isProb (v : ℝ≥0) : IsProbabilityMeasure (gauss2 v) := by
  unfold gauss2; infer_instance

/-! ### One-dimensional moments -/

/-- The absolute moment `∫ |x|^p` of the standard Gaussian. -/
def gmom (p : ℝ) : ℝ := ∫ x, |x| ^ p ∂(gaussianReal 0 1)

lemma measurable_abs_rpow (p : ℝ) : Measurable fun x : ℝ => |x| ^ p :=
  measurable_id.abs.pow_const p

lemma gmom_nonneg (p : ℝ) : 0 ≤ gmom p := integral_nonneg fun _ => by positivity

lemma gaussianReal_eq_map (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · ext; simp

lemma integrable_abs_rpow_gaussianReal (v : ℝ≥0) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 v) := by
  have hne : NNReal.mk p hp.le ≠ 0 :=
    NNReal.coe_ne_zero.mp (by simpa only [NNReal.coe_mk] using hp.ne')
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) (NNReal.mk p hp.le)).integrable_norm_rpow
    (ENNReal.coe_ne_zero.2 hne) ENNReal.coe_ne_top
  simpa only [id_eq, Real.norm_eq_abs, ENNReal.coe_toReal, NNReal.coe_mk] using h

lemma integral_abs_rpow_gaussianReal (v : ℝ≥0) (p : ℝ) :
    ∫ x, |x| ^ p ∂(gaussianReal 0 v) = (v : ℝ) ^ (p / 2) * gmom p := by
  rw [gaussianReal_eq_map, integral_map (by fun_prop)
    (measurable_abs_rpow p).aestronglyMeasurable, gmom, ← integral_const_mul]
  congr 1; funext x
  rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow, show (v:ℝ) ^ (p / 2) = ((v:ℝ) ^ (1 / 2 : ℝ)) ^ p by
      rw [← Real.rpow_mul (NNReal.coe_nonneg v)]; ring_nf]

lemma integral_id_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_of_integral_eq_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v)
    (by fun_prop) integral_id_gaussianReal
  rw [variance_fun_id_gaussianReal] at h
  exact h.symm

/-! ### Two-dimensional moments -/

lemma integral_gauss2_coord {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (v : ℝ≥0)
    (i : Fin 2) {F : ℝ → G} (hF : AEStronglyMeasurable F (gaussianReal 0 v)) :
    ∫ ζ, F (ζ i) ∂(gauss2 v) = ∫ x, F x ∂(gaussianReal 0 v) := by
  have hmp := measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 v) i
  rw [← hmp.map_eq] at hF
  rw [← hmp.map_eq, integral_map (measurable_pi_apply i).aemeasurable hF]
  rfl

lemma integrable_gauss2_coord (v : ℝ≥0) (i : Fin 2) {F : ℝ → ℝ}
    (hF : AEStronglyMeasurable F (gaussianReal 0 v))
    (hi : Integrable F (gaussianReal 0 v)) : Integrable (fun ζ : Pt 2 => F (ζ i)) (gauss2 v) := by
  have hmp := measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 v) i
  exact (hmp.integrable_comp hF).2 hi

lemma integral_gauss2_coord_id (v : ℝ≥0) (i : Fin 2) : ∫ ζ, ζ i ∂(gauss2 v) = 0 := by
  rw [integral_gauss2_coord v i (F := fun x => x) continuous_id.aestronglyMeasurable, integral_id_gaussianReal]

lemma integrable_gauss2_coord_id (v : ℝ≥0) (i : Fin 2) :
    Integrable (fun ζ : Pt 2 => ζ i) (gauss2 v) :=
  integrable_gauss2_coord v i (F := fun x => x) continuous_id.aestronglyMeasurable
    ((memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl)

lemma integrable_gauss2_coord_mul (v : ℝ≥0) (i j : Fin 2) :
    Integrable (fun ζ : Pt 2 => ζ i * ζ j) (gauss2 v) := by
  have hi := integrable_gauss2_coord v i (F := fun x => |x| ^ (2:ℝ)) (measurable_abs_rpow _).aestronglyMeasurable
    (integrable_abs_rpow_gaussianReal v two_pos)
  have hj := integrable_gauss2_coord v j (F := fun x => |x| ^ (2:ℝ)) (measurable_abs_rpow _).aestronglyMeasurable
    (integrable_abs_rpow_gaussianReal v two_pos)
  refine (hi.add hj).mono' (by fun_prop) (Eventually.of_forall fun ζ => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, Real.rpow_two, sq_abs]
  nlinarith [abs_nonneg (ζ i), abs_nonneg (ζ j), sq_abs (ζ i), sq_abs (ζ j),
    sq_nonneg (|ζ i| - |ζ j|)]

lemma integral_gauss2_coord_mul (v : ℝ≥0) (i j : Fin 2) :
    ∫ ζ, ζ i * ζ j ∂(gauss2 v) = if i = j then (v : ℝ) else 0 := by
  split_ifs with h
  · subst h
    rw [integral_gauss2_coord v i (F := fun x => x * x) (by fun_prop)]
    simpa [sq] using integral_id_sq_gaussianReal v
  · have hprod : ∀ ζ : Pt 2, ζ i * ζ j = ∏ k : Fin 2, (fun _ (x : ℝ) => x) k (ζ k) := by
      intro ζ
      fin_cases i <;> fin_cases j <;> simp_all [Fin.prod_univ_two, mul_comm]
    simp_rw [hprod]
    rw [gauss2, integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ (x : ℝ) => x)]
    simp [integral_id_gaussianReal]

lemma norm_rpow_le_sum (ζ : Pt 2) {p : ℝ} (hp : 0 ≤ p) :
    ‖ζ‖ ^ p ≤ |ζ 0| ^ p + |ζ 1| ^ p := by
  have h : ‖ζ‖ ≤ max |ζ 0| |ζ 1| := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine (Real.rpow_le_rpow (norm_nonneg _) h hp).trans ?_
  rcases le_total |ζ 0| |ζ 1| with h' | h'
  · rw [max_eq_right h']; have := Real.rpow_nonneg (abs_nonneg (ζ 0)) p; linarith
  · rw [max_eq_left h']; have := Real.rpow_nonneg (abs_nonneg (ζ 1)) p; linarith

lemma integrable_gauss2_norm_rpow (v : ℝ≥0) {p : ℝ} (hp : 0 < p) :
    Integrable (fun ζ : Pt 2 => ‖ζ‖ ^ p) (gauss2 v) := by
  have h0 := integrable_gauss2_coord v 0 (F := fun x => |x| ^ p) (measurable_abs_rpow _).aestronglyMeasurable
    (integrable_abs_rpow_gaussianReal v hp)
  have h1 := integrable_gauss2_coord v 1 (F := fun x => |x| ^ p) (measurable_abs_rpow _).aestronglyMeasurable
    (integrable_abs_rpow_gaussianReal v hp)
  refine (h0.add h1).mono' (measurable_norm.pow_const p).aestronglyMeasurable
    (Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_rpow_le_sum ζ hp.le

lemma integral_gauss2_norm_rpow_le (v : ℝ≥0) {p : ℝ} (hp : 0 < p) :
    ∫ ζ, ‖ζ‖ ^ p ∂(gauss2 v) ≤ 2 * gmom p * (v : ℝ) ^ (p / 2) := by
  have h0 := integrable_gauss2_coord v 0 (F := fun x => |x| ^ p) (measurable_abs_rpow _).aestronglyMeasurable
    (integrable_abs_rpow_gaussianReal v hp)
  have h1 := integrable_gauss2_coord v 1 (F := fun x => |x| ^ p) (measurable_abs_rpow _).aestronglyMeasurable
    (integrable_abs_rpow_gaussianReal v hp)
  calc ∫ ζ, ‖ζ‖ ^ p ∂(gauss2 v) ≤ ∫ ζ, (|ζ 0| ^ p + |ζ 1| ^ p) ∂(gauss2 v) :=
        integral_mono (integrable_gauss2_norm_rpow v hp) (h0.add h1)
          fun ζ => norm_rpow_le_sum ζ hp.le
    _ = 2 * gmom p * (v : ℝ) ^ (p / 2) := by
        rw [integral_add h0 h1, integral_gauss2_coord v 0 (F := fun x => |x| ^ p) (measurable_abs_rpow _).aestronglyMeasurable,
          integral_gauss2_coord v 1 (F := fun x => |x| ^ p) (measurable_abs_rpow _).aestronglyMeasurable,
          integral_abs_rpow_gaussianReal v p]
        ring

/-! ### The heat operator -/

lemma norm_heatOp_le {g : Pt 2 → ℂ} {C : ℝ} (hg : ∀ x, ‖g x‖ ≤ C) (v : ℝ≥0) (x : Pt 2) :
    ‖heatOp v g x‖ ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := gauss2 v) (f := fun ζ => g (x + ζ))
    (C := C) (Eventually.of_forall fun ζ => hg _)
  simpa only [heatOp, probReal_univ, mul_one] using this

lemma integrable_of_continuous_bdd {g : Pt 2 → ℂ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) (v : ℝ≥0) : Integrable g (gauss2 v) :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hC)

lemma continuous_heatOp {g : Pt 2 → ℂ} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (v : ℝ≥0) : Continuous (heatOp v g) := by
  unfold heatOp
  refine continuous_of_dominated (bound := fun _ => C)
    (fun x => (hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun ζ => hC _) (integrable_const C)
    (Eventually.of_forall fun ζ => hg.comp (continuous_id.add continuous_const))

lemma heatOp_add {g₁ g₂ : Pt 2 → ℂ} (h₁ : Continuous g₁) (h₂ : Continuous g₂) {C₁ C₂ : ℝ}
    (hC₁ : ∀ x, ‖g₁ x‖ ≤ C₁) (hC₂ : ∀ x, ‖g₂ x‖ ≤ C₂) (v : ℝ≥0) (x : Pt 2) :
    heatOp v (fun y => g₁ y + g₂ y) x = heatOp v g₁ x + heatOp v g₂ x := by
  unfold heatOp
  exact integral_add
    (integrable_of_continuous_bdd (h₁.comp (continuous_const.add continuous_id)) (fun _ => hC₁ _) v)
    (integrable_of_continuous_bdd (h₂.comp (continuous_const.add continuous_id)) (fun _ => hC₂ _) v)

/-! ### One heat step applied to `f ∘ ψ` -/

/-- Expansion of one heat step: if `ψ - id` is `lam`-Lipschitz (`lam ≤ 1`), then
`H_v(f ∘ ψ)(y) = f(ψ y) + (v/2) Δf(ψ y) + O(lam √v + lam v + v^{1+β/2})`. -/
theorem heat_step_expansion {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f) {D0 D1 D2 H β lam : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hD0 : ∀ x, ‖f x‖ ≤ D0) (hD1 : ∀ j x, ‖pd j f x‖ ≤ D1)
    (hD2 : ∀ i j x, ‖pd i (pd j f) x‖ ≤ D2)
    (hH : ∀ i j x y, ‖pd i (pd j f) x - pd i (pd j f) y‖ ≤ H * ‖x - y‖ ^ β)
    {ψ : Pt 2 → Pt 2} (hψ : Continuous ψ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hψl : ∀ x y, ‖(ψ x - x) - (ψ y - y)‖ ≤ lam * ‖x - y‖) (v : ℝ≥0) (y : Pt 2) :
    ‖heatOp v (f ∘ ψ) y - f (ψ y) - ((v : ℝ) / 2) • lap f (ψ y)‖ ≤
      2 * D1 * lam * ∫ ζ, ‖ζ‖ ^ (1 : ℝ) ∂(gauss2 v) +
      6 * D2 * lam * ∫ ζ, ‖ζ‖ ^ (2 : ℝ) ∂(gauss2 v) +
      32 * H * ∫ ζ, ‖ζ‖ ^ (2 + β) ∂(gauss2 v) := by
  set z := ψ y with hz
  set δ : Pt 2 → Pt 2 := fun ζ => ψ (y + ζ) - z with hδ
  have hδc : Continuous δ := (hψ.comp (continuous_const.add continuous_id)).sub continuous_const
  have hD1n : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0 0)
  have hD2n : 0 ≤ D2 := (norm_nonneg _).trans (hD2 0 0 0)
  have hHn : 0 ≤ H := by
    have := hH 0 0 (Pi.single 0 1) 0
    have h1 : (0:ℝ) ≤ H * ‖(Pi.single 0 1 : Pt 2) - 0‖ ^ β := (norm_nonneg _).trans this
    rwa [sub_zero, Pi.norm_single, norm_one, Real.one_rpow, mul_one] at h1
  -- the linear and quadratic parts
  set L : Pt 2 → ℂ := fun ζ => ∑ j, ζ j • pd j f z with hL
  set Q : Pt 2 → ℂ := fun ζ => (1 / 2 : ℝ) • ∑ j, ∑ i, (ζ j * ζ i) • pd i (pd j f) z with hQ
  have hLi : Integrable L (gauss2 v) :=
    integrable_finset_sum _ fun j _ => (integrable_gauss2_coord_id v j).smul_const _
  have hQi : Integrable Q (gauss2 v) := by
    have hs : Integrable (fun ζ : Pt 2 => ∑ j, ∑ i, (ζ j * ζ i) • pd i (pd j f) z) (gauss2 v) :=
      integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ =>
        (integrable_gauss2_coord_mul v j i).smul_const _
    have := hs.smul (1 / 2 : ℝ)
    exact this
  have hLint : ∫ ζ, L ζ ∂(gauss2 v) = 0 := by
    rw [hL, integral_finset_sum _ fun j _ => (integrable_gauss2_coord_id v j).smul_const _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_smul_const, integral_gauss2_coord_id, zero_smul]
  have hQint : ∫ ζ, Q ζ ∂(gauss2 v) = ((v : ℝ) / 2) • lap f z := by
    rw [hQ, integral_smul, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ =>
      (integrable_gauss2_coord_mul v j i).smul_const _]
    simp_rw [integral_finset_sum _ fun i _ => (integrable_gauss2_coord_mul v _ i).smul_const _,
      integral_smul_const, integral_gauss2_coord_mul]
    simp only [lap, Fin.sum_univ_two, Fin.isValue, ite_smul, zero_smul, smul_add]
    simp
    ring_nf
  -- pointwise bound on the integrand
  have hδb : ∀ ζ, ‖δ ζ - ζ‖ ≤ lam * ‖ζ‖ := by
    intro ζ
    have := hψl (y + ζ) y
    have e : δ ζ - ζ = (ψ (y + ζ) - (y + ζ)) - (ψ y - y) := by simp only [hδ, hz]; abel
    rw [e]; simpa using this
  have hδn : ∀ ζ, ‖δ ζ‖ ≤ 2 * ‖ζ‖ := by
    intro ζ
    have h2 := hδb ζ
    calc ‖δ ζ‖ = ‖ζ + (δ ζ - ζ)‖ := by congr 1; abel
      _ ≤ ‖ζ‖ + lam * ‖ζ‖ := (norm_add_le _ _).trans (by linarith)
      _ ≤ 2 * ‖ζ‖ := by nlinarith [norm_nonneg ζ]
  set bd : Pt 2 → ℝ := fun ζ => 2 * D1 * lam * ‖ζ‖ ^ (1 : ℝ) + 6 * D2 * lam * ‖ζ‖ ^ (2 : ℝ) +
    32 * H * ‖ζ‖ ^ (2 + β) with hbd
  set g : Pt 2 → ℂ := fun ζ => f (z + δ ζ) - f z - L ζ - Q ζ with hg
  have hgb : ∀ ζ, ‖g ζ‖ ≤ bd ζ := by
    intro ζ
    have hT := taylor2_holder hf hβ0.le hH z (δ ζ)
    set Lδ : ℂ := ∑ j, δ ζ j • pd j f z
    set Qδ : ℂ := (1 / 2 : ℝ) • ∑ j, ∑ i, (δ ζ j * δ ζ i) • pd i (pd j f) z
    have e : g ζ = (f (z + δ ζ) - f z - Lδ - Qδ) + (Lδ - L ζ) + (Qδ - Q ζ) := by
      simp only [hg]; abel
    have hcoord : ∀ j, ‖δ ζ j - ζ j‖ ≤ lam * ‖ζ‖ := fun j =>
      (norm_le_pi_norm (δ ζ - ζ) j).trans (hδb ζ)
    have hLb : ‖Lδ - L ζ‖ ≤ 2 * D1 * lam * ‖ζ‖ := by
      have e2 : Lδ - L ζ = ∑ j, (δ ζ j - ζ j) • pd j f z := by
        simp only [Lδ, hL, ← Finset.sum_sub_distrib, sub_smul]
      rw [e2]
      refine (norm_sum_le _ _).trans ?_
      have : ∀ j, ‖(δ ζ j - ζ j) • pd j f z‖ ≤ lam * ‖ζ‖ * D1 := fun j => by
        rw [norm_smul]
        exact mul_le_mul (hcoord j) (hD1 j z) (norm_nonneg _) (by positivity)
      calc _ ≤ ∑ j : Fin 2, lam * ‖ζ‖ * D1 := Finset.sum_le_sum fun j _ => this j
        _ = 2 * D1 * lam * ‖ζ‖ := by simp; ring
    have hQb : ‖Qδ - Q ζ‖ ≤ 6 * D2 * lam * ‖ζ‖ ^ 2 := by
      have e2 : Qδ - Q ζ = (1 / 2 : ℝ) • ∑ j, ∑ i,
          (δ ζ j * δ ζ i - ζ j * ζ i) • pd i (pd j f) z := by
        simp only [Qδ, hQ, ← smul_sub, ← Finset.sum_sub_distrib, sub_smul]
      rw [e2, norm_smul]
      have hterm : ∀ i j, ‖(δ ζ j * δ ζ i - ζ j * ζ i) • pd i (pd j f) z‖ ≤
          3 * lam * ‖ζ‖ ^ 2 * D2 := by
        intro i j
        rw [norm_smul]
        refine mul_le_mul ?_ (hD2 i j z) (norm_nonneg _) (by positivity)
        have e3 : δ ζ j * δ ζ i - ζ j * ζ i = (δ ζ j - ζ j) * δ ζ i + ζ j * (δ ζ i - ζ i) := by
          ring
        rw [e3]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        have a1 := hcoord j
        have a2 := hcoord i
        have a3 : ‖δ ζ i‖ ≤ 2 * ‖ζ‖ := (norm_le_pi_norm (δ ζ) i).trans (hδn ζ)
        have a4 : ‖ζ j‖ ≤ ‖ζ‖ := norm_le_pi_norm ζ j
        calc ‖δ ζ j - ζ j‖ * ‖δ ζ i‖ + ‖ζ j‖ * ‖δ ζ i - ζ i‖
            ≤ (lam * ‖ζ‖) * (2 * ‖ζ‖) + ‖ζ‖ * (lam * ‖ζ‖) := by
              gcongr
          _ = 3 * lam * ‖ζ‖ ^ 2 := by ring
      calc ‖(1 / 2 : ℝ)‖ * ‖∑ j, ∑ i, (δ ζ j * δ ζ i - ζ j * ζ i) • pd i (pd j f) z‖
          ≤ (1 / 2) * ∑ j : Fin 2, ∑ i : Fin 2, 3 * lam * ‖ζ‖ ^ 2 * D2 := by
            rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i j))
        _ = 6 * D2 * lam * ‖ζ‖ ^ 2 := by simp; ring
    have hRb : 4 * H * ‖δ ζ‖ ^ (2 + β) ≤ 32 * H * ‖ζ‖ ^ (2 + β) := by
      have h1 : ‖δ ζ‖ ^ (2 + β) ≤ (2 * ‖ζ‖) ^ (2 + β) :=
        Real.rpow_le_rpow (norm_nonneg _) (hδn ζ) (by linarith)
      have h2 : (2 * ‖ζ‖) ^ (2 + β) = 2 ^ (2 + β) * ‖ζ‖ ^ (2 + β) :=
        Real.mul_rpow (by norm_num) (norm_nonneg _)
      have h3 : (2:ℝ) ^ (2 + β) ≤ 8 := by
        calc (2:ℝ) ^ (2 + β) ≤ 2 ^ (3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by linarith)
          _ = 8 := by norm_num
      have h4 : 0 ≤ ‖ζ‖ ^ (2 + β) := by positivity
      calc 4 * H * ‖δ ζ‖ ^ (2 + β) ≤ 4 * H * (2 ^ (2 + β) * ‖ζ‖ ^ (2 + β)) := by
            rw [← h2]; gcongr
        _ ≤ 4 * H * (8 * ‖ζ‖ ^ (2 + β)) := by gcongr
        _ = 32 * H * ‖ζ‖ ^ (2 + β) := by ring
    rw [e, hbd]
    simp only [Real.rpow_one, Real.rpow_two]
    calc ‖f (z + δ ζ) - f z - Lδ - Qδ + (Lδ - L ζ) + (Qδ - Q ζ)‖
        ≤ ‖f (z + δ ζ) - f z - Lδ - Qδ‖ + ‖Lδ - L ζ‖ + ‖Qδ - Q ζ‖ := norm_add₃_le
      _ ≤ 32 * H * ‖ζ‖ ^ (2 + β) + 2 * D1 * lam * ‖ζ‖ + 6 * D2 * lam * ‖ζ‖ ^ 2 := by
          gcongr; exact hT.trans hRb
      _ = _ := by ring
  -- integrability and conclusion
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := by simp only [hg, hL, hQ]; fun_prop
  have hm : ∀ p : ℝ, 0 < p → Integrable (fun ζ : Pt 2 => ‖ζ‖ ^ p) (gauss2 v) :=
    fun p hp => integrable_gauss2_norm_rpow v hp
  have hbdi : Integrable bd (gauss2 v) :=
    (((hm 1 one_pos).const_mul _).add ((hm 2 two_pos).const_mul _)).add
      ((hm (2 + β) (by linarith)).const_mul _)
  have hgi : Integrable g (gauss2 v) :=
    hbdi.mono' hgc.aestronglyMeasurable (Eventually.of_forall hgb)
  have hFi : Integrable (fun ζ => f (z + δ ζ)) (gauss2 v) :=
    Integrable.of_bound (hfc.comp (continuous_const.add hδc)).aestronglyMeasurable D0
      (Eventually.of_forall fun ζ => hD0 _)
  have hheat : heatOp v (f ∘ ψ) y = ∫ ζ, f (z + δ ζ) ∂(gauss2 v) := by
    unfold heatOp
    congr 1; funext ζ
    simp [hδ]
  have hint : ∫ ζ, g ζ ∂(gauss2 v) =
      heatOp v (f ∘ ψ) y - f (ψ y) - ((v : ℝ) / 2) • lap f (ψ y) := by
    have e1 : ∫ ζ, g ζ ∂(gauss2 v) =
        (∫ ζ, (f (z + δ ζ) - f z - L ζ) ∂(gauss2 v)) - ∫ ζ, Q ζ ∂(gauss2 v) :=
      integral_sub ((hFi.sub (integrable_const _)).sub hLi) hQi
    have e2 : ∫ ζ, (f (z + δ ζ) - f z - L ζ) ∂(gauss2 v) =
        (∫ ζ, (f (z + δ ζ) - f z) ∂(gauss2 v)) - ∫ ζ, L ζ ∂(gauss2 v) :=
      integral_sub (hFi.sub (integrable_const _)) hLi
    have e3 : ∫ ζ, (f (z + δ ζ) - f z) ∂(gauss2 v) =
        (∫ ζ, f (z + δ ζ) ∂(gauss2 v)) - ∫ _ζ, f z ∂(gauss2 v) :=
      integral_sub hFi (integrable_const _)
    rw [e1, e2, e3, hLint, hQint, integral_const, hheat]
    simp [hz]
  rw [← hint]
  refine (norm_integral_le_of_norm_le hbdi (Eventually.of_forall hgb)).trans (le_of_eq ?_)
  have i1 := (hm 1 one_pos).const_mul (2 * D1 * lam)
  have i2 := (hm 2 two_pos).const_mul (6 * D2 * lam)
  have i3 := (hm (2 + β) (by linarith)).const_mul (32 * H)
  have e1 : ∫ ζ, bd ζ ∂(gauss2 v) = (∫ ζ, (2 * D1 * lam * ‖ζ‖ ^ (1:ℝ) +
      6 * D2 * lam * ‖ζ‖ ^ (2:ℝ)) ∂(gauss2 v)) + ∫ ζ, 32 * H * ‖ζ‖ ^ (2 + β) ∂(gauss2 v) :=
    integral_add (i1.add i2) i3
  have e2 : ∫ ζ, (2 * D1 * lam * ‖ζ‖ ^ (1:ℝ) + 6 * D2 * lam * ‖ζ‖ ^ (2:ℝ)) ∂(gauss2 v) =
      (∫ ζ, 2 * D1 * lam * ‖ζ‖ ^ (1:ℝ) ∂(gauss2 v)) +
        ∫ ζ, 6 * D2 * lam * ‖ζ‖ ^ (2:ℝ) ∂(gauss2 v) := integral_add i1 i2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]

end AnomDiss
