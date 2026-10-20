module

public import RequestProject.SplitRep
public import RequestProject.SplitRegular

/-!
# Gaussian moment estimates for the split maps

Second-moment computations for the Gaussian increments, used to compare the random split maps
`Ψ_n` with their deterministic counterpart (all increments set to zero).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

lemma euclNorm_sq_two (u : Pt 2) : euclNorm u ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  unfold euclNorm
  rw [Real.sq_sqrt (by positivity), Fin.sum_univ_two]

lemma lintegral_sq_gaussianReal (c : ℝ) (v : ℝ≥0) :
    ∫⁻ t, ENNReal.ofReal ((c + t) ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal (c ^ 2 + v) := by
  have hm : MemLp id 2 (gaussianReal 0 v) := by exact_mod_cast memLp_id_gaussianReal (μ := 0) (v := v) 2
  have hsq : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 v) := hm.integrable_sq
  have h1 : Integrable (fun t : ℝ => t) (gaussianReal 0 v) := hm.integrable (by norm_num)
  have hint : Integrable (fun t : ℝ => (c + t) ^ 2) (gaussianReal 0 v) := by
    have : (fun t : ℝ => (c + t) ^ 2) = fun t => c ^ 2 + (2 * c * t + t ^ 2) := by
      funext t; ring
    rw [this]
    exact (integrable_const _).add ((h1.const_mul _).add hsq)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => sq_nonneg _)]
  congr 1
  have hvar := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at hvar
  simp only [id, integral_id_gaussianReal, sub_zero] at hvar
  have : (fun t : ℝ => (c + t) ^ 2) = fun t => c ^ 2 + (2 * c * t + t ^ 2) := by
    funext t; ring
  rw [this, integral_add (f := fun _ => c ^ 2) (g := fun t => 2 * c * t + t ^ 2)
    (integrable_const _) ((h1.const_mul _).add hsq),
    integral_add (f := fun t => 2 * c * t) (g := fun t => t ^ 2) (h1.const_mul _) hsq,
    integral_const_mul, integral_id_gaussianReal, hvar]
  simp

lemma lintegral_euclNorm_sq_gauss2 (c : Pt 2) (v : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal (euclNorm (c + z) ^ 2) ∂(gauss2 v) =
      ENNReal.ofReal (euclNorm c ^ 2 + 2 * v) := by
  have hsplit : ∀ z : Pt 2, ENNReal.ofReal (euclNorm (c + z) ^ 2) =
      ENNReal.ofReal ((c 0 + z 0) ^ 2) + ENNReal.ofReal ((c 1 + z 1) ^ 2) := fun z => by
    rw [euclNorm_sq_two, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    simp
  simp_rw [hsplit]
  have hmi : ∀ i : Fin 2, Measurable fun t : ℝ => ENNReal.ofReal ((c i + t) ^ 2) := fun i =>
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_add_left (f := fun z : Pt 2 => ENNReal.ofReal ((c 0 + z 0) ^ 2))
    ((hmi 0).comp (measurable_pi_apply 0))]
  have he : ∀ i : Fin 2, ∫⁻ z, ENNReal.ofReal ((c i + z i) ^ 2) ∂(gauss2 v) =
      ENNReal.ofReal (c i ^ 2 + v) := fun i => by
    have := (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 v) i).lintegral_comp (hmi i)
    simp only [Function.eval] at this
    unfold gauss2
    rw [this, lintegral_sq_gaussianReal]
  rw [he 0, he 1, ← ENNReal.ofReal_add (by positivity) (by positivity), euclNorm_sq_two]
  congr 1; ring

/-- Adding an independent Gaussian increment raises the mean square by `2v`. -/
lemma lintegral_euclNorm_sq_add_coord (v : ℝ≥0) (k : ℕ) {D : (ℕ → Pt 2) → Pt 2}
    (hDm : Measurable D) (hD : ∀ ζ z, D (Function.update ζ k z) = D ζ) :
    ∫⁻ ζ, ENNReal.ofReal (euclNorm (D ζ + ζ k) ^ 2) ∂(gaussSeq v) =
      ∫⁻ ζ, ENNReal.ofReal (euclNorm (D ζ) ^ 2) ∂(gaussSeq v) + ENNReal.ofReal (2 * v) := by
  have hcont : Continuous (euclNorm : Pt 2 → ℝ) := by unfold euclNorm; fun_prop
  have hF : Measurable fun ζ : ℕ → Pt 2 => ENNReal.ofReal (euclNorm (D ζ + ζ k) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hcont.measurable.comp (hDm.add (measurable_pi_apply k))).pow_const 2)
  have hmeas : Measurable (fun p : (ℕ → Pt 2) × Pt 2 => Function.update p.1 k p.2) := by
    fun_prop
  conv_lhs => rw [← map_update_gaussSeq v k]
  rw [lintegral_map hF hmeas, lintegral_prod (f := fun p : (ℕ → Pt 2) × Pt 2 =>
    ENNReal.ofReal (euclNorm (D (Function.update p.1 k p.2) + Function.update p.1 k p.2 k) ^ 2))
    (hF.comp hmeas).aemeasurable]
  simp only [Function.update_self, hD]
  simp_rw [lintegral_euclNorm_sq_gauss2]
  have hG : Measurable fun ζ : ℕ → Pt 2 => ENNReal.ofReal (euclNorm (D ζ) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hcont.measurable.comp hDm).pow_const 2)
  simp_rw [ENNReal.ofReal_add (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * v)]
  rw [lintegral_add_right _ measurable_const]
  simp

/-- Cauchy–Schwarz for a probability measure. -/
lemma lintegral_ofReal_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ o, 0 ≤ f o) {B : ℝ}
    (hB : ∫⁻ o, ENNReal.ofReal (f o ^ 2) ∂P ≤ ENNReal.ofReal B) :
    ∫⁻ o, ENNReal.ofReal (f o) ∂P ≤ ENNReal.ofReal (Real.sqrt B) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (f := fun o => ENNReal.ofReal (f o)) (g := fun _ => 1)
    (ENNReal.measurable_ofReal.comp hf).aemeasurable aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  refine h.trans ?_
  have e : ∀ o, ENNReal.ofReal (f o) ^ (2 : ℝ) = ENNReal.ofReal (f o ^ 2) := fun o => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.ofReal_pow (hf0 o)]
  simp_rw [e]
  rcases le_or_gt B 0 with hB0 | hB0
  · rw [ENNReal.ofReal_of_nonpos hB0] at hB
    rw [nonpos_iff_eq_zero.1 hB]
    simp
  · calc (∫⁻ o, ENNReal.ofReal (f o ^ 2) ∂P) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal B ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hB (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt B) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB0.le (by norm_num), Real.sqrt_eq_rpow]

section Tail

/-- The tail compositions `T_m = f_{n-m+1} ∘ ⋯ ∘ f_n`, `f_i(y) = ψ_i(y + ζ_i)`. -/
def tailMap (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (n : ℕ) : ℕ → Pt 2 → Pt 2
  | 0 => id
  | m + 1 => (fun y => ψ (n - m) (y + ζ (n - m))) ∘ tailMap ψ ζ n m

lemma tailMap_succ (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (n m : ℕ) (x : Pt 2) :
    tailMap ψ ζ n (m + 1) x = ψ (n - m) (tailMap ψ ζ n m x + ζ (n - m)) := rfl

lemma splitMap_comp_tailMap (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (n : ℕ) :
    ∀ j ≤ n, splitMap ψ ζ j ∘ tailMap ψ ζ n (n - j) = tailMap ψ ζ n n := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [← ih (by omega)]
    have e : n - j = (n - (j + 1)) + 1 := by omega
    rw [e]
    funext x
    simp only [Function.comp_apply, tailMap_succ, splitMap_succ]
    rw [show n - (n - (j + 1)) = j + 1 by omega]

lemma splitMap_eq_tailMap (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (n : ℕ) :
    splitMap ψ ζ n = tailMap ψ ζ n n := by
  have := splitMap_comp_tailMap ψ ζ n n le_rfl
  rwa [Nat.sub_self] at this

lemma tailMap_update (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (n : ℕ) {m k : ℕ} (hm : m ≤ n)
    (hk : k ≤ n - m) (z : Pt 2) : tailMap ψ (Function.update ζ k z) n m = tailMap ψ ζ n m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext x
    rw [tailMap_succ, tailMap_succ, ih (by omega) (by omega), Function.update_of_ne (by omega)]

lemma continuous_tailMap {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, Continuous (ψ i)) (n m : ℕ)
    (x : Pt 2) : Continuous fun ζ : ℕ → Pt 2 => tailMap ψ ζ n m x := by
  induction m with
  | zero => exact continuous_const
  | succ m ih =>
    simp only [tailMap_succ]
    exact (hψ _).comp (ih.add (continuous_apply _))

lemma tailMap_C1 {ψ : ℕ → Pt 2 → Pt 2} {p : ℝ} (hp : 1 ≤ p)
    (hd : ∀ i, Differentiable ℝ (ψ i)) (hD : ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ p)
    (ζ : ℕ → Pt 2) (n m : ℕ) :
    Differentiable ℝ (tailMap ψ ζ n m) ∧ ∀ x, ‖fderiv ℝ (tailMap ψ ζ n m) x‖ ≤ p ^ m := by
  induction m with
  | zero =>
    refine ⟨differentiable_id, fun x => ?_⟩
    simp only [tailMap, pow_zero]
    rw [fderiv_id]; exact ContinuousLinearMap.norm_id_le
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have hf : Differentiable ℝ (fun y => ψ (n - m) (y + ζ (n - m))) :=
      (hd _).comp (differentiable_id.add_const _)
    refine ⟨hf.comp h1, fun x => ?_⟩
    simp only [tailMap]
    rw [fderiv_comp x (hf _) (h1 x), fderiv_shift]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [pow_succ, mul_comm (p ^ m)]
    exact mul_le_mul (hD _ _) (h2 x) (norm_nonneg _) (by positivity)

end Tail

section Stoch

variable {ψ : ℕ → Pt 2 → Pt 2} {ρ p β : ℝ} (n : ℕ) (v : ℝ≥0)

/-- The displacement of the random tail composition from the deterministic one. -/
def tailDsp (ψ : ℕ → Pt 2 → Pt 2) (n m : ℕ) (x : Pt 2) (ζ : ℕ → Pt 2) : Pt 2 :=
  tailMap ψ ζ n m x - tailMap ψ 0 n m x

lemma continuous_tailDsp (hψ : ∀ i, Continuous (ψ i)) (m : ℕ) (x : Pt 2) :
    Continuous (tailDsp ψ n m x) :=
  (continuous_tailMap hψ n m x).sub continuous_const

lemma tailDsp_update {m k : ℕ} (hm : m ≤ n) (hk : k ≤ n - m) (x : Pt 2) (ζ : ℕ → Pt 2)
    (z : Pt 2) : tailDsp ψ n m x (Function.update ζ k z) = tailDsp ψ n m x ζ := by
  simp only [tailDsp, tailMap_update ψ ζ n hm hk z]

lemma lintegral_tailDsp_add (hψ : ∀ i, Continuous (ψ i)) {m : ℕ} (hm : m ≤ n) (x : Pt 2) :
    ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) ^ 2) ∂(gaussSeq v) =
      ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailDsp ψ n m x ζ) ^ 2) ∂(gaussSeq v) +
        ENNReal.ofReal (2 * v) :=
  lintegral_euclNorm_sq_add_coord v (n - m) (continuous_tailDsp n hψ m x).measurable
    fun ζ z => tailDsp_update n hm le_rfl x ζ z

lemma tailDsp_succ (m : ℕ) (x : Pt 2) (ζ : ℕ → Pt 2) :
    tailDsp ψ n (m + 1) x ζ = ψ (n - m) (tailMap ψ 0 n m x + (tailDsp ψ n m x ζ + ζ (n - m))) -
      ψ (n - m) (tailMap ψ 0 n m x) := by
  simp only [tailDsp, tailMap_succ, Pi.zero_apply, add_zero]
  congr 2; abel

/-- Mean-square growth of the displacement. -/
theorem lintegral_tailDsp_sq (hψ : ∀ i, Continuous (ψ i)) (hρ : 1 ≤ ρ)
    (hE : ∀ i y u, euclNorm (ψ i (y + u) - ψ i y) ≤ ρ * euclNorm u) (x : Pt 2) :
    ∀ m ≤ n, ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailDsp ψ n m x ζ) ^ 2) ∂(gaussSeq v) ≤
      ENNReal.ofReal (m * ρ ^ (2 * m) * (2 * v)) := by
  intro m
  induction m with
  | zero => intro _; simp [tailDsp, tailMap, euclNorm]
  | succ m ih =>
    intro hm
    have hρ0 : 0 ≤ ρ := by linarith
    have hpt : ∀ ζ, ENNReal.ofReal (euclNorm (tailDsp ψ n (m + 1) x ζ) ^ 2) ≤
        ENNReal.ofReal (ρ ^ 2) *
          ENNReal.ofReal (euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) ^ 2) := fun ζ => by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [tailDsp_succ]
      have h := hE (n - m) (tailMap ψ 0 n m x) (tailDsp ψ n m x ζ + ζ (n - m))
      have h0 := euclNorm_nonneg (ψ (n - m) (tailMap ψ 0 n m x + (tailDsp ψ n m x ζ +
        ζ (n - m))) - ψ (n - m) (tailMap ψ 0 n m x))
      calc _ ≤ (ρ * euclNorm (tailDsp ψ n m x ζ + ζ (n - m))) ^ 2 :=
            pow_le_pow_left₀ h0 h 2
        _ = _ := by ring
    calc _ ≤ ∫⁻ ζ, ENNReal.ofReal (ρ ^ 2) *
          ENNReal.ofReal (euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) ^ 2) ∂(gaussSeq v) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (ρ ^ 2) * (∫⁻ ζ, ENNReal.ofReal (euclNorm (tailDsp ψ n m x ζ) ^ 2)
            ∂(gaussSeq v) + ENNReal.ofReal (2 * v)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_tailDsp_add n v hψ (by omega) x]
      _ ≤ ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal (m * ρ ^ (2 * m) * (2 * v)) +
            ENNReal.ofReal (2 * v)) := by
          gcongr; exact ih (by omega)
      _ = ENNReal.ofReal (ρ ^ 2 * (m * ρ ^ (2 * m) * (2 * v) + 2 * v)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 1 ≤ ρ ^ (2 * (m + 1)) := one_le_pow₀ hρ
          have e : ρ ^ (2 * (m + 1)) = ρ ^ 2 * ρ ^ (2 * m) := by ring
          have hv : (0 : ℝ) ≤ v := v.2
          push_cast
          rw [e]
          have h2 : 1 ≤ ρ ^ (2 * m) := one_le_pow₀ hρ
          nlinarith [mul_nonneg (mul_nonneg hv (sq_nonneg ρ)) (sub_nonneg.2 h2)]

/-- Pathwise derivative comparison. -/
theorem norm_fderiv_tailMap_sub_le (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hd : ∀ i, Differentiable ℝ (ψ i)) (hD : ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ p)
    (hD2 : ∀ i y z, ‖fderiv ℝ (ψ i) y - fderiv ℝ (ψ i) z‖ ≤ β * ‖y - z‖)
    (x : Pt 2) (ζ : ℕ → Pt 2) (m : ℕ) :
    ‖fderiv ℝ (tailMap ψ ζ n m) x - fderiv ℝ (tailMap ψ 0 n m) x‖ ≤
      p ^ m * β * ∑ j ∈ Finset.range m, euclNorm (tailDsp ψ n j x ζ + ζ (n - j)) := by
  induction m with
  | zero => simp [tailMap]
  | succ m ih =>
    obtain ⟨h1, -⟩ := tailMap_C1 hp hd hD ζ n m
    obtain ⟨h1', h2'⟩ := tailMap_C1 hp hd hD 0 n m
    have hf : ∀ c : Pt 2, Differentiable ℝ (fun y => ψ (n - m) (y + c)) := fun c =>
      (hd _).comp (differentiable_id.add_const _)
    have eζ : fderiv ℝ (tailMap ψ ζ n (m + 1)) x =
        (fderiv ℝ (ψ (n - m)) (tailMap ψ ζ n m x + ζ (n - m))).comp
          (fderiv ℝ (tailMap ψ ζ n m) x) := by
      simp only [tailMap]
      rw [fderiv_comp x (hf _ _) (h1 x), fderiv_shift]
    have e0 : fderiv ℝ (tailMap ψ 0 n (m + 1)) x =
        (fderiv ℝ (ψ (n - m)) (tailMap ψ 0 n m x)).comp (fderiv ℝ (tailMap ψ 0 n m) x) := by
      simp only [tailMap]
      rw [fderiv_comp x (hf _ _) (h1' x), fderiv_shift]
      simp
    rw [eζ, e0]
    set A := fderiv ℝ (ψ (n - m)) (tailMap ψ ζ n m x + ζ (n - m))
    set B := fderiv ℝ (ψ (n - m)) (tailMap ψ 0 n m x)
    set G := fderiv ℝ (tailMap ψ ζ n m) x
    set g := fderiv ℝ (tailMap ψ 0 n m) x
    have e : A.comp G - B.comp g = A.comp (G - g) + (A - B).comp g := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
    rw [e]
    have hAB : ‖A - B‖ ≤ β * euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) := by
      refine (hD2 _ _ _).trans ?_
      gcongr
      refine le_of_eq_of_le ?_ (norm_le_euclNorm _)
      congr 1; simp only [tailDsp]; abel
    have hA : ‖A‖ ≤ p := hD _ _
    have hg : ‖g‖ ≤ p ^ m := h2' x
    have hS0 : 0 ≤ ∑ j ∈ Finset.range m, euclNorm (tailDsp ψ n j x ζ + ζ (n - j)) :=
      Finset.sum_nonneg fun j _ => euclNorm_nonneg _
    have hu0 := euclNorm_nonneg (tailDsp ψ n m x ζ + ζ (n - m))
    have hpm : p ^ m ≤ p ^ (m + 1) := pow_le_pow_right₀ hp (by omega)
    have hp0 : 0 ≤ p := by linarith
    calc ‖A.comp (G - g) + (A - B).comp g‖ ≤ ‖A‖ * ‖G - g‖ + ‖A - B‖ * ‖g‖ :=
          (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _))
      _ ≤ p * (p ^ m * β * ∑ j ∈ Finset.range m, euclNorm (tailDsp ψ n j x ζ + ζ (n - j))) +
          β * euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) * p ^ m := by
          gcongr
      _ ≤ p ^ (m + 1) * β * ∑ j ∈ Finset.range (m + 1),
            euclNorm (tailDsp ψ n j x ζ + ζ (n - j)) := by
          rw [Finset.sum_range_succ, pow_succ]
          have : β * euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) * p ^ m ≤
              p ^ m * p * β * euclNorm (tailDsp ψ n m x ζ + ζ (n - m)) := by
            have : p ^ m ≤ p ^ m * p := by nlinarith [pow_nonneg hp0 m]
            nlinarith [mul_nonneg hβ hu0]
          nlinarith

/-- **Mean derivative comparison**: the expected deviation of `DΨ_n(x)` from the derivative of
the deterministic composition (all increments zero). -/
theorem lintegral_fderiv_splitMap_sub_le (hp : 1 ≤ p) (hβ : 0 ≤ β) (hρ : 1 ≤ ρ)
    (hd : ∀ i, Differentiable ℝ (ψ i))
    (hE : ∀ i y u, euclNorm (ψ i (y + u) - ψ i y) ≤ ρ * euclNorm u)
    (hD : ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ p)
    (hD2 : ∀ i y z, ‖fderiv ℝ (ψ i) y - fderiv ℝ (ψ i) z‖ ≤ β * ‖y - z‖) (x : Pt 2) :
    ∫⁻ ζ, ‖fderiv ℝ (splitMap ψ ζ n) x - fderiv ℝ (splitMap ψ 0 n) x‖ₑ ∂(gaussSeq v) ≤
      ENNReal.ofReal (p ^ n * β * n * Real.sqrt (n * ρ ^ (2 * n) * (2 * v))) := by
  have hψ : ∀ i, Continuous (ψ i) := fun i => (hd i).continuous
  have hv : (0 : ℝ) ≤ v := v.2
  have hρ0 : 0 ≤ ρ := by linarith
  have hcE : Continuous (euclNorm : Pt 2 → ℝ) := by unfold euclNorm; fun_prop
  set B : ℝ := n * ρ ^ (2 * n) * (2 * v) with hB
  have hu : ∀ j ∈ Finset.range n, ∫⁻ ζ, ENNReal.ofReal (euclNorm (tailDsp ψ n j x ζ +
      ζ (n - j))) ∂(gaussSeq v) ≤ ENNReal.ofReal (Real.sqrt B) := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine lintegral_ofReal_le_sqrt _ (hcE.comp ((continuous_tailDsp n hψ j x).add
      (continuous_apply _))).measurable (fun _ => euclNorm_nonneg _) ?_
    simp only [Function.comp_apply, Pi.add_apply]
    rw [lintegral_tailDsp_add n v hψ hj.le x]
    refine (add_le_add (lintegral_tailDsp_sq n v hψ hρ hE x j hj.le) le_rfl).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ρ ^ (2 * j) ≤ ρ ^ (2 * n) := pow_le_pow_right₀ hρ (by omega)
    have h2 : 1 ≤ ρ ^ (2 * n) := one_le_pow₀ hρ
    have h3 : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    rw [hB]
    nlinarith [mul_nonneg (Nat.cast_nonneg j) (sub_nonneg.2 h1), mul_nonneg hv
      (sub_nonneg.2 h2), pow_nonneg hρ0 (2 * j), mul_nonneg (mul_nonneg hv
      (Nat.cast_nonneg j)) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h3)
      (mul_nonneg hv (pow_nonneg hρ0 (2 * n)))]
  simp only [splitMap_eq_tailMap]
  have hp0 : 0 ≤ p ^ n * β := mul_nonneg (pow_nonneg (by linarith) n) hβ
  calc ∫⁻ ζ, ‖fderiv ℝ (tailMap ψ ζ n n) x - fderiv ℝ (tailMap ψ 0 n n) x‖ₑ ∂(gaussSeq v)
      ≤ ∫⁻ ζ, ENNReal.ofReal (p ^ n * β) * ∑ j ∈ Finset.range n,
          ENNReal.ofReal (euclNorm (tailDsp ψ n j x ζ + ζ (n - j))) ∂(gaussSeq v) := by
        refine lintegral_mono fun ζ => ?_
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_sum_of_nonneg
          (fun j _ => euclNorm_nonneg _), ← ENNReal.ofReal_mul hp0]
        exact ENNReal.ofReal_le_ofReal (norm_fderiv_tailMap_sub_le n hp hβ hd hD hD2 x ζ n)
    _ = ENNReal.ofReal (p ^ n * β) * ∑ j ∈ Finset.range n, ∫⁻ ζ,
          ENNReal.ofReal (euclNorm (tailDsp ψ n j x ζ + ζ (n - j))) ∂(gaussSeq v) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finset_sum]
        intro j _
        exact ENNReal.measurable_ofReal.comp (hcE.comp ((continuous_tailDsp n hψ j x).add
          (continuous_apply _))).measurable
    _ ≤ ENNReal.ofReal (p ^ n * β) * ∑ j ∈ Finset.range n, ENNReal.ofReal (Real.sqrt B) := by
        gcongr with j hj
        exact hu j hj
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hp0]
        ring_nf

end Stoch

end AnomDiss
