module

public import RequestProject.SplitNegMoment
public import RequestProject.SplitMeasurable
public import RequestProject.SplitClose

/-!
# The weighted Fourier bound for the split maps

The per-`n` estimate in the proof of Proposition 3.11: Lemma 3.5 applied to the random maps
`Ψ_n` (canonical Lie splitting of `B_{μ,ω}` with Gaussian increments), with the negative moment
hypothesis inherited from Lemma 2.7 through Lemma 3.9.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal Matrix

noncomputable section

namespace AnomDiss

section SplitDefs

variable {L M : ℕ} {S : ℕ → ℝ}

/-- The averaged weighted Fourier sum `𝔼_ζ ∑ₘ W_{qk}(ℓ + km)|c_m^{Ψ_n}(ℓ/k)|²` of the canonical
split maps with `n` steps, for the parameter `ω`. -/
def splitFourierSum (cf : ControlFamily L M S) (σ R : ℝ) (q k : ℕ) (ℓ : Fin 2 → ℤ) (μ : ℝ)
    (n : ℕ) (w : BlockParam L) : ℝ≥0∞ :=
  ∫⁻ ζ, ∑' m, ENNReal.ofReal (weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec m)) *
    ‖coeffC (splitMap (canonPsi cf μ w n) ζ n) ((k : ℝ)⁻¹ • intVec ℓ) m‖ₑ ^ 2
    ∂(gaussSeq (splitVar μ n))

lemma norm_dampedCoef_le_all (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (s : ℝ) : ‖dampedCoef cf μ w s‖ ≤ 2 * coefBound cf := by
  have hC := coefBound_nonneg cf
  set f : ℝ → Fin 4 → ℝ := fun r => Real.exp (-μ * (s - r)) • cf.coef w.1 r with hf
  have hfc : Continuous f := by
    have := (cf.contDiff_coef w.1).continuous
    simp only [hf]; fun_prop
  have hzero : ∀ r, r ∉ Icc cf.a₀ cf.b₀ → f r = 0 := fun r hr => by
    simp [hf, cf.support w.1 r hr]
  rcases lt_or_ge s 0 with hs | hs
  · have hint : ∫ r in (0 : ℝ)..s, f r = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : Fin 4 → ℝ)) fun r hr => ?_]
      · simp
      · rw [uIcc_of_ge hs.le] at hr
        exact hzero r fun h => by linarith [h.1, hr.2, cf.ha₀]
    unfold dampedCoef
    rw [show (∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r) = 0 from hint]
    simp only [smul_zero, sub_zero]
    linarith [norm_coef_le cf w.1 s]
  rcases le_or_gt s 1 with hs1 | hs1
  · exact norm_dampedCoef_le cf hμ w ⟨hs, hs1⟩
  · have hsplit : ∫ r in (0 : ℝ)..s, f r = ∫ r in (0 : ℝ)..1, f r := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
        (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
      rw [intervalIntegral.integral_congr (a := 1) (b := s) (g := fun _ => (0 : Fin 4 → ℝ))
        fun r hr => ?_]
      · simp
      · rw [uIcc_of_le hs1.le] at hr
        exact hzero r fun h => by linarith [h.2, hr.1, cf.hb₀]
    have hint : ‖∫ r in (0 : ℝ)..1, f r‖ ≤ coefBound cf * |1 - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
      rw [uIoc_of_le zero_le_one] at hr
      simp only [hf]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-μ * (s - r)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [hμ.1, hr.2])
      calc Real.exp (-μ * (s - r)) * ‖cf.coef w.1 r‖ ≤ 1 * coefBound cf := by
            gcongr
            exact norm_coef_le cf w.1 r
        _ = coefBound cf := one_mul _
    unfold dampedCoef
    rw [show (∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • cf.coef w.1 r) =
      ∫ r in (0 : ℝ)..1, f r from hsplit]
    calc ‖cf.coef w.1 s - μ • ∫ r in (0 : ℝ)..1, f r‖
        ≤ ‖cf.coef w.1 s‖ + |μ| * ‖∫ r in (0 : ℝ)..1, f r‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ coefBound cf + 1 * (coefBound cf * 1) := by
          gcongr
          · exact norm_coef_le cf w.1 s
          · rw [abs_of_nonneg hμ.1]; exact hμ.2
          · simpa using hint
      _ = 2 * coefBound cf := by ring

/-- `B_{μ,ω}` itself is a bounded, Lipschitz, time-continuous field on all of `ℝ`. -/
theorem dampedB_good (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) : GoodField (dampedB cf μ w) (splitM cf) (splitK cf) where
  cont x := by
    have hc : Continuous (dampedCoef cf μ w) :=
      continuous_iff_continuousAt.2 fun s => (hasDerivAt_dampedCoef cf μ w s).continuousAt
    simp_rw [dampedB_eq, ← eFieldCLM_apply]
    exact (eFieldCLM (x - w.2)).continuous.comp hc
  bound s x := by
    rw [dampedB_eq]
    refine (norm_eField_le _ _).trans ?_
    have := norm_dampedCoef_le_all cf hμ w s
    change 2 * ‖dampedCoef cf μ w s‖ ≤ 4 * coefBound cf
    linarith
  lip s := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, dampedB_eq]
    refine (norm_eField_sub_le _ _ _).trans ?_
    have := norm_dampedCoef_le_all cf hμ w s
    have e : x - w.2 - (y - w.2) = x - y := by abel
    rw [e]
    simp only [splitK, NNReal.coe_mk]
    calc 4 * π * ‖dampedCoef cf μ w s‖ * ‖x - y‖
        ≤ 4 * π * (2 * coefBound cf) * ‖x - y‖ := by gcongr
      _ = 8 * π * coefBound cf * ‖x - y‖ := by ring

/-- On `[0,1]` the flows of `B_{μ,ω}` and of the clamped splitting field agree. -/
lemma gflow_dampedB_eq (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (x : Pt 2) : gflow (dampedB cf μ w) t₀ t x = gflow (splitField cf μ w) t₀ t x := by
  have hD := dampedB_good cf hμ w
  have hS := splitField_good cf hμ w
  refine hS.eqOn_Icc (α := fun s => gflow (dampedB cf μ w) t₀ s x)
    (β := fun s => gflow (splitField cf μ w) t₀ s x) ht₀ (fun s hs => ?_) (fun s hs => ?_)
    (by simp only [hD.gflow_self, hS.gflow_self]) ht
  · have := (hD.hasDerivAt_gflow t₀ s x).hasDerivWithinAt (s := Icc 0 1)
    rwa [← splitField_eq_of_mem cf μ w hs] at this
  · exact (hS.hasDerivAt_gflow t₀ s x).hasDerivWithinAt

/-- The canonical maps `ψ_i` form a splitting of `B_{μ,ω}` with `n` steps. -/
theorem canonPsi_isSplitting (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (n : ℕ) (hn : 1 ≤ n) :
    IsSplitting (dampedB cf μ w) n (canonPsi cf μ w n) := by
  intro i hi1 hin
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hin' : (i : ℝ) ≤ n := by exact_mod_cast hin
  have ht₀ : ((i - 1 : ℝ)) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).2 (by linarith)⟩
  have ht₁ : (i : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).2 hin'⟩
  have hD := dampedB_good cf hμ w
  have hS := splitField_good cf hμ w
  refine ⟨fun s x => gflow (dampedB cf μ w) ((i - 1 : ℝ) / n) s x, fun x => hD.gflow_self _ x,
    fun s x => hD.hasDerivAt_gflow _ s x, fun x => ?_⟩
  simp only
  rw [gflow_dampedB_eq cf hμ w ht₀ ht₁, gflow_dampedB_eq cf hμ w ht₀ ht₁]
  exact ⟨hS.gflow_inv _ _ x, hS.gflow_inv _ _ x⟩


/-- Regularity of the canonical split maps (the `C²` part of Lemma 3.8): `Ψ_n` is a `C²` lift of
a torus map with a `C¹` left inverse, and `DΨ_n`, `D²Ψ_n`, `DΨ_n⁻¹` are bounded uniformly in
`μ ∈ [0,1]`, `ω`, `n ≥ 1` and the Gaussian increments. -/
theorem canonSplit_regular (cf : ControlFamily L M S) :
    ∃ C : ℝ, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ (w : BlockParam L) (n : ℕ), 1 ≤ n → ∀ ζ : ℕ → Pt 2,
      ContDiff ℝ 2 (splitMap (canonPsi cf μ w n) ζ n) ∧
      IsLift (splitMap (canonPsi cf μ w n) ζ n) ∧
      ∃ Ψinv : Pt 2 → Pt 2, ContDiff ℝ 1 Ψinv ∧
        Function.LeftInverse Ψinv (splitMap (canonPsi cf μ w n) ζ n) ∧
        ∀ x, ‖fderiv ℝ (splitMap (canonPsi cf μ w n) ζ n) x‖ ≤ C ∧
          ‖iteratedFDeriv ℝ 2 (splitMap (canonPsi cf μ w n) ζ n) x‖ ≤ C ∧
          ‖fderiv ℝ Ψinv x‖ ≤ C :=
  canonSplit_regular_aux cf

end SplitDefs

/-- A `C^k` (`k ≥ 1`) bijection of `ℝ²` with nonvanishing Jacobian determinant has a `C^k`
inverse. -/
theorem contDiff_inverse_of_det {k : WithTop ℕ∞} (hk : k ≠ 0) {Φ Φi : Pt 2 → Pt 2}
    (hΦ : ContDiff ℝ k Φ) (hl : Function.LeftInverse Φi Φ) (hr : Function.RightInverse Φi Φ)
    (hdet : ∀ y, (jac Φ y).det ≠ 0) : ContDiff ℝ k Φi := by
  have hmat : ∀ y, jac Φ y = LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2))
      (fderiv ℝ Φ y : Pt 2 →ₗ[ℝ] Pt 2) := by
    intro y
    rw [LinearMap.toMatrix_eq_toMatrix']
    ext i j
    simp [jac, LinearMap.toMatrix'_apply]
  have hunit : ∀ y, IsUnit (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2))
      (fderiv ℝ Φ y : Pt 2 →ₗ[ℝ] Pt 2)).det := fun y => by
    rw [← hmat]; exact (hdet y).isUnit
  let f' : Pt 2 → Pt 2 ≃L[ℝ] Pt 2 := fun y => (LinearEquiv.ofIsUnitDet (hunit y)).toContinuousLinearEquiv
  have hf' : ∀ y, (f' y : Pt 2 →L[ℝ] Pt 2) = fderiv ℝ Φ y := fun y => by
    ext v i
    simp only [f', ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv']
    rw [← LinearEquiv.coe_coe, LinearEquiv.coe_ofIsUnitDet]
    rfl
  have hopen : IsOpenMap Φ := isOpenMap_of_hasStrictFDerivAt_equiv (f' := f') fun y => by
    rw [hf']; exact hΦ.hasStrictFDerivAt hk
  let e : Pt 2 ≃ₜ Pt 2 :=
    { toFun := Φ, invFun := Φi, left_inv := hl, right_inv := hr,
      continuous_toFun := hΦ.continuous,
      continuous_invFun := by
        rw [continuous_def]; intro U hU
        rw [← Set.image_eq_preimage_of_inverse hl hr]; exact hopen U hU }
  exact e.contDiff_symm (f₀' := f') (fun y => by
    rw [hf']; exact (hΦ.differentiable hk y).hasFDerivAt) hΦ

/-- The negative moment bound for the split maps (the estimate `(split-negative-moment)` in the
proof of Proposition 3.11). -/
theorem split_negative_moment (q : ℕ) (hq : 3 ≤ q) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (L : ℕ)
    (hneg : NegMomentBound q σ L) {M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) :
    ∃ μstar : ℝ, 0 < μstar ∧ μstar ≤ 1 ∧ ∀ μ ∈ Icc 0 μstar, ∀ n : ℕ, 1 ≤ n →
      ∀ e : Pt 2, euclNorm e = 1 →
        ∫ o, (∫ y in cell 2, euclNorm ((jac (splitMap (canonPsi cf μ o.1 n) o.2 n) y)ᵀ *ᵥ e) ^ (-σ))
          ∂((blockMeasure L).prod (gaussSeq (splitVar μ n))) ≤ 1 / (32 * (q : ℝ) ^ σ) := by
  obtain ⟨C1, hreg⟩ := canonSplit_regular cf
  obtain ⟨Cc, hCc⟩ := split_deriv_closeness cf
  set K1 : ℝ := max C1 0 + 1 with hK1
  have hK1pos : 0 < K1 := by positivity
  set c : ℝ := 1 / (2 * K1) with hc
  have hcpos : 0 < c := by positivity
  set Lc : ℝ := (σ + 1) * c ^ (-σ - 1) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  set Kc : ℝ := 2 * Lc * max Cc 0 + 1 with hKc
  have hKcpos : 0 < Kc := by positivity
  have hqσ : 0 < (q : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q)) σ
  set ε : ℝ := 3 / (128 * (q : ℝ) ^ σ) with hε
  have hεpos : 0 < ε := by positivity
  refine ⟨min 1 ((ε / Kc) ^ 2), by positivity, min_le_left _ _, fun μ hμ n hn e he => ?_⟩
  have hμ' : μ ∈ Icc (0 : ℝ) 1 := ⟨hμ.1, hμ.2.trans (min_le_left _ _)⟩
  set Ψ : BlockParam L × (ℕ → Pt 2) → Pt 2 → Pt 2 :=
    fun o => splitMap (canonPsi cf μ o.1 n) o.2 n with hΨdef
  set P := (blockMeasure L).prod (gaussSeq (splitVar μ n)) with hPdef
  have hΨsm : ∀ o, ContDiff ℝ 2 (Ψ o) := fun o => (hreg μ hμ' o.1 n hn o.2).1
  have hlow : ∀ o y, c ≤ euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) := by
    intro o y
    obtain ⟨-, -, Ψi, hΨi, hl, hb⟩ := hreg μ hμ' o.1 n hn o.2
    have h := jac_transpose_lower (Ψ o) Ψi ((hΨsm o).differentiable (by simp))
      (hΨi.differentiable (by simp)) hl K1 (fun x => by
        have := (hb x).2.2
        have := le_max_left C1 0
        linarith) y e he
    rw [hc, div_le_iff₀ (by positivity)]; linarith
  -- the integrands
  set A : (BlockParam L × (ℕ → Pt 2)) × Pt 2 → ℝ :=
    fun p => euclNorm ((jac (Ψ p.1) p.2)ᵀ *ᵥ e) ^ (-σ) with hAdef
  set Bt : BlockParam L × Pt 2 → ℝ :=
    fun p => euclNorm ((jac (termInv p.1) p.2)ᵀ *ᵥ e) ^ (-σ) with hBtdef
  set G : BlockParam L × (ℕ → Pt 2) → Pt 2 → ℝ≥0∞ :=
    fun o y => ‖fderiv ℝ (Ψ o) y - fderiv ℝ (termInv o.1) y‖ₑ with hGdef
  set D : BlockParam L × (ℕ → Pt 2) → ℝ≥0∞ := fun o => ∫⁻ y in cell 2, G o y with hDdef
  have hA0 : ∀ p, 0 ≤ A p := fun p => Real.rpow_nonneg (euclNorm_nonneg _) _
  have hAle : ∀ p, A p ≤ c ^ (-σ) := fun p =>
    Real.rpow_le_rpow_of_nonpos hcpos (hlow p.1 p.2) (by linarith)
  have hmeasΨ : Measurable (Function.uncurry Ψ) := measurable_canonSplit cf hμ' n
  have hAm : Measurable A := by
    have hij := measurable_jac_param Ψ hmeasΨ (fun o => (hΨsm o).differentiable (by simp))
    have h2 : Measurable fun p : (BlockParam L × (ℕ → Pt 2)) × Pt 2 =>
        euclNorm ((jac (Ψ p.1) p.2)ᵀ *ᵥ e) := by
      unfold euclNorm
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
      have h00 := hij 0 0; have h01 := hij 0 1; have h10 := hij 1 0; have h11 := hij 1 1
      fun_prop
    exact h2.pow_const _
  have hBtm : Measurable fun p : BlockParam L × Pt 2 => ENNReal.ofReal (Bt p) := by
    have hcont := continuous_euclNorm_jac_blockMapInv L e
    have : (fun p : BlockParam L × Pt 2 => ENNReal.ofReal (Bt p)) = fun p =>
        ENNReal.ofReal (euclNorm ((jac (blockMapInv p.1.1) (p.2 - p.1.2))ᵀ *ᵥ e) ^ (-σ)) := by
      funext p; simp only [hBtdef, jac_termInv]
    rw [this]
    exact ENNReal.measurable_ofReal.comp
      ((hcont.comp (by fun_prop : Continuous fun p : BlockParam L × Pt 2 =>
        (p.1.1, p.2 - p.1.2))).measurable.pow_const _)
  -- pointwise comparison
  have hpt : ∀ o y, ENNReal.ofReal (A (o, y)) ≤
      ENNReal.ofReal (Bt (o.1, y)) + ENNReal.ofReal (2 * Lc) * G o y := by
    intro o y
    have h1 := rpow_neg_le_add hcpos (hlow o y) (euclNorm_nonneg ((jac (termInv o.1) y)ᵀ *ᵥ e))
      hσ0
    have h2 := abs_euclNorm_jac_sub_le (Ψ o) (termInv o.1) y e he
    have h3 : A (o, y) ≤ Bt (o.1, y) +
        2 * Lc * ‖fderiv ℝ (Ψ o) y - fderiv ℝ (termInv o.1) y‖ := by
      simp only [hAdef, hBtdef]
      nlinarith [mul_le_mul_of_nonneg_left h2 hLc0]
    calc ENNReal.ofReal (A (o, y))
        ≤ ENNReal.ofReal (Bt (o.1, y) +
            2 * Lc * ‖fderiv ℝ (Ψ o) y - fderiv ℝ (termInv o.1) y‖) := ENNReal.ofReal_le_ofReal h3
      _ ≤ ENNReal.ofReal (Bt (o.1, y)) +
            ENNReal.ofReal (2 * Lc * ‖fderiv ℝ (Ψ o) y - fderiv ℝ (termInv o.1) y‖) :=
          ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (Bt (o.1, y)) + ENNReal.ofReal (2 * Lc) *
            ‖fderiv ℝ (Ψ o) y - fderiv ℝ (termInv o.1) y‖ₑ := by
          rw [ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm]
  have hvol : volume (cell 2) = 1 := volume_cell_two
  -- lintegral bound
  have hlin : ∫⁻ o, (∫⁻ y in cell 2, ENNReal.ofReal (A (o, y))) ∂P ≤
      ENNReal.ofReal (1 / (128 * (q : ℝ) ^ σ)) + ENNReal.ofReal (2 * Lc) *
        ENNReal.ofReal (Cc * Real.sqrt μ) := by
    have hmB : Measurable fun o : BlockParam L × (ℕ → Pt 2) =>
        ∫⁻ y in cell 2, ENNReal.ofReal (Bt (o.1, y)) :=
      (hBtm.comp (by fun_prop : Measurable fun p : (BlockParam L × (ℕ → Pt 2)) × Pt 2 =>
        (p.1.1, p.2))).lintegral_prod_right'
    calc ∫⁻ o, (∫⁻ y in cell 2, ENNReal.ofReal (A (o, y))) ∂P
        ≤ ∫⁻ o, ((∫⁻ y in cell 2, ENNReal.ofReal (Bt (o.1, y))) +
            ENNReal.ofReal (2 * Lc) * D o) ∂P := by
          refine lintegral_mono fun o => ?_
          calc ∫⁻ y in cell 2, ENNReal.ofReal (A (o, y))
              ≤ ∫⁻ y in cell 2, (ENNReal.ofReal (Bt (o.1, y)) +
                  ENNReal.ofReal (2 * Lc) * G o y) := lintegral_mono fun y => hpt o y
            _ = _ := by
                rw [lintegral_add_left (f := fun y => ENNReal.ofReal (Bt (o.1, y))) ((hBtm.comp (by fun_prop :
                  Measurable fun y : Pt 2 => (o.1, y))))]
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ o, (∫⁻ y in cell 2, ENNReal.ofReal (Bt (o.1, y))) ∂P +
            ENNReal.ofReal (2 * Lc) * ∫⁻ o, D o ∂P := by
          rw [lintegral_add_left hmB, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          · rw [hPdef, lintegral_prod _ hmB.aemeasurable]
            simp only [lintegral_const, measure_univ, mul_one]
            have := termInv_neg_moment (q : ℝ) σ hσ0 L hneg e he
            exact this
          · refine (lintegral_prod_le _).trans ?_
            have hGm : ∀ w : BlockParam L, Measurable (Function.uncurry fun (ζ : ℕ → Pt 2)
                (y : Pt 2) => G (w, ζ) y) := fun w => by
              have hψc : ∀ i, Continuous (canonPsi cf μ w n i) := fun i =>
                (splitField_good cf hμ' w).continuous_gflow _ _
              have h1 := measurable_fderiv_with_param ℝ
                (f := fun (ζ : ℕ → Pt 2) (y : Pt 2) => splitMap (canonPsi cf μ w n) ζ n y)
                (continuous_splitMap hψc n)
              have h2 : Measurable fun p : (ℕ → Pt 2) × Pt 2 => fderiv ℝ (termInv w) p.2 :=
                ((contDiff_termInv w).continuous_fderiv (by simp)).measurable.comp measurable_snd
              exact (h1.sub h2).enorm
            calc ∫⁻ w, ∫⁻ ζ, D (w, ζ) ∂(gaussSeq (splitVar μ n)) ∂(blockMeasure L)
                = ∫⁻ w, (∫⁻ y in cell 2, ∫⁻ ζ, G (w, ζ) y ∂(gaussSeq (splitVar μ n)))
                    ∂(blockMeasure L) :=
                  lintegral_congr fun w => lintegral_lintegral_swap (hGm w).aemeasurable
              _ ≤ ∫⁻ w, (∫⁻ y in cell 2, ENNReal.ofReal (Cc * Real.sqrt μ)) ∂(blockMeasure L) :=
                  lintegral_mono fun w => lintegral_mono fun y => hCc μ hμ' w n hn y
              _ = _ := by simp [hvol]
  -- convert to Bochner integrals
  have hAint : ∀ o, IntegrableOn (fun y => A (o, y)) (cell 2) := fun o =>
    Integrable.of_bound (hAm.comp (by fun_prop : Measurable fun y : Pt 2 => (o, y))).aestronglyMeasurable
      (c ^ (-σ)) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA0 _)]; exact hAle _)
  set J : BlockParam L × (ℕ → Pt 2) → ℝ := fun o => ∫ y in cell 2, A (o, y) with hJdef
  have hJ0 : ∀ o, 0 ≤ J o := fun o => setIntegral_nonneg measurableSet_Icc fun y _ => hA0 _
  have hJle : ∀ o, J o ≤ c ^ (-σ) := fun o => by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cell 2) (C := c ^ (-σ))
      (f := fun y => A (o, y)) (by rw [hvol]; simp) (fun y _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA0 _)]; exact hAle _)
    simp only [Measure.real, hvol, ENNReal.toReal_one, mul_one] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have hJm : Measurable J :=
    (hAm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (cell 2))).measurable
  have hJint : Integrable J P := Integrable.of_bound hJm.aestronglyMeasurable (c ^ (-σ))
    (Eventually.of_forall fun o => by rw [Real.norm_eq_abs, abs_of_nonneg (hJ0 o)]; exact hJle o)
  have hconv : ENNReal.ofReal (∫ o, J o ∂P) =
      ∫⁻ o, (∫⁻ y in cell 2, ENNReal.ofReal (A (o, y))) ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hJint (Eventually.of_forall hJ0)]
    refine lintegral_congr fun o => ?_
    exact ofReal_integral_eq_lintegral_ofReal (hAint o) (Eventually.of_forall fun _ => hA0 _)
  have hsq : Real.sqrt μ ≤ ε / Kc := by
    calc Real.sqrt μ ≤ Real.sqrt ((ε / Kc) ^ 2) := Real.sqrt_le_sqrt (hμ.2.trans (min_le_right _ _))
      _ = ε / Kc := Real.sqrt_sq (by positivity)
  have hfinal : 1 / (128 * (q : ℝ) ^ σ) + 2 * Lc * (max Cc 0 * Real.sqrt μ) ≤
      1 / (32 * (q : ℝ) ^ σ) := by
    have h1 : 2 * Lc * (max Cc 0 * Real.sqrt μ) ≤ Kc * Real.sqrt μ := by
      have := Real.sqrt_nonneg μ
      rw [hKc]; nlinarith
    have h2 : Kc * Real.sqrt μ ≤ ε := by
      calc Kc * Real.sqrt μ ≤ Kc * (ε / Kc) := by gcongr
        _ = ε := by field_simp
    have h3 : 1 / (128 * (q : ℝ) ^ σ) + ε = 1 / (32 * (q : ℝ) ^ σ) := by
      rw [hε]; field_simp; ring
    linarith
  have hle : ENNReal.ofReal (∫ o, J o ∂P) ≤
      ENNReal.ofReal (1 / (128 * (q : ℝ) ^ σ) + 2 * Lc * (max Cc 0 * Real.sqrt μ)) := by
    rw [hconv]
    refine hlin.trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := 2 * Lc) (by positivity)]
    exact add_le_add le_rfl (mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))) _)
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
  exact this.trans hfinal

/-- Measurability of the Fourier coefficients of a jointly measurable random map. -/
lemma measurable_coeffC_of_uncurry {Ω : Type*} [MeasurableSpace Ω] {Ψ : Ω → Pt 2 → Pt 2}
    (hΨ : Measurable (Function.uncurry Ψ)) (ξ : Pt 2) (m : Fin 2 → ℤ) :
    Measurable fun o => coeffC (Ψ o) ξ m := by
  unfold coeffC
  have hF : Measurable (Function.uncurry fun (o : Ω) (y : Pt 2) => Complex.exp (2 * π *
      Complex.I * ((dot ξ (Ψ o y - y) - dot (intVec m) y : ℝ) : ℂ))) := by
    refine Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))
    simp only [dot, Pi.sub_apply]
    have hi : ∀ i, Measurable fun p : Ω × Pt 2 => Ψ p.1 p.2 i :=
      fun i => (measurable_pi_apply i).comp hΨ
    have hy : ∀ i, Measurable fun p : Ω × Pt 2 => p.2 i :=
      fun i => (measurable_pi_apply i).comp measurable_snd
    fun_prop
  exact (hF.stronglyMeasurable.integral_prod_right (ν := volume.restrict (cell 2))).measurable

/-- The weighted Fourier bound for the split maps (the per-`n` estimate in the proof of
Proposition 3.11): for `n` large, `𝔼_ω 𝔼_ζ ∑ₘ W_{qk}(ℓ + km)|c_m^{Ψ_n}(ℓ/k)|² ≤ ½ W_k(ℓ)`.
It follows from Lemma 3.5 applied to the random maps `Ψ_n`, whose negative moment hypothesis
is inherited from Lemma 2.5 through the closeness of `Ψ_n` to the terminal flow map
(Lemma 3.9). -/
theorem split_fourier_bound (q : ℕ) (hq : 3 ≤ q) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (L : ℕ)
    (hneg : NegMomentBound q σ L) {M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) :
    ∃ μstar R₀ : ℝ, 0 < μstar ∧ μstar ≤ 1 ∧ 1 ≤ R₀ ∧ ∀ R, R₀ ≤ R → ∀ μ ∈ Icc 0 μstar,
      ∀ k : ℕ, 1 ≤ k → ∀ ℓ : Fin 2 → ℤ, R * k ≤ euclNorm (intVec ℓ) → ∃ N : ℕ, ∀ n, N ≤ n →
        AEMeasurable (splitFourierSum cf σ R q k ℓ μ n) (blockMeasure L) ∧
        ∫⁻ w, splitFourierSum cf σ R q k ℓ μ n w ∂(blockMeasure L) ≤
          ENNReal.ofReal (weightW σ R k (intVec ℓ) / 2) := by
  obtain ⟨Creg, hreg⟩ := canonSplit_regular cf
  obtain ⟨μstar, hμ0, hμ1, hmom⟩ := split_negative_moment q hq σ hσ0 hσ1 L hneg cf
  obtain ⟨R₀, hR₀, hfour⟩ := lemma_fourier_core_C2 q hq σ hσ0 hσ1 (fun _ => Creg)
  refine ⟨μstar, R₀, hμ0, hμ1, hR₀, fun R hR μ hμ k hk ℓ hℓ => ⟨1, fun n hn => ?_⟩⟩
  have hμ' : μ ∈ Icc (0 : ℝ) 1 := ⟨hμ.1, hμ.2.trans hμ1⟩
  set Ψ : BlockParam L × (ℕ → Pt 2) → Pt 2 → Pt 2 :=
    fun o => splitMap (canonPsi cf μ o.1 n) o.2 n with hΨdef
  have hinvex : ∀ o, ∃ Ψi : Pt 2 → Pt 2, ContDiff ℝ 1 Ψi ∧
      Function.LeftInverse Ψi (Ψ o) ∧
      ∀ x, ‖fderiv ℝ (Ψ o) x‖ ≤ Creg ∧ ‖iteratedFDeriv ℝ 2 (Ψ o) x‖ ≤ Creg ∧
        ‖fderiv ℝ Ψi x‖ ≤ Creg := fun o => (hreg μ hμ' o.1 n hn o.2).2.2
  choose Ψinv hci hl hb using hinvex
  have hsmooth : ∀ o, ContDiff ℝ 2 (Ψ o) ∧ ContDiff ℝ 1 (Ψinv o) ∧ IsLift (Ψ o) ∧
      Function.LeftInverse (Ψinv o) (Ψ o) := fun o =>
    ⟨(hreg μ hμ' o.1 n hn o.2).1, hci o, (hreg μ hμ' o.1 n hn o.2).2.1, hl o⟩
  have hinvbd : ∀ o y, ‖iteratedFDeriv ℝ 1 (Ψ o) y‖ ≤ Creg ∧
      ‖iteratedFDeriv ℝ 2 (Ψ o) y‖ ≤ Creg ∧ ‖iteratedFDeriv ℝ 1 (Ψinv o) y‖ ≤ Creg :=
    fun o y => ⟨by rw [norm_iteratedFDeriv_one]; exact (hb o y).1, (hb o y).2.1,
      by rw [norm_iteratedFDeriv_one]; exact (hb o y).2.2⟩
  have hmeas : Measurable (Function.uncurry Ψ) := measurable_canonSplit cf hμ' n
  set P := (blockMeasure L).prod (gaussSeq (splitVar μ n)) with hPdef
  have hb := hfour (BlockParam L × (ℕ → Pt 2)) P Ψ Ψinv hmeas hsmooth
    hinvbd (fun e he => hmom μ hμ n hn e he) R hR k hk ℓ hℓ
  -- the integrand
  set ξ : Pt 2 := (k : ℝ)⁻¹ • intVec ℓ
  set W : (Fin 2 → ℤ) → ℝ := fun m => weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec m)
  have hR0 : 0 ≤ R := by linarith
  have hW0 : ∀ m, 0 ≤ W m := fun m => weightW_nonneg (by positivity) _
  have hW1 : ∀ m, W m ≤ 1 := fun m => weightW_le_one _ _ _ _
  have hcm : ∀ m, Measurable fun o => coeffC (Ψ o) ξ m :=
    fun m => measurable_coeffC_of_uncurry hmeas ξ m
  set H : BlockParam L × (ℕ → Pt 2) → ℝ≥0∞ :=
    fun o => ∑' m, ENNReal.ofReal (W m) * ‖coeffC (Ψ o) ξ m‖ₑ ^ 2 with hHdef
  have hHm : Measurable H :=
    Measurable.ennreal_tsum fun m => measurable_const.mul ((hcm m).enorm.pow_const 2)
  set F : BlockParam L × (ℕ → Pt 2) → ℝ := fun o => ∑' m, W m * ‖coeffC (Ψ o) ξ m‖ ^ 2
  have hpars : ∀ o, HasSum (fun m => ‖coeffC (Ψ o) ξ m‖ ^ 2) 1 := fun o =>
    coeff_parseval _ (hsmooth o).1.continuous (hsmooth o).2.2.1 ξ
  have hsumm : ∀ o, Summable fun m => W m * ‖coeffC (Ψ o) ξ m‖ ^ 2 := fun o =>
    (hpars o).summable.of_nonneg_of_le (fun m => mul_nonneg (hW0 m) (sq_nonneg _))
      (fun m => mul_le_of_le_one_left (sq_nonneg _) (hW1 m))
  have hHF : ∀ o, H o = ENNReal.ofReal (F o) := by
    intro o
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (hW0 m) (sq_nonneg _)) (hsumm o)]
    refine tsum_congr fun m => ?_
    rw [ENNReal.ofReal_mul (hW0 m), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hF0 : ∀ o, 0 ≤ F o := fun o => tsum_nonneg fun m => mul_nonneg (hW0 m) (sq_nonneg _)
  have hF1 : ∀ o, F o ≤ 1 := fun o =>
    ((hsumm o).tsum_le_tsum (fun m => mul_le_of_le_one_left (sq_nonneg _) (hW1 m))
      (hpars o).summable).trans_eq (hpars o).tsum_eq
  have hFm : Measurable F := by
    have : F = fun o => (H o).toReal := funext fun o => by
      rw [hHF o, ENNReal.toReal_ofReal (hF0 o)]
    rw [this]; exact hHm.ennreal_toReal
  have hFi : Integrable F P := Integrable.of_bound hFm.aestronglyMeasurable 1
    (Eventually.of_forall fun o => by rw [Real.norm_eq_abs, abs_of_nonneg (hF0 o)]; exact hF1 o)
  have hG : splitFourierSum cf σ R q k ℓ μ n = fun w => ∫⁻ ζ, H (w, ζ) ∂(gaussSeq (splitVar μ n)) :=
    rfl
  refine ⟨?_, ?_⟩
  · rw [hG]; exact (hHm.lintegral_prod_right').aemeasurable
  · rw [hG, ← lintegral_prod _ hHm.aemeasurable]
    simp_rw [hHF]
    rw [← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hF0)]
    exact ENNReal.ofReal_le_ofReal hb

end AnomDiss
