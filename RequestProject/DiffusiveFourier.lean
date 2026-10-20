module

public import RequestProject.SplitFourierBound

/-!
# Proposition 3.11: the diffusive Fourier drift estimate

The time-one Fourier coefficients of a cell solution are limits of the averaged coefficients
`𝔼_ζ c_m^{Ψ_n}(ξ)` of the split maps; Jensen's inequality and Fatou's lemma then transfer the
per-`n` weighted Fourier bound for the split maps to the cell solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

section SplitHelpers

variable {L M : ℕ} {S : ℕ → ℝ}

/-- Jensen's inequality `|𝔼 f|² ≤ 𝔼|f|²` for a probability measure. -/
lemma sq_norm_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → ℂ} (hf : Integrable f P)
    (hf2 : Integrable (fun o => ‖f o‖ ^ 2) P) :
    ‖∫ o, f o ∂P‖ ^ 2 ≤ ∫ o, ‖f o‖ ^ 2 ∂P := by
  set c := ∫ o, ‖f o‖ ∂P
  have h1 : ‖∫ o, f o ∂P‖ ≤ c := norm_integral_le_integral_norm _
  have hn : Integrable (fun o => ‖f o‖) P := hf.norm
  have h0 : 0 ≤ ∫ o, (‖f o‖ - c) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∫ o, (‖f o‖ - c) ^ 2 ∂P = ∫ o, ‖f o‖ ^ 2 ∂P - c ^ 2 := by
    have : (fun o => (‖f o‖ - c) ^ 2) = fun o => ‖f o‖ ^ 2 - (2 * c) * ‖f o‖ + c ^ 2 := by
      funext o; ring
    rw [this, integral_add (f := fun o => ‖f o‖ ^ 2 - 2 * c * ‖f o‖) (g := fun _ => c ^ 2)
      (hf2.sub (hn.const_mul _)) (integrable_const _),
      integral_sub hf2 (hn.const_mul _), integral_const_mul, integral_const]
    simp; ring
  have hc0 : 0 ≤ c := integral_nonneg fun _ => norm_nonneg _
  nlinarith [norm_nonneg (∫ o, f o ∂P)]

lemma expChar_comp_mul (Ψ : Pt 2 → Pt 2) (ξ : Pt 2) (m : Fin 2 → ℤ) (y : Pt 2) :
    expChar ξ (Ψ y) * expChar (-(ξ + intVec m)) y =
      Complex.exp (2 * π * Complex.I * ((dot ξ (Ψ y - y) - dot (intVec m) y : ℝ) : ℂ)) := by
  unfold expChar
  rw [← Complex.exp_add]
  congr 1
  have : dot ξ (Ψ y - y) - dot (intVec m) y = dot ξ (Ψ y) + dot (-(ξ + intVec m)) y := by
    simp only [dot, Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Fin.sum_univ_two]; ring
  rw [this]; push_cast; ring

lemma norm_coeffC_le_one (Ψ : Pt 2 → Pt 2) (ξ : Pt 2) (m : Fin 2 → ℤ) :
    ‖coeffC Ψ ξ m‖ ≤ 1 := by
  unfold coeffC
  have hvol : volume (cell 2) = 1 := by
    simp [cell, Real.volume_Icc_pi]
  calc _ ≤ 1 * (volume (cell 2)).toReal := by
        refine norm_setIntegral_le_of_norm_le_const (by rw [hvol]; simp) fun y _ => ?_
        rw [Complex.norm_exp]; simp
    _ = 1 := by rw [hvol]; simp

lemma continuous_coeffC_splitMap {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, Continuous (ψ i)) (n : ℕ)
    (ξ : Pt 2) (m : Fin 2 → ℤ) : Continuous fun ζ => coeffC (splitMap ψ ζ n) ξ m := by
  unfold coeffC
  have hc := continuous_splitMap hψ n
  have hF : Continuous fun p : (ℕ → Pt 2) × Pt 2 => Complex.exp (2 * π * Complex.I *
      ((dot ξ (splitMap ψ p.1 n p.2 - p.2) - dot (intVec m) p.2 : ℝ) : ℂ)) := by
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    simp only [dot, Pi.sub_apply]
    have hi : ∀ i, Continuous fun p : (ℕ → Pt 2) × Pt 2 => splitMap ψ p.1 n p.2 i :=
      fun i => (continuous_apply i).comp hc
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict (cell 2)) := by
    rw [isFiniteMeasure_restrict]; simp [cell, Real.volume_Icc_pi]
  refine continuous_of_dominated (bound := fun _ => 1) (fun ζ => ?_) (fun ζ => ?_)
    (integrable_const _) (Eventually.of_forall fun y => ?_)
  · exact (hF.comp (by fun_prop : Continuous fun y : Pt 2 => (ζ, y))).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by rw [Complex.norm_exp]; simp
  · have hi : ∀ i, Continuous fun x : ℕ → Pt 2 => splitMap ψ x n y i := fun i =>
      (continuous_apply i).comp (hc.comp (Continuous.prodMk continuous_id continuous_const))
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    simp only [dot, Pi.sub_apply]
    fun_prop

/-- The averaged split coefficients: `∫_{𝕋²} P_n(e_ξ) e_{-(ξ+m)} = 𝔼_ζ c_m^{Ψ_n}(ξ)`. -/
lemma split_coeff_eq (μ : ℝ) (n : ℕ) {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, Continuous (ψ i))
    (ξ : Pt 2) (m : Fin 2 → ℤ) :
    ∫ y in cell 2, splitOp μ n ψ n (expChar ξ) y * expChar (-(ξ + intVec m)) y =
      ∫ ζ, coeffC (splitMap ψ ζ n) ξ m ∂(gaussSeq (splitVar μ n)) := by
  have hrep : ∀ y, splitOp μ n ψ n (expChar ξ) y =
      ∫ ζ, expChar ξ (splitMap ψ ζ n y) ∂(gaussSeq (splitVar μ n)) :=
    fun y => splitOp_eq_integral μ n hψ (continuous_expChar ξ) (fun x => (norm_expChar ξ x).le) n y
  simp_rw [hrep, ← integral_mul_const]
  unfold coeffC
  simp_rw [← expChar_comp_mul]
  have hc := continuous_splitMap hψ n
  have hcont : Continuous (Function.uncurry fun (y : Pt 2) (ζ : ℕ → Pt 2) =>
      expChar ξ (splitMap ψ ζ n y) * expChar (-(ξ + intVec m)) y) := by
    have h1 : Continuous fun p : Pt 2 × (ℕ → Pt 2) => splitMap ψ p.2 n p.1 :=
      hc.comp continuous_swap
    exact ((continuous_expChar ξ).comp h1).mul ((continuous_expChar _).comp continuous_fst)
  refine integral_integral_swap ?_
  refine Integrable.of_bound hcont.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
  simp [Function.uncurry, norm_expChar]

lemma continuous_canonPsi (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (n i : ℕ) : Continuous (canonPsi cf μ w n i) :=
  (splitField_good cf hμ w).continuous_gflow _ _

/-- The averaged split coefficients converge to the time-one coefficients of the cell solution. -/
lemma tendsto_split_coeff (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (ξ : Pt 2) {h : ℝ → Pt 2 → ℂ}
    (hcell : IsCellSolution (dampedB cf μ w) μ ξ h) (m : Fin 2 → ℤ) :
    Tendsto (fun n : ℕ => ∫ ζ, coeffC (splitMap (canonPsi cf μ w n) ζ n) ξ m
      ∂(gaussSeq (splitVar μ n))) atTop (𝓝 (cellCoeff h ξ m)) := by
  obtain ⟨C, β, hβ, hC⟩ := split_cell_uniform cf hμ w ξ hcell
  have hrw : ∀ n : ℕ, ∫ ζ, coeffC (splitMap (canonPsi cf μ w n) ζ n) ξ m
      ∂(gaussSeq (splitVar μ n)) =
      ∫ y in cell 2, splitOp μ n (canonPsi cf μ w n) n (expChar ξ) y *
        expChar (-(ξ + intVec m)) y := fun n =>
    (split_coeff_eq μ n (continuous_canonPsi cf hμ w n) ξ m).symm
  simp_rw [hrw]
  obtain ⟨β0, -, -, hreg⟩ := hcell.regular
  have hh1 : Continuous (h 1) := (hreg.smooth_x 1 ⟨zero_le_one, le_rfl⟩).continuous
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(β / 2))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by positivity : 0 < β / 2)).comp
      tendsto_natCast_atTop_atTop
    simpa using this.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hP := splitOp_cont_bdd μ n (continuous_canonPsi cf hμ w n) (continuous_expChar ξ)
    (fun x => (norm_expChar ξ x).le) n
  have hi1 : IntegrableOn (fun y => splitOp μ n (canonPsi cf μ w n) n (expChar ξ) y *
      expChar (-(ξ + intVec m)) y) (cell 2) :=
    (hP.1.mul (continuous_expChar _))
      |>.continuousOn.integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun y => h 1 y * expChar (-(ξ + intVec m)) y) (cell 2) :=
    (hh1.mul (continuous_expChar _))
      |>.continuousOn.integrableOn_compact isCompact_Icc
  unfold cellCoeff
  rw [← integral_sub hi1 hi2]
  calc _ ≤ C * (n : ℝ) ^ (-(β / 2)) * (volume (cell 2)).toReal := by
        refine norm_setIntegral_le_of_norm_le_const (by rw [volume_cell_two]; simp) fun y _ => ?_
        rw [← sub_mul, norm_mul, norm_expChar, mul_one]
        exact hC n hn y
    _ = _ := by rw [volume_cell_two]; simp

/-- Fatou's lemma for series of nonnegative extended reals. -/
lemma tsum_liminf_le {ι : Type*} [Countable ι] (f : ℕ → ι → ℝ≥0∞) :
    ∑' i, liminf (fun n => f n i) atTop ≤ liminf (fun n => ∑' i, f n i) atTop := by
  letI : MeasurableSpace ι := ⊤
  have hms : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have h := lintegral_liminf_le' (μ := Measure.count) (f := f) (u := (atTop : Filter ℕ))
    (fun n => (measurable_from_top (f := f n)).aemeasurable)
  simpa only [lintegral_count] using h

/-- Jensen's inequality for the averaged split coefficients, weighted. -/
lemma ofReal_mul_sq_integral_le (P : Measure (ℕ → Pt 2)) [IsProbabilityMeasure P]
    {c : (ℕ → Pt 2) → ℂ} (hc : Continuous c) (hc1 : ∀ ζ, ‖c ζ‖ ≤ 1) {W : ℝ} (hW : 0 ≤ W) :
    ENNReal.ofReal (W * ‖∫ ζ, c ζ ∂P‖ ^ 2) ≤ ∫⁻ ζ, ENNReal.ofReal W * ‖c ζ‖ₑ ^ 2 ∂P := by
  have hi : Integrable c P := Integrable.of_bound hc.aestronglyMeasurable 1
    (Eventually.of_forall hc1)
  have hi2 : Integrable (fun ζ => ‖c ζ‖ ^ 2) P := Integrable.of_bound
    (hc.norm.pow 2).aestronglyMeasurable 1 (Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (norm_nonneg _) (hc1 ζ))
  calc ENNReal.ofReal (W * ‖∫ ζ, c ζ ∂P‖ ^ 2)
      ≤ ENNReal.ofReal (W * ∫ ζ, ‖c ζ‖ ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sq_norm_integral_le P hi hi2) hW)
    _ = ENNReal.ofReal W * ∫⁻ ζ, ENNReal.ofReal (‖c ζ‖ ^ 2) ∂P := by
        rw [ENNReal.ofReal_mul hW, ofReal_integral_eq_lintegral_ofReal hi2
          (Eventually.of_forall fun _ => by positivity)]
    _ = ∫⁻ ζ, ENNReal.ofReal W * ‖c ζ‖ₑ ^ 2 ∂P := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1; funext ζ
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

/-- Per-`ω` Fatou step: the weighted Fourier sum of the cell solution is bounded by the
`liminf` of the averaged weighted Fourier sums of the split maps. -/
lemma cell_sum_le_liminf (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (ξ : Pt 2) {h : ℝ → Pt 2 → ℂ}
    (hcell : IsCellSolution (dampedB cf μ w) μ ξ h) (W : (Fin 2 → ℤ) → ℝ) (hW : ∀ m, 0 ≤ W m) :
    ∑' m, ENNReal.ofReal (W m * ‖cellCoeff h ξ m‖ ^ 2) ≤
      liminf (fun n : ℕ => ∫⁻ ζ, ∑' m, ENNReal.ofReal (W m) *
        ‖coeffC (splitMap (canonPsi cf μ w n) ζ n) ξ m‖ₑ ^ 2 ∂(gaussSeq (splitVar μ n))) atTop := by
  set a : ℕ → (Fin 2 → ℤ) → ℂ := fun n m =>
    ∫ ζ, coeffC (splitMap (canonPsi cf μ w n) ζ n) ξ m ∂(gaussSeq (splitVar μ n))
  have hlim : ∀ m, ENNReal.ofReal (W m * ‖cellCoeff h ξ m‖ ^ 2) =
      liminf (fun n => ENNReal.ofReal (W m * ‖a n m‖ ^ 2)) atTop := by
    intro m
    refine (Tendsto.liminf_eq ?_).symm
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul
      (((tendsto_split_coeff cf hμ w ξ hcell m).norm).pow 2))
  have hcont : ∀ n m, Continuous fun ζ => coeffC (splitMap (canonPsi cf μ w n) ζ n) ξ m :=
    fun n m => continuous_coeffC_splitMap (continuous_canonPsi cf hμ w n) n ξ m
  simp_rw [hlim]
  refine (tsum_liminf_le _).trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
  rw [lintegral_tsum fun m => ((hcont n m).measurable.enorm.pow_const 2).aemeasurable.const_mul _]
  exact ENNReal.tsum_le_tsum fun m =>
    ofReal_mul_sq_integral_le _ (hcont n m) (fun ζ => norm_coeffC_le_one _ _ _) (hW m)

lemma ofReal_tsum_le_tsum_ofReal {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ENNReal.ofReal (∑' i, f i) ≤ ∑' i, ENNReal.ofReal (f i) := by
  by_cases hs : Summable f
  · rw [ENNReal.ofReal_tsum_of_nonneg hf hs]
  · rw [tsum_eq_zero_of_not_summable hs]; simp

end SplitHelpers

/-- **Proposition 3.11** (diffusive Fourier drift).  Given the negative moment bound of
Lemma 2.5 and a family of controls, there are `μ_* > 0` and `R₀ ≥ 1` such that for every
`R ≥ R₀`, `0 ≤ μ ≤ μ_*`, `k ≥ 1` and `|ℓ| ≥ Rk`,
`𝔼_ω ∑ₘ W_{qk}(ℓ + km)|a_m^{μ,ω}(ℓ/k)|² ≤ ½ W_k(ℓ)`. -/
theorem diffusive_fourier (q : ℕ) (hq : 3 ≤ q) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (L : ℕ)
    (hneg : NegMomentBound q σ L) {M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) :
    ∃ μstar R₀ : ℝ, 0 < μstar ∧ 1 ≤ R₀ ∧ ∀ R, R₀ ≤ R → ∀ μ ∈ Icc 0 μstar,
      ∀ k : ℕ, 1 ≤ k → ∀ ℓ : Fin 2 → ℤ, R * k ≤ euclNorm (intVec ℓ) →
      ∀ h : BlockParam L → ℝ → Pt 2 → ℂ,
        (∀ w, IsCellSolution (dampedB cf μ w) μ ((k : ℝ)⁻¹ • intVec ℓ) (h w)) →
        ∫ w, ∑' m, weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec m) *
            ‖cellCoeff (h w) ((k : ℝ)⁻¹ • intVec ℓ) m‖ ^ 2 ∂(blockMeasure L)
          ≤ weightW σ R k (intVec ℓ) / 2 := by
  obtain ⟨μstar, R₀, hμ0, hμ1, hR₀, hF⟩ := split_fourier_bound q hq σ hσ0 hσ1 L hneg cf
  refine ⟨μstar, R₀, hμ0, hR₀, fun R hR μ hμ k hk ℓ hℓ h hcell => ?_⟩
  have hμ' : μ ∈ Icc (0 : ℝ) 1 := ⟨hμ.1, hμ.2.trans hμ1⟩
  obtain ⟨N, hN⟩ := hF R hR μ hμ k hk ℓ hℓ
  have hR0 : 0 ≤ R := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set ξ : Pt 2 := (k : ℝ)⁻¹ • intVec ℓ
  set W : (Fin 2 → ℤ) → ℝ := fun m => weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec m)
  have hW : ∀ m, 0 ≤ W m := fun m => weightW_nonneg (by positivity) _
  set F : BlockParam L → ℝ := fun w => ∑' m, W m * ‖cellCoeff (h w) ξ m‖ ^ 2
  have hF0 : ∀ w, 0 ≤ F w := fun w => tsum_nonneg fun m => mul_nonneg (hW m) (sq_nonneg _)
  set G : ℕ → BlockParam L → ℝ≥0∞ := fun n w => splitFourierSum cf σ R q k ℓ μ (n + N) w
  have hpw : ∀ w, ENNReal.ofReal (F w) ≤ liminf (fun n => G n w) atTop := by
    intro w
    refine (ofReal_tsum_le_tsum_ofReal _ fun m => mul_nonneg (hW m) (sq_nonneg _)).trans ?_
    refine (cell_sum_le_liminf cf hμ' w ξ (hcell w) W hW).trans_eq ?_
    exact (liminf_nat_add (fun n => splitFourierSum cf σ R q k ℓ μ n w) N).symm
  have hWnn : 0 ≤ weightW σ R k (intVec ℓ) / 2 :=
    div_nonneg (weightW_nonneg (by positivity) _) zero_le_two
  have hlin : ∫⁻ w, ENNReal.ofReal (F w) ∂(blockMeasure L) ≤
      ENNReal.ofReal (weightW σ R k (intVec ℓ) / 2) :=
    calc _ ≤ ∫⁻ w, liminf (fun n => G n w) atTop ∂(blockMeasure L) := lintegral_mono hpw
      _ ≤ liminf (fun n => ∫⁻ w, G n w ∂(blockMeasure L)) atTop :=
          lintegral_liminf_le' fun n => (hN (n + N) (by omega)).1
      _ ≤ _ := liminf_le_of_frequently_le'
          (Frequently.of_forall fun n => (hN (n + N) (by omega)).2)
  by_cases hm : AEStronglyMeasurable F (blockMeasure L)
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hm]
    exact ENNReal.toReal_le_of_le_ofReal hWnn hlin
  · rw [integral_non_aestronglyMeasurable hm]; exact hWnn

end AnomDiss
