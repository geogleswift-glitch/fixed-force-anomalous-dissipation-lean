module

public import RequestProject.HolderCalc

/-!
# Lemma 4.6: regularity of the fixed horizontal force

The force `g_ω` is a sum of rescaled pulses supported in disjoint open subintervals of the
pulse intervals `I_j`.  Its `r`-th time derivative is the corresponding sum of the pieces
`(k_j δ_j^{r+2})⁻¹ (∂ₛ^{r+1} b_{ω_j})((t - s_j)/δ_j, k_j x)`.  Each piece is bounded in `C^α`
by `C k_j^{α-1} δ_j^{-r-2}`, which tends to zero (even after division by `η_j`), so all time
derivatives extend by zero across the accumulation time `T_*`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-! ### The pieces -/

/-- The `j`-th piece of the `r`-th time derivative of the force. -/
def fpiece (w : Phase) (r j : ℕ) (t : ℝ) (x : Pt 2) : Pt 2 :=
  (1 / (kk j * δs j ^ (r + 2))) •
    eField (iteratedDeriv (r + 1) (cf₀.coef (w j).1) ((t - sj j) / δs j)) (kk j • x - (w j).2)

/-- The `r`-th time derivative of the force (as a sum of pieces). -/
def forceD (w : Phase) (r : ℕ) (t : ℝ) (x : Pt 2) : Pt 2 :=
  ∑' j : ℕ, if 1 ≤ j then fpiece w r j t x else 0

lemma iteratedDeriv_coef_eq_zero {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S)
    (b : Fin L → Bool × Pt 2) (n : ℕ) {s : ℝ} (hs : s ∉ Icc cf.a₀ cf.b₀) :
    iteratedDeriv n (cf.coef b) s = 0 := by
  have h : cf.coef b =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hs] with u hu using cf.support b u hu
  rw [h.iteratedDeriv_eq n]
  simp

lemma fpiece_eq_zero' (w : Phase) (r : ℕ) {j : ℕ} {t : ℝ}
    (ht : (t - sj j) / δs j ∉ Icc cf₀.a₀ cf₀.b₀) : fpiece w r j t = 0 := by
  funext x
  simp [fpiece, iteratedDeriv_coef_eq_zero cf₀ _ _ ht, eField_zero]

lemma fpiece_eq_zero (w : Phase) (r : ℕ) {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (ht : t ∉ Ioo (sj j) (sj j + δs j)) : fpiece w r j t = 0 := by
  refine fpiece_eq_zero' w r fun hu => ht ?_
  have hδ := δs_pos j hj
  have h0 := cf₀.ha₀
  have h1 := cf₀.hb₀
  have hu0 : 0 < (t - sj j) / δs j := h0.trans_le hu.1
  have hu1 : (t - sj j) / δs j < 1 := hu.2.trans_lt h1
  rw [lt_div_iff₀ hδ] at hu0
  rw [div_lt_iff₀ hδ] at hu1
  constructor <;> linarith

lemma forceD_eq_single (w : Phase) (r : ℕ) {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (ht : t ∈ Ioo (sj j) (sj j + δs j)) : forceD w r t = fpiece w r j t := by
  funext x
  unfold forceD
  rw [tsum_eq_single j fun j' hj' => ?_, if_pos hj]
  split_ifs with h
  · rw [fpiece_eq_zero w r h fun ht' => hj' (Ij_unique h hj (Ioo_subset_Icc_self ht')
      (Ioo_subset_Icc_self ht))]
    rfl
  · rfl

lemma forceD_eq_zero (w : Phase) (r : ℕ) {t : ℝ}
    (ht : ∀ j, 1 ≤ j → fpiece w r j t = 0) : forceD w r t = 0 := by
  funext x
  unfold forceD
  have : ∀ j, (if 1 ≤ j then fpiece w r j t x else 0) = 0 := fun j => by
    split_ifs with h
    · rw [ht j h]; rfl
    · rfl
  simp only [this, tsum_zero]
  rfl

lemma forceD_single (w : Phase) (r : ℕ) (t : ℝ) : forceD w r t = 0 ∨
    ∃ j, 1 ≤ j ∧ t ∈ Ioo (sj j) (sj j + δs j) ∧ forceD w r t = fpiece w r j t := by
  by_cases h : ∃ j, 1 ≤ j ∧ t ∈ Ioo (sj j) (sj j + δs j)
  · obtain ⟨j, hj, ht⟩ := h
    exact Or.inr ⟨j, hj, ht, forceD_eq_single w r hj ht⟩
  · push_neg at h
    exact Or.inl (forceD_eq_zero w r fun j hj => fpiece_eq_zero w r hj (h j hj))

lemma forceD_zero_eq (w : Phase) : forceD w 0 = gForce w := by
  funext t x
  unfold forceD gForce
  congr 1
  funext j
  by_cases hj : 1 ≤ j
  · by_cases ht : t ∈ Ij j
    · simp only [hj, ht, and_self, if_true, fpiece, bDot, iteratedDeriv_one, zero_add]
    · rw [if_pos hj, if_neg fun h => ht h.2,
        fpiece_eq_zero w 0 hj fun h => ht (Ioo_subset_Icc_self h)]
      rfl
  · rw [if_neg hj, if_neg fun h => hj h.1]

/-! ### Hölder bounds -/

lemma eBasis_holderBd {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (i : Fin 4) :
    ∃ K, HolderBd α (eBasis i) K := by
  obtain ⟨C0, hC0, h0⟩ := exists_bound_iteratedFDeriv_eBasis 0 i
  obtain ⟨C1, hC1, h1⟩ := exists_bound_iteratedFDeriv_eBasis 1 i
  have hb : ∀ x, ‖eBasis i x‖ ≤ C0 := fun x => by simpa using h0 x
  have hd : ∀ x, ‖fderiv ℝ (eBasis i) x‖ ≤ C1 := fun x => by
    simpa [norm_iteratedFDeriv_one] using h1 x
  have hdiff : Differentiable ℝ (eBasis i) := (contDiff_eBasis i).differentiable (by simp)
  have hlip : ∀ x y, ‖eBasis i x - eBasis i y‖ ≤ C1 * ‖x - y‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) (fun z _ => hd z)
      (mem_univ y) (mem_univ x)
  refine ⟨max (2 * C0) C1, fun x => (hb x).trans (by
    have := le_max_left (2 * C0) C1; linarith), fun x y => ?_⟩
  have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  rcases le_total ‖x - y‖ 1 with h | h
  · calc ‖eBasis i x - eBasis i y‖ ≤ C1 * ‖x - y‖ := hlip x y
      _ ≤ C1 * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left (by
          simpa using Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) h hα0 hα1) hC1
      _ ≤ max (2 * C0) C1 * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right (le_max_right _ _) hr
  · calc ‖eBasis i x - eBasis i y‖ ≤ ‖eBasis i x‖ + ‖eBasis i y‖ := norm_sub_le _ _
      _ ≤ 2 * C0 := by linarith [hb x, hb y]
      _ ≤ 2 * C0 * ‖x - y‖ ^ α := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow h hα0)
      _ ≤ max (2 * C0) C1 * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right (le_max_left _ _) hr

lemma eField_holderBd {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ v : Fin 4 → ℝ, HolderBd α (eField v) (K * ‖v‖) := by
  choose K hK using eBasis_holderBd hα0 hα1
  refine ⟨∑ i, K i, Finset.sum_nonneg fun i _ => (hK i).nonneg, fun v => ?_⟩
  have h := HolderBd.sum Finset.univ (fun i _ => (hK i).smul (v i))
  have e : eField v = fun x => ∑ i ∈ Finset.univ, v i • eBasis i x := rfl
  rw [e]
  refine h.mono ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm (K i)]
  refine mul_le_mul_of_nonneg_right ?_ (hK i).nonneg
  simpa [Real.norm_eq_abs] using norm_le_pi_norm v i

lemma one_le_kk (j : ℕ) : 1 ≤ kk j := by
  unfold kk
  exact one_le_pow₀ (by have := qq_ge; exact_mod_cast (by omega : 1 ≤ qq))

lemma fpiece_holderBd {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ (w : Phase) (r j : ℕ) (t : ℝ), HolderBd α (fpiece w r j t)
      (|1 / (kk j * δs j ^ (r + 2))| * (kk j ^ α *
        (K * ‖iteratedDeriv (r + 1) (cf₀.coef (w j).1) ((t - sj j) / δs j)‖))) := by
  obtain ⟨K, hK0, hK⟩ := eField_holderBd hα0 hα1
  exact ⟨K, hK0, fun w r j t => ((hK _).comp_affine hα0 (one_le_kk j) (w j).2).smul _⟩

/-- Uniform bound on the pieces: `‖piece‖_{C^α} ≤ C k_j^{α-1} δ_j^{-r-2}`. -/
lemma fpiece_bound {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (r : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (w : Phase) (j : ℕ), 1 ≤ j → ∀ t, HolderBd α (fpiece w r j t)
      (C * kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2)) := by
  obtain ⟨K, hK0, hK⟩ := fpiece_holderBd hα0 hα1
  obtain ⟨Cm, hCm⟩ := cf₀.mixed (r + 1)
  have hCm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm (fun _ => (true, 0)) 0)
  refine ⟨K * Cm, by positivity, fun w j hj t => (hK w r j t).mono ?_⟩
  have hk := (zero_lt_one.trans_le (one_le_kk j))
  have hδ := δs_pos j hj
  have e : |1 / (kk j * δs j ^ (r + 2))| * (kk j ^ α * (K * Cm)) =
      K * Cm * kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2) := by
    rw [abs_of_pos (by positivity), Real.rpow_sub_one hk.ne',
      show -(r : ℝ) - 2 = -((r + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hδ.le,
      Real.rpow_natCast]
    field_simp
  calc _ ≤ |1 / (kk j * δs j ^ (r + 2))| * (kk j ^ α * (K * Cm)) := by
        gcongr; exact hCm _ _
    _ = _ := e

/-! ### The `C^α` norm -/

lemma holderNorm_zero' {d : ℕ} {E : Type*} [NormedAddCommGroup E] (α : ℝ) :
    holderNorm α (0 : Pt d → E) = 0 := by
  simp [holderNorm]

lemma holderNorm_add_le {d : ℕ} {E : Type*} [NormedAddCommGroup E] (α : ℝ) (f g : Pt d → E) :
    holderNorm α (f + g) ≤ holderNorm α f + holderNorm α g := by
  unfold holderNorm
  calc (⨆ x, ‖(f + g) x‖ₑ) + ⨆ x, ⨆ y, ‖(f + g) x - (f + g) y‖ₑ / ‖x - y‖ₑ ^ α
      ≤ ((⨆ x, ‖f x‖ₑ) + ⨆ x, ‖g x‖ₑ) + ((⨆ x, ⨆ y, ‖f x - f y‖ₑ / ‖x - y‖ₑ ^ α) +
          ⨆ x, ⨆ y, ‖g x - g y‖ₑ / ‖x - y‖ₑ ^ α) := by
        gcongr
        · exact iSup_le fun x => (enorm_add_le _ _).trans (add_le_add
            (le_iSup (fun x => ‖f x‖ₑ) x) (le_iSup (fun x => ‖g x‖ₑ) x))
        · refine iSup₂_le fun x y => ?_
          have e : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
            simp only [Pi.add_apply]; abel
          rw [e]
          calc ‖(f x - f y) + (g x - g y)‖ₑ / ‖x - y‖ₑ ^ α
              ≤ (‖f x - f y‖ₑ + ‖g x - g y‖ₑ) / ‖x - y‖ₑ ^ α := by
                gcongr; exact enorm_add_le _ _
            _ = ‖f x - f y‖ₑ / ‖x - y‖ₑ ^ α + ‖g x - g y‖ₑ / ‖x - y‖ₑ ^ α := ENNReal.add_div
            _ ≤ _ := add_le_add
                (le_iSup₂ (f := fun x y => ‖f x - f y‖ₑ / ‖x - y‖ₑ ^ α) x y)
                (le_iSup₂ (f := fun x y => ‖g x - g y‖ₑ / ‖x - y‖ₑ ^ α) x y)
    _ = _ := add_add_add_comm _ _ _ _

lemma holderNorm_sum_le {d : ℕ} {E : Type*} [NormedAddCommGroup E] {ι : Type*} (α : ℝ)
    (s : Finset ι) (f : ι → Pt d → E) :
    holderNorm α (∑ i ∈ s, f i) ≤ ∑ i ∈ s, holderNorm α (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [holderNorm_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (holderNorm_add_le _ _ _).trans (add_le_add le_rfl ih)

/-! ### Differentiability of the pieces in `C^α` -/

lemma fpiece_deriv {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (w : Phase) (r j : ℕ) (t : ℝ) :
    Tendsto (fun h : ℝ => holderNorm α (h⁻¹ • (fpiece w r j (t + h) - fpiece w r j t) -
      fpiece w (r + 1) j t)) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := eField_holderBd hα0.le hα1
  set A := 1 / (kk j * δs j ^ (r + 2)) with hA
  set c : ℝ → Fin 4 → ℝ := fun u =>
    iteratedDeriv (r + 1) (cf₀.coef (w j).1) ((u - sj j) / δs j) with hc
  set c' : Fin 4 → ℝ :=
    (δs j)⁻¹ • iteratedDeriv (r + 1 + 1) (cf₀.coef (w j).1) ((t - sj j) / δs j) with hc'
  have hcd : HasDerivAt c c' t := by
    have h1 : HasDerivAt (fun u => (u - sj j) / δs j) (1 / δs j) t :=
      ((hasDerivAt_id t).sub_const _).div_const _
    have hd : Differentiable ℝ (iteratedDeriv (r + 1) (cf₀.coef (w j).1)) :=
      (cf₀.contDiff_coef _).differentiable_iteratedDeriv _
        (by exact_mod_cast WithTop.coe_lt_top _)
    have h2 : HasDerivAt (iteratedDeriv (r + 1) (cf₀.coef (w j).1))
        (iteratedDeriv (r + 1 + 1) (cf₀.coef (w j).1) ((t - sj j) / δs j))
        ((t - sj j) / δs j) := by
      rw [iteratedDeriv_succ (n := r + 1)]; exact (hd _).hasDerivAt
    have := h2.scomp t h1
    simpa only [hc, hc', Function.comp_def, one_div] using this
  set Δ : ℝ → Fin 4 → ℝ := fun h => h⁻¹ • (c (t + h) - c t) - c' with hΔdef
  have hΔ : Tendsto (fun h => ‖Δ h‖) (𝓝[≠] 0) (𝓝 0) := by
    have h3 := hcd.tendsto_slope_zero.sub_const c'
    rw [sub_self] at h3
    simpa only [hΔdef, Function.comp_def, norm_zero] using
      (continuous_norm.tendsto (0 : Fin 4 → ℝ)).comp h3
  have key : ∀ h, h⁻¹ • (fpiece w r j (t + h) - fpiece w r j t) - fpiece w (r + 1) j t =
      fun x => A • eField (Δ h) (kk j • x - (w j).2) := by
    intro h
    funext x
    simp only [fpiece, Pi.sub_apply, Pi.smul_apply, ← eFieldCLM_apply, hΔdef, map_sub, map_smul,
      hc, hc']
    have e : 1 / (kk j * δs j ^ (r + 1 + 2)) = A * (δs j)⁻¹ := by rw [hA]; ring
    rw [e]
    module
  have hbound : ∀ h, holderNorm α (h⁻¹ • (fpiece w r j (t + h) - fpiece w r j t) -
      fpiece w (r + 1) j t) ≤ ENNReal.ofReal (2 * (|A| * (kk j ^ α * (K * ‖Δ h‖)))) := fun h => by
    rw [key h]
    exact holderNorm_le_of_bd hα0 (((hK (Δ h)).comp_affine hα0.le (one_le_kk j) _).smul A)
  have hlim : Tendsto (fun h => ENNReal.ofReal (2 * (|A| * (kk j ^ α * (K * ‖Δ h‖)))))
      (𝓝[≠] 0) (𝓝 0) := by
    have h4 : Tendsto (fun h => 2 * (|A| * (kk j ^ α * (K * ‖Δ h‖)))) (𝓝[≠] 0)
        (𝓝 (2 * (|A| * (kk j ^ α * (K * 0))))) :=
      (((hΔ.const_mul K).const_mul _).const_mul _).const_mul _
    simpa using ENNReal.tendsto_ofReal h4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun h => zero_le)
    hbound

/-! ### Localization in time -/

lemma exists_sj_gt {t : ℝ} (ht : t < Tstar) : ∃ n, t < sj n := by
  have hs := summable_stage.hasSum.tendsto_sum_nat
  obtain ⟨n, hn⟩ := (hs.eventually (lt_mem_nhds ht)).exists
  refine ⟨n + 1, ?_⟩
  have e : sj (n + 1) = ∑ i ∈ Finset.range n, (δs (i + 1) + ηs (i + 1)) := by
    unfold sj; rw [Finset.sum_Ico_eq_sum_range]; simp [add_comm]
  rw [e]; exact hn

lemma sj_add_δs_le_Tstar (j : ℕ) (hj : 1 ≤ j) : sj j + δs j ≤ Tstar :=
  (sj_lt_succ j hj).le.trans (sj_bounds _).2

lemma forceD_local_lt (w : Phase) {t : ℝ} (ht : t < Tstar) : ∃ n : ℕ,
    ∀ᶠ t' in 𝓝 t, ∀ r, forceD w r t' = ∑ j ∈ Finset.Ico 1 n, fpiece w r j t' := by
  obtain ⟨n, hn⟩ := exists_sj_gt ht
  refine ⟨n, ?_⟩
  filter_upwards [Iio_mem_nhds hn] with t' ht' r
  funext x
  unfold forceD
  rw [tsum_eq_sum (s := Finset.range n) fun j hj => ?_]
  · rw [Finset.sum_apply, ← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  · split_ifs with h1
    · rw [fpiece_eq_zero w r h1 fun h => ?_]
      · rfl
      have := sj_mono (show n ≤ j by simpa using hj)
      linarith [h.1, ht'.out]
    · rfl

lemma forceD_local_gt (w : Phase) {t : ℝ} (ht : Tstar < t) :
    ∀ᶠ t' in 𝓝 t, ∀ r, forceD w r t' = 0 := by
  filter_upwards [Ioi_mem_nhds ht] with t' ht' r
  exact forceD_eq_zero w r fun j hj => fpiece_eq_zero w r hj fun h => by
    have := sj_add_δs_le_Tstar j hj
    linarith [h.2, ht'.out]

lemma forceD_Tstar (w : Phase) (r : ℕ) : forceD w r Tstar = 0 :=
  forceD_eq_zero w r fun j hj => fpiece_eq_zero w r hj fun h => by
    have := sj_add_δs_le_Tstar j hj
    linarith [h.2]

/-- The decay `(k_j δ_j^{r+2})⁻¹ k_j^α / η_j → 0`. -/
lemma piece_decay {α : ℝ} (hα1 : α < 1) (r : ℕ) :
    Tendsto (fun j : ℕ => kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2) / ηs j) atTop (𝓝 0) := by
  have hq : (1 : ℝ) < qq := by have := qq_ge; exact_mod_cast (by omega : 1 < qq)
  set ρ : ℝ := (qq : ℝ) ^ (α - 1) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by linarith) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one (3 * r + 8)
    (by rw [abs_of_pos hρ0]; exact hρ1)).const_mul (τstar ^ (r + 3))⁻¹
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hδ := δs_pos j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hkρ : kk j ^ (α - 1) = ρ ^ j := by
    rw [hρ, ← Real.rpow_mul_natCast (by linarith), mul_comm, Real.rpow_natCast_mul (by linarith)]
    rfl
  rw [hkρ, show -(r : ℝ) - 2 = -((r + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hδ.le,
    Real.rpow_natCast]
  have hj' : (j : ℝ) ≠ 0 := hj0.ne'
  unfold δs ηs
  have hτ : τstar ≠ 0 := by unfold τstar; norm_num
  rw [div_pow, ← pow_mul, inv_div, div_div_eq_mul_div]
  rw [show 3 * r + 8 = 3 * (r + 2) + 2 by ring, show r + 3 = r + 2 + 1 by ring,
    pow_add (j : ℝ), pow_succ τstar (r + 2)]
  field_simp

lemma forceD_deriv_Tstar {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (w : Phase) (r : ℕ) :
    Tendsto (fun h : ℝ => holderNorm α (h⁻¹ • (forceD w r (Tstar + h) - forceD w r Tstar) -
      forceD w (r + 1) Tstar)) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := fpiece_bound hα0.le hα1.le r
  simp only [forceD_Tstar, sub_zero]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨ε', hε'0, hε'1, hε'2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hε' : 0 < ε' := ENNReal.ofReal_pos.1 hε'1
  obtain ⟨J, hJ⟩ := ((piece_decay hα1 r).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε' / (2 * C + 1) by positivity))).exists_forall_of_atTop
  set J' := max J 1
  have hJ'1 : 1 ≤ J' := le_max_right _ _
  have hηJ : 0 < ηs J' := ηs_pos J' hJ'1
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (neg_lt_zero.2 hηJ) hηJ)] with h hh
  rcases forceD_single w r (Tstar + h) with h0 | ⟨j, hj, hjI, hjeq⟩
  · rw [h0, smul_zero, holderNorm_zero']; exact zero_le
  rw [hjeq]
  have hsj : sj j + δs j + ηs j ≤ Tstar := by rw [← sj_succ j hj]; exact (sj_bounds _).2
  have hηj := ηs_pos j hj
  have hneg : h < -ηs j := by linarith [hjI.2]
  have hjJ : J' ≤ j := by
    by_contra hlt
    push_neg at hlt
    have : ηs J' ≤ ηs j := by
      unfold ηs
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
      have : (j : ℝ) ≤ J' := by exact_mod_cast hlt.le
      apply div_le_div_of_nonneg_left (by unfold τstar; norm_num) (by positivity)
      nlinarith
    linarith [hh.1]
  have hX := hJ j ((le_max_left J 1).trans hjJ)
  set X := kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2)
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (by linarith [one_le_kk j]) _)
    (Real.rpow_nonneg (δs_pos j hj).le _)
  have hb := (hC w j hj (Tstar + h)).smul h⁻¹
  refine (holderNorm_le_of_bd hα0 hb).trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hε'2.le)
  have hinv : |h⁻¹| ≤ (ηs j)⁻¹ := by
    rw [abs_inv]
    exact inv_anti₀ hηj (by rw [abs_of_neg (by linarith)]; linarith)
  have h1 : |h⁻¹| * (C * kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2)) ≤ C * (X / ηs j) := by
    calc |h⁻¹| * (C * kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2)) = |h⁻¹| * (C * X) := by
          simp only [X]; ring
      _ ≤ (ηs j)⁻¹ * (C * X) := mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = C * (X / ηs j) := by ring
  have h2 : C * (X / ηs j) ≤ C * (ε' / (2 * C + 1)) := mul_le_mul_of_nonneg_left hX.le hC0
  have h3 : 2 * (C * (ε' / (2 * C + 1))) ≤ ε' := by
    rw [← mul_assoc, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma forceD_deriv {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (w : Phase) (r : ℕ) (t : ℝ) :
    Tendsto (fun h : ℝ => holderNorm α (h⁻¹ • (forceD w r (t + h) - forceD w r t) -
      forceD w (r + 1) t)) (𝓝[≠] 0) (𝓝 0) := by
  have hc : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 t) := by
    simpa using (tendsto_const_nhds.add tendsto_id : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)))
  rcases lt_trichotomy t Tstar with ht | rfl | ht
  · obtain ⟨n, hn⟩ := forceD_local_lt w ht
    have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ r, forceD w r (t + h) =
        ∑ j ∈ Finset.Ico 1 n, fpiece w r j (t + h) := nhdsWithin_le_nhds (hc.eventually hn)
    have h0 := hn.self_of_nhds
    have hsum := tendsto_finset_sum (Finset.Ico 1 n) fun j _ => fpiece_deriv hα0 hα1.le w r j t
    rw [Finset.sum_const_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun h => zero_le) ?_
    filter_upwards [hev] with h hh
    rw [hh r, h0 r, h0 (r + 1), ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact holderNorm_sum_le α _ _
  · exact forceD_deriv_Tstar hα0 hα1 w r
  · have hn := forceD_local_gt w ht
    have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ r, forceD w r (t + h) = 0 :=
      nhdsWithin_le_nhds (hc.eventually hn)
    have h0 := hn.self_of_nhds
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with h hh
    rw [hh r, h0 r, h0 (r + 1)]
    simp [holderNorm_zero']

lemma forceD_finite {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (w : Phase) (r : ℕ) (t : ℝ) :
    holderNorm α (forceD w r t) < ⊤ := by
  obtain ⟨C, -, hC⟩ := fpiece_bound hα0.le hα1.le r
  rcases forceD_single w r t with h0 | ⟨j, hj, -, hjeq⟩
  · rw [h0, holderNorm_zero']; exact ENNReal.zero_lt_top
  · rw [hjeq]; exact (holderNorm_le_of_bd hα0 (hC w j hj t)).trans_lt ENNReal.ofReal_lt_top

/-! ### Properties of the time slices -/

lemma sc_add_nat (a b t : ℝ) (n : ℕ) : sc a b (t + n) = sc a b t := by
  unfold sc
  rw [mul_add, show 2 * π * (n : ℝ) = n * (2 * π) by ring, Real.sin_add_nat_mul_two_pi,
    Real.cos_add_nat_mul_two_pi]

lemma integral_sc_affine (a b z : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0 : ℝ)..1, sc a b (n * t - z) = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hn' : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  set F : ℝ → ℝ := fun t => sc (b / (2 * π)) (-(a / (2 * π))) (n * t - z) / n with hFdef
  have hF : ∀ t, HasDerivAt F (sc a b (n * t - z)) t := by
    intro t
    have h0 : HasDerivAt (sc (b / (2 * π)) (-(a / (2 * π)))) (sc a b (n * t - z)) (n * t - z) := by
      convert hasDerivAt_sc _ _ (n * t - z) using 2 <;> field_simp
    have h1 : HasDerivAt (fun t : ℝ => (n : ℝ) * t - z) ((n : ℝ) * 1) t :=
      ((hasDerivAt_id t).const_mul _).sub_const _
    have := (h0.comp t h1).div_const n
    simpa [hFdef, Function.comp_def, hn'] using this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    ((by unfold sc; fun_prop : Continuous fun t : ℝ => sc a b (n * t - z)).intervalIntegrable 0 1)]
  simp only [hFdef, mul_one, mul_zero, zero_sub]
  rw [show (n : ℝ) - z = -z + n by ring, sc_add_nat]
  ring

lemma integral_eField_affine (c : Fin 4 → ℝ) (n : ℕ) (hn : 1 ≤ n) (z : Pt 2) :
    ∫ x in cell 2, eField c ((n : ℝ) • x - z) = 0 := by
  have hint : Integrable (fun x => eField c ((n : ℝ) • x - z))
      ((volume : Measure (Pt 2)).restrict (cell 2)) :=
    ((contDiff_eField c).continuous.comp (by fun_prop)).integrableOn_Icc
  ext k
  rw [← ContinuousLinearMap.proj_apply (R := ℝ) k (∫ x in cell 2, eField c ((n : ℝ) • x - z)),
    ← ContinuousLinearMap.integral_comp_comm _ hint]
  simp only [ContinuousLinearMap.proj_apply, eField_eq, pair2, Pi.zero_apply]
  fin_cases k
  · simpa using integral_cell_coord (fun t => sc (c 0) (c 1) (n * t - z 1)) 1
      (integral_sc_affine _ _ _ n hn)
  · simpa using integral_cell_coord (fun t => sc (c 2) (c 3) (n * t - z 0)) 0
      (integral_sc_affine _ _ _ n hn)

lemma fpiece_props (w : Phase) (r j : ℕ) (t : ℝ) :
    IsPeriodic (fpiece w r j t) ∧ ContDiff ℝ ∞ (fpiece w r j t) ∧
    (∀ x, divergence (fpiece w r j t) x = 0) ∧ (∫ x in cell 2, fpiece w r j t x) = 0 := by
  set A := 1 / (kk j * δs j ^ (r + 2))
  set c := iteratedDeriv (r + 1) (cf₀.coef (w j).1) ((t - sj j) / δs j)
  have e : fpiece w r j t = fun x => A • eField c (((qq ^ j : ℕ) : ℝ) • x - (w j).2) := by
    funext x; simp [fpiece, kk, A, c]
  have ht := trigDrift_props (fun _ => c) contDiff_const A (qq ^ j) (w j).2
  have hq : 1 ≤ qq ^ j := Nat.one_le_pow _ _ (by have := qq_ge; omega)
  rw [e]
  have hsm : ContDiff ℝ ∞ (fun x : Pt 2 => A • eField c (((qq ^ j : ℕ) : ℝ) • x - (w j).2)) :=
    ((contDiff_eField c).comp ((contDiff_id.const_smul ((qq ^ j : ℕ) : ℝ)).sub
      contDiff_const)).const_smul A
  refine ⟨ht.1 0, hsm, ht.2.2 0, ?_⟩
  rw [integral_smul, integral_eField_affine c _ hq, smul_zero]

lemma gForce_slice_props (w : Phase) (t : ℝ) :
    IsPeriodic (gForce w t) ∧ ContDiff ℝ ∞ (gForce w t) ∧
    (∀ x, divergence (gForce w t) x = 0) ∧ (∫ x in cell 2, gForce w t x) = 0 := by
  rw [← forceD_zero_eq]
  rcases forceD_single w 0 t with h | ⟨j, -, -, h⟩
  · rw [h]
    exact ⟨fun _ _ => rfl, contDiff_const, fun x => by simp [divergence, pd], by simp⟩
  · rw [h]; exact fpiece_props w 0 j t

lemma gForce_support (w : Phase) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ ∀ t, t ∉ Icc a b → gForce w t = 0 := by
  have hδ := δs_pos 1 le_rfl
  have ha := cf₀.ha₀
  have hab := cf₀.hab₀
  have hb := cf₀.hb₀
  have h1 := sj_add_δs_le_Tstar 1 le_rfl
  rw [sj_one] at h1
  have hlt : δs 1 * cf₀.a₀ < δs 1 := by nlinarith
  refine ⟨δs 1 * cf₀.a₀, Tstar, by positivity, by linarith, accumulation_time.2, fun t ht => ?_⟩
  rw [← forceD_zero_eq]
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · refine forceD_eq_zero w 0 fun j hj => ?_
    rcases eq_or_lt_of_le hj with rfl | hj2
    · refine fpiece_eq_zero' w 0 fun hu => ?_
      rw [sj_one, sub_zero] at hu
      have := (le_div_iff₀ hδ).1 hu.1
      linarith
    · refine fpiece_eq_zero w 0 hj fun h => ?_
      have h2 := sj_mono (show 2 ≤ j by omega)
      have h3 := sj_succ 1 le_rfl
      rw [sj_one] at h3
      have := ηs_pos 1 le_rfl
      norm_num at h3
      linarith [h.1]
  · exact (forceD_local_gt w ht).self_of_nhds 0

/-- **Lemma 4.6** (regularity of the force).  For every `ω`, `g_ω` is real, mean zero,
divergence free, and belongs to `⋂_{0<α<1} C_c^∞((0,1); C^α_σ(𝕋²))`; on `I_j` the `r`-th time
derivative satisfies `‖∂ₜʳ g_ω(t)‖_{C^α} ≤ C k_j^{α-1} δ_j^{-r-2}` uniformly in `ω`. -/
theorem force_regularity :
    (∀ w : Phase, IsAdmissibleForce (gForce w) ∧ ∀ t, (∫ x in cell 2, gForce w t x) = 0) ∧
    ∀ (r : ℕ) (α : ℝ), 0 < α → α < 1 → ∃ C : ℝ, ∀ (w : Phase) (j : ℕ), 1 ≤ j → ∀ t ∈ Ij j,
      holderNorm α (fun x => (1 / (kk j * δs j ^ (r + 2))) •
          eField (iteratedDeriv (r + 1) (cf₀.coef (w j).1) ((t - sj j) / δs j))
            (kk j • x - (w j).2))
        ≤ ENNReal.ofReal (C * kk j ^ (α - 1) * δs j ^ (-(r : ℝ) - 2)) := by
  refine ⟨fun w => ⟨⟨⟨fun t => (gForce_slice_props w t).1, fun t => (gForce_slice_props w t).2.1,
    fun t => (gForce_slice_props w t).2.2.1, fun α hα0 hα1 =>
      ⟨forceD w, forceD_zero_eq w, forceD_finite hα0 hα1 w, forceD_deriv hα0 hα1 w⟩⟩,
    gForce_support w⟩, fun t => (gForce_slice_props w t).2.2.2⟩, fun r α hα0 hα1 => ?_⟩
  obtain ⟨C, -, hC⟩ := fpiece_bound hα0.le hα1.le r
  exact ⟨2 * C, fun w j hj t _ => (holderNorm_le_of_bd hα0 (hC w j hj t)).trans_eq
    (by ring_nf)⟩

end AnomDiss
