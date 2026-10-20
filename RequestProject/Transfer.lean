module

public import RequestProject.Comparison

/-!
# Section 5: diagonal velocity error and transfer

Lemma 5.7 (the comparison drift is close to the true horizontal velocity in `L²`) and
Proposition 5.8 (transfer of the dissipation from the comparison scalar to the true scalar).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss


lemma Vpulse_start_zero {ν : ℝ} (hν : 0 < ν) (w : Phase) {j : ℕ} (hj : 1 ≤ j) :
    Vpulse ν w j (sj j) = 0 := by
  obtain ⟨C, hC⟩ := isolated_pulse_properties
  exact (hC ν hν j hj w).2.2.1

lemma vbar_on_Ij (ν : ℝ) (w : Phase) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ Ij j) :
    vbar ν w t = Vpulse ν w j t := by
  funext x
  unfold vbar
  rw [tsum_eq_single j fun j' hj' => by
    rw [if_neg fun h => hj' (Ij_unique h.1 hj h.2 ht)]]
  rw [if_pos ⟨hj, ht⟩]

open Classical in
lemma vbar_on_gap {ν : ℝ} (hν : 0 < ν) (w : Phase) {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (ht : t ∈ Ioc (sj j + δs j) (sj (j + 1))) : vbar ν w t = 0 := by
  funext x
  unfold vbar
  have hterm : ∀ i : ℕ, (if 1 ≤ i ∧ t ∈ Ij i then Vpulse ν w i t x else 0) = 0 := by
    intro i
    split_ifs with h
    · obtain ⟨hi, hti⟩ := h
      rcases lt_trichotomy i (j + 1) with hlt | heq | hgt
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | rfl
        · have h1 := sj_lt_succ i hi
          have h2 := sj_mono (show i + 1 ≤ j by omega)
          linarith [hti.2, ht.1, δs_pos j hj]
        · linarith [hti.2, ht.1]
      · subst heq
        have : t = sj (j + 1) := le_antisymm ht.2 hti.1
        rw [this, Vpulse_start_zero hν w hi]
        rfl
      · have h1 := sj_lt_succ (j + 1) (by omega)
        have h2 := sj_mono (show j + 1 + 1 ≤ i by omega)
        linarith [hti.1, ht.2, δs_pos (j + 1) (by omega)]
    · rfl
  simp only [hterm, tsum_zero, Pi.zero_apply]

lemma l2sqV_nonneg' (u : Pt 2 → Pt 2) : 0 ≤ l2sqV u :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma l2sqV_eq_l2V_sq (u : Pt 2 → Pt 2) : l2sqV u = l2V u ^ 2 := by
  rw [l2V, Real.sq_sqrt (l2sqV_nonneg' u)]

/-- The kinetic energy at the end of the pulse interval. -/
lemma l2V_pulse_end_le (ν : ℝ) (hν : 0 < ν) (w : Phase) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ) (hv : IsClassicalNS 1 ν 0 (gForce w) v p) (j : ℕ) (hj : 1 ≤ j) :
    l2V (v (sj j + δs j)) ≤ Real.exp Λ₀ * l2V (v (sj j)) + l2V (Vpulse ν w j (sj j + δs j)) := by
  obtain ⟨β, -, -, reg, -⟩ := hv.regular
  have hδ := δs_pos j hj
  have hmem : sj j + δs j ∈ Ij j := ⟨by linarith, le_rfl⟩
  have hvb : Continuous (v (sj j + δs j)) :=
    (reg.smooth_x _ (Ij_subset_unit hj hmem)).continuous
  have hV := (Vpulse_slice_C2 ν w j (sj j + δs j)).continuous
  have htri := sqrt_l2sqV_add_le (fun x => v (sj j + δs j) x - Vpulse ν w j (sj j + δs j) x)
    (Vpulse ν w j (sj j + δs j)) (hvb.sub hV) hV
  simp only [sub_add_cancel] at htri
  have hp1 := (single_stage_stability ν hν w v p hv j hj).1 _ hmem
  unfold l2V at hp1 ⊢
  calc Real.sqrt (l2sqV (v (sj j + δs j)))
      ≤ Real.sqrt (l2sqV fun x => v (sj j + δs j) x - Vpulse ν w j (sj j + δs j) x) +
        Real.sqrt (l2sqV (Vpulse ν w j (sj j + δs j))) := htri
    _ ≤ _ := by gcongr; exact hp1

/-- On each stage `(s_j, s_{j+1}]`, `‖v - v̄‖₂ ≤ e^Λ E_j + r_j`. -/
lemma stage_error_le (ν : ℝ) (hν : 0 < ν) (w : Phase) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ) (hv : IsClassicalNS 1 ν 0 (gForce w) v p) (j : ℕ) (hj : 1 ≤ j)
    (t : ℝ) (ht : t ∈ Ioc (sj j) (sj (j + 1))) :
    l2sqV (v t - vbar ν w t) ≤
      (Real.exp Λ₀ * l2V (v (sj j)) + l2V (Vpulse ν w j (sj j + δs j))) ^ 2 := by
  have hE : 0 ≤ Real.exp Λ₀ * l2V (v (sj j)) := by
    have := Real.sqrt_nonneg (l2sqV (v (sj j))); unfold l2V; positivity
  have hr : 0 ≤ l2V (Vpulse ν w j (sj j + δs j)) := Real.sqrt_nonneg _
  rcases le_or_gt t (sj j + δs j) with h | h
  · have hmem : t ∈ Ij j := ⟨ht.1.le, h⟩
    rw [vbar_on_Ij ν w hj hmem, l2sqV_eq_l2V_sq]
    have h1 := (single_stage_stability ν hν w v p hv j hj).1 t hmem
    have h0 : 0 ≤ l2V (v t - Vpulse ν w j t) := Real.sqrt_nonneg _
    nlinarith
  · rw [vbar_on_gap hν w hj ⟨h, ht.2⟩, sub_zero]
    have h1 := quiet_energy_le ν hν w v p hv j hj t ⟨h.le, ht.2⟩
    have h2 := l2V_pulse_end_le ν hν w v p hv j hj
    rw [l2sqV_eq_l2V_sq (v (sj j + δs j))] at h1
    have h0 : 0 ≤ l2V (v (sj j + δs j)) := Real.sqrt_nonneg _
    nlinarith


lemma Apulse_pred_le (ν : ℝ) (hν : 0 < ν) {j : ℕ} (hj : 2 ≤ j) :
    Apulse ν (j - 1) ≤ 2 ^ (3 * M₀) * Apulse ν j := by
  have h := Apulse_shift ν hν (j - 1) 1 (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
  have hq : (1 : ℝ) ≤ ((qq : ℝ) ^ (2 * M₀ + 1)) ^ 1 := by
    have := qq_ge
    rw [pow_one]; exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ qq))
  have hA := (Apulse_pos ν hν (j - 1) (by omega)).le
  norm_num at h
  nlinarith

/-- A uniform bound `e^Λ E_j + r_j ≤ K A_j`. -/
lemma stage_const : ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℝ, 0 < ν → ∀ (w : Phase) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ), IsClassicalNS 1 ν 0 (gForce w) v p → ∀ j : ℕ, 1 ≤ j →
    Real.exp Λ₀ * l2V (v (sj j)) + l2V (Vpulse ν w j (sj j + δs j)) ≤ K * Apulse ν j := by
  obtain ⟨CR, hCR⟩ := global_reset
  obtain ⟨C1, hC1⟩ := isolated_pulse_properties
  set CR' := max CR 0
  set C1' := max C1 0
  refine ⟨Real.exp Λ₀ * CR' * 2 ^ (3 * M₀) + C1', by positivity, fun ν hν w v p hv j hj => ?_⟩
  have hAj := (Apulse_pos ν hν j hj).le
  have hr : l2V (Vpulse ν w j (sj j + δs j)) ≤ C1' * Apulse ν j :=
    (hC1 ν hν j hj w).2.2.2.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hAj)
  have hE : l2V (v (sj j)) ≤ CR' * 2 ^ (3 * M₀) * Apulse ν j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · obtain rfl : j = 1 := by omega
      rw [show sj 1 = 0 by simp [sj], hv.init]
      have : l2V (0 : Pt 2 → Pt 2) = 0 := by simp [l2V, l2sqV]
      rw [this]; positivity
    · have h1 := hCR ν hν w v p hv (j - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h1
      have h2 := Apulse_pred_le ν hν h
      have hA1 := (Apulse_pos ν hν (j - 1) (by omega)).le
      calc l2V (v (sj j)) ≤ CR * Apulse ν (j - 1) := h1
        _ ≤ CR' * Apulse ν (j - 1) := mul_le_mul_of_nonneg_right (le_max_left _ _) hA1
        _ ≤ CR' * (2 ^ (3 * M₀) * Apulse ν j) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
        _ = _ := by ring
  have he := (Real.exp_pos Λ₀).le
  calc Real.exp Λ₀ * l2V (v (sj j)) + l2V (Vpulse ν w j (sj j + δs j))
      ≤ Real.exp Λ₀ * (CR' * 2 ^ (3 * M₀) * Apulse ν j) + C1' * Apulse ν j := by gcongr
    _ = _ := by ring

/-- The ratio `q^{-(4M+2)}`. -/
def diagRatio : ℝ := (((qq : ℝ) ^ (2 * M₀ + 1)) ^ 2)⁻¹

lemma diagRatio_pos : 0 < diagRatio := by unfold diagRatio; have := qq_ge; positivity

lemma diagRatio_lt_one : diagRatio < 1 := by
  unfold diagRatio
  have hq : (1 : ℝ) < (qq : ℝ) := by have := qq_ge; exact_mod_cast (by omega : 1 < qq)
  apply inv_lt_one_of_one_lt₀
  exact one_lt_pow₀ (one_lt_pow₀ hq (by omega)) (by norm_num)

lemma summable_diag :
    Summable fun a : ℕ => ((1 : ℝ) + a) ^ (6 * M₀ + 2) * diagRatio ^ a := by
  have hr := diagRatio_pos
  have h := summable_pow_mul_geometric_of_norm_lt_one (6 * M₀ + 2)
    (show ‖diagRatio‖ < 1 by rw [Real.norm_of_nonneg hr.le]; exact diagRatio_lt_one)
  have h' := ((summable_nat_add_iff 1).2 h).mul_left diagRatio⁻¹
  refine h'.congr fun a => ?_
  push_cast
  rw [pow_succ]; field_simp; ring

lemma stage_term_le (ν : ℝ) (hν : 0 < ν) (N a : ℕ) (ha : a < N) :
    (δs (N - a) + ηs (N - a)) * Apulse ν (N - a) ^ 2 ≤
      2 * (((1 : ℝ) + a) ^ (6 * M₀ + 2) * diagRatio ^ a) * (Apulse ν N ^ 2 * ηs N) := by
  set j := N - a with hjdef
  have hj : 1 ≤ j := by omega
  have hN : N = j + a := by omega
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hτ : (0 : ℝ) < τstar := by unfold τstar; norm_num
  -- the time step
  have hδη : δs j ≤ ηs j := by
    unfold δs ηs
    apply div_le_div_of_nonneg_left hτ.le (by positivity)
    nlinarith [pow_le_pow_right₀ hjr (show 2 ≤ 3 by norm_num)]
  have hη : ηs j ≤ ((1 : ℝ) + a) ^ 2 * ηs N := by
    unfold ηs
    rw [hN]; push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((j : ℝ) + a) ≤ (1 + a) * j := by nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    have h0 : (0 : ℝ) ≤ (j : ℝ) + a := by positivity
    have := mul_le_mul this this h0 (by positivity)
    nlinarith
  -- the amplitude
  have hA := Apulse_shift ν hν j a hj
  rw [← hN] at hA
  have hQ : (0 : ℝ) < ((qq : ℝ) ^ (2 * M₀ + 1)) ^ a := by have := qq_ge; positivity
  have hAj := (Apulse_pos ν hν j hj).le
  have hA' : Apulse ν j ≤ ((1 : ℝ) + a) ^ (3 * M₀) * Apulse ν N / ((qq : ℝ) ^ (2 * M₀ + 1)) ^ a := by
    rw [le_div_iff₀ hQ]; exact hA
  have hA2 : Apulse ν j ^ 2 ≤ ((1 : ℝ) + a) ^ (6 * M₀) * diagRatio ^ a * Apulse ν N ^ 2 := by
    have := pow_le_pow_left₀ hAj hA' 2
    refine this.trans (le_of_eq ?_)
    unfold diagRatio
    rw [div_pow, mul_pow, ← pow_mul, inv_pow, ← pow_mul, ← pow_mul]
    field_simp
    ring
  have hηN : 0 ≤ ηs N := by unfold ηs; positivity
  have hd : 0 ≤ diagRatio := diagRatio_pos.le
  calc (δs j + ηs j) * Apulse ν j ^ 2 ≤ (2 * (((1 : ℝ) + a) ^ 2 * ηs N)) *
        (((1 : ℝ) + a) ^ (6 * M₀) * diagRatio ^ a * Apulse ν N ^ 2) := by
        gcongr
        · linarith
    _ = _ := by ring


lemma integral_le_stage_sum (N : ℕ) (c : ℕ → ℝ) (F : ℝ → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hF : ∀ j, 1 ≤ j → j ≤ N → ∀ t ∈ Ioc (sj j) (sj (j + 1)), F t ≤ c j) :
    ∫ t in (0 : ℝ)..TN N, F t ≤ ∑ j ∈ Finset.Ico 1 (N + 1), (sj (j + 1) - sj j) * c j := by
  have hlen : ∀ j, 0 ≤ sj (j + 1) - sj j := fun j => sub_nonneg.2 (sj_mono (Nat.le_succ j))
  have hRHS : 0 ≤ ∑ j ∈ Finset.Ico 1 (N + 1), (sj (j + 1) - sj j) * c j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hlen j) (hc j)
  by_cases hint : IntervalIntegrable F volume 0 (TN N)
  swap
  · rw [intervalIntegral.integral_undef hint]; exact hRHS
  have h0 : (0 : ℝ) = sj 1 := by simp [sj]
  have hpiece : ∀ k < N, IntervalIntegrable F volume (sj (k + 1)) (sj (k + 1 + 1)) := by
    intro k hk
    refine hint.mono_set ?_
    rw [uIcc_of_le (sj_mono (by omega)), uIcc_of_le (TN_bounds N).1]
    exact Icc_subset_Icc ((sj_bounds _).1) (sj_mono (by omega))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => sj (k + 1))
    (n := N) (μ := volume) (f := F) hpiece
  rw [show TN N = sj (N + 1) from rfl, h0, ← hsum, Finset.sum_Ico_eq_sum_range,
    show N + 1 - 1 = N by omega]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hle : sj (k + 1) ≤ sj (k + 1 + 1) := sj_mono (by omega)
  rw [intervalIntegral.integral_of_le hle, add_comm 1 k]
  calc ∫ t in Ioc (sj (k + 1)) (sj (k + 1 + 1)), F t
      ≤ ∫ t in Ioc (sj (k + 1)) (sj (k + 1 + 1)), c (k + 1) := by
        refine setIntegral_mono_on ((hpiece k hk').1) (integrableOn_const (by simp))
          measurableSet_Ioc fun t ht => hF (k + 1) (by omega) (by omega) t ht
    _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hle, smul_eq_mul]


lemma diag_scaling (N : ℕ) (hN : 1 ≤ N) :
    (1 / nuN N) * (Apulse (nuN N) N ^ 2 * ηs N) =
      1 / ((4 * π ^ 2) ^ (2 * M₀ + 1) * (N : ℝ) ^ (2 * M₀)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ : (0 : ℝ) < τstar := by unfold τstar; norm_num
  have hk := kk_pos' N
  have hη : 0 < ηs N := by unfold ηs; positivity
  have hδ : δs N = ηs N * (1 / N) := by unfold δs ηs; field_simp
  have hν : 0 < nuN N := by unfold nuN; positivity
  have h1 : nuN N * (kk N ^ 2 * ηs N) = 1 / (4 * π ^ 2) := by
    unfold nuN; field_simp
  unfold Apulse
  rw [hδ]
  calc 1 / nuN N * ((nuN N ^ (M₀ + 1) * kk N ^ (2 * M₀ + 1) * (ηs N * (1 / N)) ^ M₀) ^ 2 * ηs N)
      = (1 / nuN N * nuN N) * ((nuN N * (kk N ^ 2 * ηs N)) ^ (2 * M₀ + 1) *
          (1 / (N : ℝ)) ^ (2 * M₀)) := by ring
    _ = _ := by
        rw [h1, one_div_mul_cancel hν.ne', one_mul, div_pow, div_pow, one_pow, one_pow,
          div_mul_div_comm, one_mul]


lemma stage_sum_le (ν : ℝ) (hν : 0 < ν) (N : ℕ) (K : ℝ) :
    ∑ j ∈ Finset.Ico 1 (N + 1), (sj (j + 1) - sj j) * (K * Apulse ν j) ^ 2 ≤
      K ^ 2 * (2 * ∑' a : ℕ, ((1 : ℝ) + a) ^ (6 * M₀ + 2) * diagRatio ^ a) *
        (Apulse ν N ^ 2 * ηs N) := by
  set g : ℕ → ℝ := fun a => ((1 : ℝ) + a) ^ (6 * M₀ + 2) * diagRatio ^ a with hg
  have hg0 : ∀ a, 0 ≤ g a := fun a => by have := diagRatio_pos; positivity
  have hX : 0 ≤ Apulse ν N ^ 2 * ηs N := by
    have : 0 ≤ ηs N := by unfold ηs τstar; positivity
    positivity
  rw [Finset.sum_Ico_eq_sum_range, show N + 1 - 1 = N by omega, ← Finset.sum_range_reflect]
  calc ∑ k ∈ Finset.range N, (sj (1 + (N - 1 - k) + 1) - sj (1 + (N - 1 - k))) *
        (K * Apulse ν (1 + (N - 1 - k))) ^ 2
      ≤ ∑ k ∈ Finset.range N, K ^ 2 * (2 * g k * (Apulse ν N ^ 2 * ηs N)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        rw [show 1 + (N - 1 - k) = N - k by omega, sj_succ (N - k) (by omega)]
        have := stage_term_le ν hν N k hk'
        calc (sj (N - k) + δs (N - k) + ηs (N - k) - sj (N - k)) * (K * Apulse ν (N - k)) ^ 2
            = K ^ 2 * ((δs (N - k) + ηs (N - k)) * Apulse ν (N - k) ^ 2) := by ring
          _ ≤ K ^ 2 * (2 * g k * (Apulse ν N ^ 2 * ηs N)) := by gcongr
    _ = K ^ 2 * (2 * (∑ k ∈ Finset.range N, g k)) * (Apulse ν N ^ 2 * ηs N) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ _ := by
        gcongr
        exact summable_diag.sum_le_tsum _ fun a _ => hg0 a

/-- **Lemma 5.7** (diagonal velocity error).
`ν_N⁻¹ ∫₀^{T_N}‖v_ω^{ν_N} - v̄_ω^{ν_N}‖₂² dt ≤ C_M N^{-2M}` for all large `N`. -/
theorem diagonal_velocity_error : ∃ (C : ℝ) (N' : ℕ), ∀ N : ℕ, N' ≤ N → ∀ (w : Phase)
    (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ), IsClassicalNS 1 (nuN N) 0 (gForce w) v p →
    (1 / nuN N) * ∫ t in (0 : ℝ)..TN N, l2sqV (v t - vbar (nuN N) w t)
      ≤ C * (N : ℝ) ^ (-(2 * (M₀ : ℝ))) := by
  obtain ⟨K, hK0, hK⟩ := stage_const
  set S2 := ∑' a : ℕ, ((1 : ℝ) + a) ^ (6 * M₀ + 2) * diagRatio ^ a with hS2
  refine ⟨K ^ 2 * (2 * S2) / (4 * π ^ 2) ^ (2 * M₀ + 1), 1, fun N hN w v p hv => ?_⟩
  have hν := viscosity_properties.2.2.1 N hN
  have hint := integral_le_stage_sum N (fun j => (K * Apulse (nuN N) j) ^ 2)
    (fun t => l2sqV (v t - vbar (nuN N) w t)) (fun j => sq_nonneg _)
    (fun j hj _ t ht => by
      have h1 := stage_error_le (nuN N) hν w v p hv j hj t ht
      have h2 := hK (nuN N) hν w v p hv j hj
      have h0 : 0 ≤ Real.exp Λ₀ * l2V (v (sj j)) + l2V (Vpulse (nuN N) w j (sj j + δs j)) := by
        have := Real.sqrt_nonneg (l2sqV (v (sj j)))
        have := Real.sqrt_nonneg (l2sqV (Vpulse (nuN N) w j (sj j + δs j)))
        unfold l2V; positivity
      exact h1.trans (pow_le_pow_left₀ h0 h2 2))
  have hsum := stage_sum_le (nuN N) hν N K
  have hscale := diag_scaling N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrpow : (N : ℝ) ^ (-(2 * (M₀ : ℝ))) = 1 / (N : ℝ) ^ (2 * M₀) := by
    rw [Real.rpow_neg hNr.le, one_div, show (2 * (M₀ : ℝ)) = ((2 * M₀ : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hinv : 0 ≤ 1 / nuN N := by positivity
  calc 1 / nuN N * ∫ t in (0 : ℝ)..TN N, l2sqV (v t - vbar (nuN N) w t)
      ≤ 1 / nuN N * (K ^ 2 * (2 * S2) * (Apulse (nuN N) N ^ 2 * ηs N)) :=
        mul_le_mul_of_nonneg_left (hint.trans hsum) hinv
    _ = K ^ 2 * (2 * S2) * (1 / nuN N * (Apulse (nuN N) N ^ 2 * ηs N)) := by ring
    _ = _ := by
        rw [hscale, hrpow]
        field_simp


/-- One stage of the transfer estimate: on `[a, a+T]`, the difference between the true scalar
`θ` (drift `v`) and a stage solution `φ` (drift `D`, local time) grows in `L²` at most by
`(M²/(2ν)) ∫ ‖v - D‖₂²`. -/
lemma stage_transfer {a T ν M : ℝ} (ha : 0 ≤ a) (hT : 0 < T) (haT : a + T ≤ 1) (hν : 0 < ν)
    (v : ℝ → Pt 2 → Pt 2) (hvc : ContinuousOn (fun q : ℝ × Pt 2 => v q.1 q.2) (Icc 0 1 ×ˢ univ))
    (hvreg : ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ 1 (v s) ∧ IsPeriodic (v s) ∧
      ∀ x, divergence (v s) x = 0)
    (D : ℝ → Pt 2 → Pt 2) (hDc : ContinuousOn (fun q : ℝ × Pt 2 => D q.1 q.2) (Icc 0 T ×ˢ univ))
    (hDreg : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (D t) ∧ IsPeriodic (D t) ∧
      ∀ x, divergence (D t) x = 0)
    (θ₀ : Pt 2 → ℝ) (θ : ℝ → Pt 2 → ℝ) (hθ : IsClassicalScalar 1 ν v θ₀ θ)
    (hθM : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |θ t x| ≤ M)
    (φ₀ : Pt 2 → ℝ) (φ : ℝ → Pt 2 → ℝ) (hφ : IsClassicalScalar T ν D φ₀ φ) :
    l2sq (fun x => θ (a + T) x - φ T x) ≤ l2sq (fun x => θ a x - φ 0 x) +
      M ^ 2 / (2 * ν) * ∫ s in a..a + T, l2sqV (fun x => v s x - D (s - a) x) := by
  obtain ⟨β, hβ0, -, reg⟩ := hθ.regular
  obtain ⟨β', hβ0', -, regφ⟩ := hφ.regular
  have hab : a ≤ a + T := by linarith
  have hsub : Icc a (a + T) ⊆ Icc 0 1 := Icc_subset_Icc ha haT
  have hshift : ∀ s ∈ Icc a (a + T), s - a ∈ Icc 0 T := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmaps : MapsTo (fun q : ℝ × Pt 2 => (q.1 - a, q.2)) (Icc a (a + T) ×ˢ univ)
      (Icc 0 T ×ˢ univ) := fun q hq => ⟨hshift q.1 hq.1, mem_univ _⟩
  have hcshift : Continuous (fun q : ℝ × Pt 2 => (q.1 - a, q.2)) := by fun_prop
  have hcomp : ∀ {G : ℝ → Pt 2 → ℝ}, ContinuousOn (fun q : ℝ × Pt 2 => G q.1 q.2) (Icc 0 T ×ˢ univ) →
      ContinuousOn (fun q : ℝ × Pt 2 => G (q.1 - a) q.2) (Icc a (a + T) ×ˢ univ) :=
    fun hG => hG.comp hcshift.continuousOn hmaps
  set z : ℝ → Pt 2 → ℝ := fun s x => θ s x - φ (s - a) x with hz
  set z' : ℝ → Pt 2 → ℝ := fun s x => dt 1 θ s x - dt T φ (s - a) x with hz'
  have hzc : ContinuousOn (fun q : ℝ × Pt 2 => z q.1 q.2) (Icc a (a + T) ×ˢ univ) :=
    (reg.continuousOn.mono (prod_mono hsub subset_rfl)).sub (hcomp regφ.continuousOn)
  have hz'c : ContinuousOn (fun q : ℝ × Pt 2 => z' q.1 q.2) (Icc a (a + T) ×ˢ univ) :=
    ((reg.holder_dt.continuousOn hβ0).mono (prod_mono hsub subset_rfl)).sub
      (hcomp (regφ.holder_dt.continuousOn hβ0'))
  have hd : ∀ s ∈ Ioo a (a + T), ∀ x, HasDerivAt (fun r => z r x) (z' s x) s := by
    intro s hs x
    have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt hs.1, hs.2.trans_le haT⟩
    have h1 : HasDerivAt (fun r => θ r x) (dt 1 θ s x) s :=
      (reg.diff_t x s (Ioo_subset_Icc_self hs01)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs01.1 hs01.2)
    have hsT : s - a ∈ Ioo 0 T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 : HasDerivAt (fun r => φ r x) (dt T φ (s - a) x) (s - a) :=
      (regφ.diff_t x (s - a) (Ioo_subset_Icc_self hsT)).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hsT.1 hsT.2)
    exact h1.sub (h2.comp_sub_const s a)
  obtain ⟨hform, hcont⟩ := l2sq_integral_form hab z z' hzc hz'c hd
  -- the energy rate is controlled by the velocity difference
  set g : ℝ → ℝ := fun s => l2sqV (fun x => v s x - D (s - a) x) with hg
  have hgc : ContinuousOn g (Icc a (a + T)) := by
    refine continuousOn_integral_cell' hab _ ?_
    refine continuousOn_finset_sum _ fun k _ => ?_
    exact ((continuous_apply k).comp_continuousOn
      ((hvc.mono (prod_mono hsub subset_rfl)).sub (hDc.comp hcshift.continuousOn hmaps))).pow 2
  have hle : ∀ s ∈ Icc a (a + T), ∫ x in cell 2, 2 * z s x * z' s x ≤ M ^ 2 / (2 * ν) * g s := by
    intro s hs
    have hs1 := hsub hs
    have hsT := hshift s hs
    obtain ⟨hv1, hvp, hvdiv⟩ := hvreg s hs1
    obtain ⟨hD1, hDp, hDdiv⟩ := hDreg (s - a) hsT
    have hθs := reg.smooth_x s hs1
    have hφs := regφ.smooth_x (s - a) hsT
    refine scalar_diff_energy_le ν M hν (D (s - a)) (fun x => v s x - D (s - a) x) (θ s) (z s)
      (z' s) hD1 hDp hDdiv (hv1.sub hD1) (fun x n => by simp only [hvp x n, hDp x n])
      (fun x => by
        rw [divergence_sub_fun _ _ (hv1.differentiable one_ne_zero)
          (hD1.differentiable one_ne_zero), hvdiv, hDdiv, sub_zero])
      (hθs.of_le (by norm_num)) (hθ.periodic s hs1) (hθM s hs1) (hθs.sub hφs)
      (fun x n => by simp only [hz, hθ.periodic s hs1 x n, hφ.periodic (s - a) hsT x n])
      (fun x => ?_)
    have h1 := hθ.eqn s hs1 x
    have h2 := hφ.eqn (s - a) hsT x
    simp only [smul_eq_mul] at h1 h2
    simp only [hz, hz']
    rw [conv_sub_right _ _ _ (hθs.differentiable (by norm_num)) (hφs.differentiable (by norm_num)),
      conv_sub_left, lap_sub_fun _ _ hθs hφs]
    linear_combination h1 - h2
  have hfin := hform (a + T) ⟨hab, le_rfl⟩
  have hint : ∫ s in a..a + T, ∫ x in cell 2, 2 * z s x * z' s x ≤
      ∫ s in a..a + T, M ^ 2 / (2 * ν) * g s :=
    intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable_of_Icc hab)
      ((continuousOn_const.mul hgc).intervalIntegrable_of_Icc hab) hle
  rw [intervalIntegral.integral_const_mul] at hint
  have e0 : z a = fun x => θ a x - φ 0 x := by funext x; simp [hz]
  have e1 : z (a + T) = fun x => θ (a + T) x - φ T x := by funext x; simp [hz]
  rw [e0, e1] at hfin
  linarith

lemma intervalIntegrable_of_eqOn_Ioc {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (h : EqOn f g (Ioc a b)) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact ((hg.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self).congr_fun
    h.symm measurableSet_Ioc

lemma integral_eq_of_eqOn_Ioc {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioc a b)) :
    ∫ s in a..b, f s = ∫ s in a..b, g s := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact setIntegral_congr_fun measurableSet_Ioc h

/-- Chaining the stage estimates: the `L²` distance between the true scalar and the comparison
scalar at `s_j` is controlled by `(M²/(2ν)) ∫₀^{s_j} ‖v - v̄‖₂²`. -/
lemma transfer_chain {N : ℕ} (hN : 1 ≤ N) (w : Phase) (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ)
    (hv : IsClassicalNS 1 (nuN N) 0 (gForce w) v p) (θ₀ : Pt 2 → ℝ) (θ : ℝ → Pt 2 → ℝ)
    (hθ : IsClassicalScalar 1 (nuN N) v θ₀ θ) {M : ℝ} (hM : ∀ x, |θ₀ x| ≤ M)
    (θb : ℝ → Pt 2 → ℝ) (hθb : IsComparisonScalar N w θ₀ θb) :
    ∀ j, 1 ≤ j → j ≤ N + 1 →
      IntervalIntegrable (fun s => l2sqV (v s - vbar (nuN N) w s)) volume 0 (sj j) ∧
      l2sq (fun x => θ (sj j) x - θb (sj j) x) ≤
        M ^ 2 / (2 * nuN N) * ∫ s in (0 : ℝ)..sj j, l2sqV (v s - vbar (nuN N) w s) := by
  have hν := viscosity_properties.2.2.1 N hN
  obtain ⟨β, -, -, reg, -⟩ := hv.regular
  have hvc := reg.continuousOn
  have hvreg : ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ 1 (v s) ∧ IsPeriodic (v s) ∧
      ∀ x, divergence (v s) x = 0 := fun s hs =>
    ⟨(reg.smooth_x s hs).of_le (by norm_num), hv.periodic_u s hs, hv.div_free s hs⟩
  have hθM : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |θ t x| ≤ M :=
    hθ.abs_le hν.le hM
  set F : ℝ → ℝ := fun s => l2sqV (v s - vbar (nuN N) w s) with hF
  set c := M ^ 2 / (2 * nuN N)
  have hc : 0 ≤ c := by positivity
  intro j hj hjN
  induction j, hj using Nat.le_induction with
  | base =>
    rw [sj_one]
    refine ⟨IntervalIntegrable.refl, ?_⟩
    rw [intervalIntegral.integral_same, mul_zero, hθb.1, ← hθ.init]
    simp [l2sq]
  | succ j hj ih =>
    obtain ⟨hint, hZ⟩ := ih (by omega)
    obtain ⟨hI, hJ⟩ := hθb.2 j hj (by omega)
    have hδ := δs_pos j hj
    have hη := ηs_pos j hj
    have hsj0 := (sj_bounds j).1
    have hend : sj j + δs j + ηs j ≤ 1 := by
      rw [← sj_succ j hj]; exact (sj_succ_lt_one j).le
    have hjs : sj (j + 1) = sj j + δs j + ηs j := sj_succ j hj
    -- the pulse stage
    have hSI := stage_transfer (a := sj j) (T := δs j) hsj0 hδ (by linarith) hν v hvc hvreg
      (fun t => Vpulse (nuN N) w j (sj j + t))
      (vpulse_stage_props (nuN N) w j).2.1.continuous.continuousOn
      (fun t _ => ⟨(Vpulse_slice_C2 _ w j _).of_le (by norm_num),
        (vpulse_stage_props (nuN N) w j).1 t, (vpulse_stage_props (nuN N) w j).2.2 t⟩)
      θ₀ θ hθ hθM _ _ hI
    -- the quiet stage
    have hSJ := stage_transfer (a := sj j + δs j) (T := ηs j) (by linarith) hη hend hν v hvc hvreg
      (fun _ _ => 0) continuousOn_const
      (fun t _ => ⟨contDiff_const, fun _ _ => rfl, fun x => by simp [divergence, pd]⟩)
      θ₀ θ hθ hθM _ _ hJ
    simp only [add_zero, add_sub_cancel, sub_zero] at hSI hSJ
    -- identify the stage integrands with `‖v - v̄‖₂²`
    have hcI : ContinuousOn (fun s => l2sqV (fun x => v s x - Vpulse (nuN N) w j s x))
        (Icc (sj j) (sj j + δs j)) := by
      refine continuousOn_integral_cell' (by linarith) _ ?_
      refine continuousOn_finset_sum _ fun k _ => ?_
      exact ((continuous_apply k).comp_continuousOn ((hvc.mono (prod_mono
        (Ij_subset_unit hj) subset_rfl)).sub (Vpulse_props (nuN N) w j).2.1.continuous.continuousOn)).pow 2
    have hJsub : Icc (sj j + δs j) (sj j + δs j + ηs j) ⊆ Icc 0 1 :=
      Icc_subset_Icc (by linarith) hend
    have hcJ : ContinuousOn (fun s => l2sqV (fun x => v s x))
        (Icc (sj j + δs j) (sj j + δs j + ηs j)) := by
      refine continuousOn_integral_cell' (by linarith) _ ?_
      refine continuousOn_finset_sum _ fun k _ => ?_
      exact ((continuous_apply k).comp_continuousOn (hvc.mono (prod_mono hJsub subset_rfl))).pow 2
    have eqI : EqOn F (fun s => l2sqV (fun x => v s x - Vpulse (nuN N) w j s x))
        (Ioc (sj j) (sj j + δs j)) := fun s hs => by
      simp only [hF, vbar_on_Ij (nuN N) w hj (Ioc_subset_Icc_self hs)]; rfl
    have eqJ : EqOn F (fun s => l2sqV (fun x => v s x)) (Ioc (sj j + δs j) (sj j + δs j + ηs j)) :=
      fun s hs => by
        simp only [hF, vbar_on_gap hν w hj (by rw [hjs]; exact hs), sub_zero]
    have iI := intervalIntegrable_of_eqOn_Ioc (by linarith) hcI eqI
    have iJ := intervalIntegrable_of_eqOn_Ioc (by linarith) hcJ eqJ
    have hsplit : ∫ s in (0 : ℝ)..sj (j + 1), F s = (∫ s in (0 : ℝ)..sj j, F s) +
        (∫ s in sj j..sj j + δs j, F s) + ∫ s in sj j + δs j..sj j + δs j + ηs j, F s := by
      rw [hjs, intervalIntegral.integral_add_adjacent_intervals hint iI,
        intervalIntegral.integral_add_adjacent_intervals (hint.trans iI) iJ]
    refine ⟨by rw [hjs]; exact (hint.trans iI).trans iJ, ?_⟩
    rw [hsplit, integral_eq_of_eqOn_Ioc (by linarith) eqI, integral_eq_of_eqOn_Ioc (by linarith) eqJ,
      hjs]
    nlinarith


lemma dissipation_nonneg' (ν : ℝ) (hν : 0 ≤ ν) (θ : ℝ → Pt 2 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ dissipation ν θ t := by
  unfold dissipation
  refine mul_nonneg hν (intervalIntegral.integral_nonneg ht (fun s _ => ?_))
  refine setIntegral_nonneg measurableSet_Icc (fun x _ => ?_)
  unfold gradSq; positivity

lemma l2sq_nonneg' (h : Pt 2 → ℝ) : 0 ≤ l2sq h :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

/-- Cauchy–Schwarz on the unit cell. -/
lemma abs_integral_mul_le (a b : Pt 2 → ℝ) (ha : Continuous a) (hb : Continuous b) :
    |∫ x in cell 2, a x * b x| ≤ Real.sqrt (l2sq a) * Real.sqrt (l2sq b) := by
  set A := l2sq a
  set B := l2sq b
  set C := ∫ x in cell 2, a x * b x
  have hA := l2sq_nonneg' a
  have hq : ∀ r : ℝ, 0 ≤ B * (r * r) + 2 * C * r + A := by
    intro r
    have h0 := l2sq_nonneg' (fun x => a x + r * b x)
    have e : l2sq (fun x => a x + r * b x) = A + 2 * r * C + r ^ 2 * B := by
      have ex : ∀ x, (a x + r * b x) ^ 2 = (a x ^ 2 + 2 * r * (a x * b x)) + r ^ 2 * b x ^ 2 :=
        fun x => by ring
      have ia2 : IntegrableOn (fun x => a x ^ 2) (cell 2) :=
        integrableOn_cell_of_continuous (by fun_prop)
      have iab : IntegrableOn (fun x => 2 * r * (a x * b x)) (cell 2) :=
        integrableOn_cell_of_continuous (by fun_prop)
      have ib2 : IntegrableOn (fun x => r ^ 2 * b x ^ 2) (cell 2) :=
        integrableOn_cell_of_continuous (by fun_prop)
      have iab_sum : IntegrableOn (fun x => a x ^ 2 + 2 * r * (a x * b x)) (cell 2) :=
        integrableOn_cell_of_continuous (by fun_prop)
      simp only [l2sq, ex]
      rw [integral_add (f := fun x => a x ^ 2 + 2 * r * (a x * b x))
        (g := fun x => r ^ 2 * b x ^ 2) iab_sum ib2,
        integral_add (f := fun x => a x ^ 2) (g := fun x => 2 * r * (a x * b x)) ia2 iab,
        integral_const_mul, integral_const_mul]
      rfl
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [← Real.sqrt_mul hA, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- **Proposition 5.8** (transfer).  For `θ₀` smooth with `‖θ₀‖₂ = 1` and `|θ₀| ≤ M₀'`, the
dissipations of the true scalar and of the comparison scalar up to `T_N` differ by at most
`C_M M₀' N^{-M}`, equivalently the terminal energies differ by at most `2C_M M₀' N^{-M}`. -/
theorem transfer (hSc : ExternalScalar) : ∃ (C : ℝ) (N' : ℕ), ∀ θ₀ : Pt 2 → ℝ,
    ContDiff ℝ ∞ θ₀ → IsPeriodic θ₀ → l2sq θ₀ = 1 → ∀ M0 : ℝ, (∀ x, |θ₀ x| ≤ M0) →
    ∀ N : ℕ, N' ≤ N → ∀ (w : Phase) (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ),
    IsClassicalNS 1 (nuN N) 0 (gForce w) v p → ∀ θ : ℝ → Pt 2 → ℝ,
    IsClassicalScalar 1 (nuN N) v θ₀ θ → ∀ θb, IsComparisonScalar N w θ₀ θb →
    |dissipation (nuN N) θ (TN N) - dissipation (nuN N) θb (TN N)|
        ≤ C * M0 * (N : ℝ) ^ (-(M₀ : ℝ)) ∧
    |l2sq (θ (TN N)) - l2sq (θb (TN N))| ≤ 2 * C * M0 * (N : ℝ) ^ (-(M₀ : ℝ)) := by
  obtain ⟨Cd, N'd, hd⟩ := diagonal_velocity_error
  set Cd' := max Cd 0 with hCd'
  have hCd'0 : 0 ≤ Cd' := le_max_right _ _
  refine ⟨Real.sqrt (Cd' / 2), max N'd 1, fun θ₀ hθ₀ hp hl2 M0 hM N hN w v p hv θ hθ θb hθb => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hν := viscosity_properties.2.2.1 N hN1
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hM 0)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  set Y := (N : ℝ) ^ (-(M₀ : ℝ)) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hNr.le _
  have hY2 : Y ^ 2 = (N : ℝ) ^ (-(2 * (M₀ : ℝ))) := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]; congr 1; push_cast; ring
  -- the `L²` distance at `T_N`
  set Z := l2sq (fun x => θ (TN N) x - θb (TN N) x) with hZ
  have hchain := (transfer_chain hN1 w v p hv θ₀ θ hθ hM θb hθb (N + 1) (by omega) le_rfl).2
  have hdiag := hd N (le_trans (le_max_left _ _) hN) w v p hv
  set I := ∫ s in (0 : ℝ)..TN N, l2sqV (v s - vbar (nuN N) w s) with hI
  have hI' : I ≤ nuN N * (Cd' * (N : ℝ) ^ (-(2 * (M₀ : ℝ)))) := by
    have h1 : I = nuN N * (1 / nuN N * I) := by field_simp
    rw [h1]
    refine mul_le_mul_of_nonneg_left (hdiag.trans ?_) hν.le
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hNr.le _)
  have hZle : Z ≤ (Real.sqrt (Cd' / 2) * M0 * Y) ^ 2 := by
    have hc : 0 ≤ M0 ^ 2 / (2 * nuN N) := by positivity
    calc Z ≤ M0 ^ 2 / (2 * nuN N) * I := hchain
      _ ≤ M0 ^ 2 / (2 * nuN N) * (nuN N * (Cd' * (N : ℝ) ^ (-(2 * (M₀ : ℝ))))) :=
          mul_le_mul_of_nonneg_left hI' hc
      _ = (Real.sqrt (Cd' / 2) * M0 * Y) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hY2]
          field_simp
  have hsZ : Real.sqrt Z ≤ Real.sqrt (Cd' / 2) * M0 * Y := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt (Cd' / 2) * M0 * Y)]
    exact Real.sqrt_le_sqrt hZle
  -- energy identities
  obtain ⟨β, -, -, regv, -⟩ := hv.regular
  obtain ⟨βθ, -, -, regθ⟩ := hθ.regular
  have hT := TN_bounds N
  have eθ := energy_identity_core 1 (nuN N) v (fun t ht => hv.periodic_u t ht)
    (fun t ht => (regv.smooth_x t ht).of_le (by norm_num)) (fun t ht => hv.div_free t ht)
    θ₀ θ hθ (TN N) ⟨hT.1, hT.2⟩
  have eθb := ((comparison_scalar_identities hSc N hN1 w θ₀ hθ₀ hp).2.2 θb hθb).2 (TN N)
    ⟨hT.1, le_rfl⟩
  have dθ := dissipation_nonneg' (nuN N) hν.le θ (TN N) hT.1
  have dθb := dissipation_nonneg' (nuN N) hν.le θb (TN N) hT.1
  rw [hl2] at eθ eθb
  have hθ1 : l2sq (θ (TN N)) ≤ 1 := by linarith
  have hθb1 : l2sq (θb (TN N)) ≤ 1 := by linarith
  -- continuity of the terminal values
  have cθ : Continuous (θ (TN N)) := (regθ.smooth_x _ hT).continuous
  have cθb : Continuous (θb (TN N)) := by
    obtain ⟨-, hJ⟩ := hθb.2 N hN1 le_rfl
    obtain ⟨β', -, -, regJ⟩ := hJ.regular
    have := (regJ.smooth_x (ηs N) ⟨(ηs_pos N hN1).le, le_rfl⟩).continuous
    rwa [show sj N + δs N + ηs N = TN N from (sj_succ N hN1).symm] at this
  -- the difference of the terminal energies
  have hdiff : |l2sq (θ (TN N)) - l2sq (θb (TN N))| ≤ 2 * Real.sqrt Z := by
    have e : l2sq (θ (TN N)) - l2sq (θb (TN N)) =
        ∫ x in cell 2, (θ (TN N) x - θb (TN N) x) * (θ (TN N) x + θb (TN N) x) := by
      unfold l2sq
      rw [← integral_sub (f := fun x => θ (TN N) x ^ 2)
        (g := fun x => θb (TN N) x ^ 2)
        (integrableOn_cell_of_continuous (by fun_prop))
        (integrableOn_cell_of_continuous (by fun_prop))]
      exact setIntegral_congr_fun measurableSet_Icc fun x _ => by ring
    rw [e]
    refine (abs_integral_mul_le _ _ (cθ.sub cθb) (cθ.add cθb)).trans ?_
    have hS : l2sq (fun x => θ (TN N) x + θb (TN N) x) ≤ 4 := by
      have : l2sq (fun x => θ (TN N) x + θb (TN N) x) ≤
          2 * l2sq (θ (TN N)) + 2 * l2sq (θb (TN N)) := by
        unfold l2sq
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add
          (f := fun x => 2 * θ (TN N) x ^ 2) (g := fun x => 2 * θb (TN N) x ^ 2)
          (integrableOn_cell_of_continuous (continuous_const.mul (cθ.pow 2)))
          (integrableOn_cell_of_continuous (continuous_const.mul (cθb.pow 2)))]
        refine setIntegral_mono_on (integrableOn_cell_of_continuous ((cθ.add cθb).pow 2))
          (integrableOn_cell_of_continuous ((continuous_const.mul (cθ.pow 2)).add
            (continuous_const.mul (cθb.pow 2)))) measurableSet_Icc fun x _ => ?_
        nlinarith [sq_nonneg (θ (TN N) x - θb (TN N) x)]
      linarith
    have h2 : Real.sqrt (l2sq (fun x => θ (TN N) x + θb (TN N) x)) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hS
    have := Real.sqrt_nonneg Z
    rw [mul_comm 2]
    exact mul_le_mul_of_nonneg_left h2 this
  refine ⟨?_, ?_⟩
  · have e : dissipation (nuN N) θ (TN N) - dissipation (nuN N) θb (TN N) =
        -(l2sq (θ (TN N)) - l2sq (θb (TN N))) / 2 := by linarith
    rw [e, abs_div, abs_neg, abs_two]
    linarith
  · linarith

end AnomDiss
