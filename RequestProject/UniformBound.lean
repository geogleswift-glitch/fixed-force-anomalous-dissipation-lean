module

public import RequestProject.VortL4Main
public import RequestProject.Interpolation
public import RequestProject.ForceRegularity

/-!
# Proposition 6.2: uniform bound for the horizontal velocity

`‖v_ω^{ν_N}‖_{L^∞([0,1]×𝕋²)} ≤ C` uniformly in `ω` and `N ≥ 1`.

The proof follows the paper: on each stage the `L²` norm of the velocity is small (by the global
reset, Lemma 5.4, and the energy inequality), the `L⁴` norm of the vorticity grows at most
polynomially in the stage index (by the vorticity `L⁴` estimates of `RequestProject/VortL4Main`),
and the interpolation inequality (Lemma 6.1) combines the two.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

noncomputable section

namespace AnomDiss

/-! ### Elementary estimates -/

/-- Polynomials are dominated by `3ⁿ`. -/
lemma pow_le_three_pow (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, (n : ℝ) ^ k ≤ K * 3 ^ n := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ k / 3 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num)
  rw [← Nat.cofinite_eq_atTop] at ht
  obtain ⟨K, hK⟩ := ht.bddAbove_range_of_cofinite
  refine ⟨max K 0, le_max_right _ _, fun n => ?_⟩
  have h1 : (n : ℝ) ^ k / 3 ^ n ≤ max K 0 := (hK ⟨n, rfl⟩).trans (le_max_left _ _)
  rwa [div_le_iff₀ (by positivity)] at h1

/-! ### The force -/

/-- Uniform bounds for the force and its curl on the pulse intervals. -/
lemma force_piece_bounds : ∃ Cb Cc : ℝ, 0 ≤ Cb ∧ 0 ≤ Cc ∧ ∀ (w : Phase) (t : ℝ),
    gForce w t = 0 ∨ ∃ j, 1 ≤ j ∧ t ∈ Ioo (sj j) (sj j + δs j) ∧
      (∀ x, ‖gForce w t x‖ ≤ Cb / (kk j * δs j ^ 2)) ∧
      ∀ x, |curl2 (gForce w t) x| ≤ Cc / δs j ^ 2 := by
  obtain ⟨C0, hC0, h0⟩ := fpiece_bound (α := 0) le_rfl zero_le_one 0
  obtain ⟨C1, hC1, h1⟩ := fpiece_bound (α := 1) zero_le_one le_rfl 0
  refine ⟨C0, 2 * C1, hC0, by positivity, fun w t => ?_⟩
  rw [← forceD_zero_eq]
  rcases forceD_single w 0 t with h | ⟨j, hj, ht, h⟩
  · exact Or.inl h
  refine Or.inr ⟨j, hj, ht, fun x => ?_, fun x => ?_⟩
  · have hk := kk_pos' j
    have hδ := δs_pos j hj
    have := (h0 w j hj t).1 x
    rw [h]
    convert this using 1
    rw [show ((0 : ℝ) - 1) = -1 by norm_num, Real.rpow_neg_one,
      show (-((0 : ℕ) : ℝ) - 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hδ.le,
      Real.rpow_natCast]
    field_simp
  · have hδ := δs_pos j hj
    set f := fpiece w 0 j t
    have hL : ∀ x y, ‖f x - f y‖ ≤ C1 / δs j ^ 2 * ‖x - y‖ := by
      intro x y
      have := (h1 w j hj t).2 x y
      rw [Real.rpow_one] at this
      convert this using 2
      rw [sub_self, Real.rpow_zero, mul_one,
        show (-((0 : ℕ) : ℝ) - 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hδ.le,
        Real.rpow_natCast]
      field_simp
    have hL0 : 0 ≤ C1 / δs j ^ 2 := by positivity
    have hlip : LipschitzWith (C1 / δs j ^ 2).toNNReal f := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
      exact hL x y
    have hd : ∀ i y, ‖pd i f y‖ ≤ C1 / δs j ^ 2 := by
      intro i y
      unfold pd
      calc ‖fderiv ℝ f y (Pi.single i 1)‖ ≤ ‖fderiv ℝ f y‖ * ‖(Pi.single i 1 : Pt 2)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (C1 / δs j ^ 2) * 1 := by
            gcongr
            · exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans (by rw [Real.coe_toNNReal _ hL0])
            · rw [Pi.norm_single]; simp
        _ = C1 / δs j ^ 2 := mul_one _
    rw [h]
    unfold curl2
    have a0 := (abs_apply_le_norm (pd 0 f x) 1).trans (hd 0 x)
    have a1 := (abs_apply_le_norm (pd 1 f x) 0).trans (hd 1 x)
    calc |pd 0 f x 1 - pd 1 f x 0| ≤ |pd 0 f x 1| + |pd 1 f x 0| := abs_sub _ _
      _ ≤ 2 * C1 / δs j ^ 2 := by rw [mul_div_assoc]; linarith

/-! ### The energy inequality with a force -/

/-- `‖v(b)‖₂ ≤ ‖v(a)‖₂ + 3B(b - a)` when `|g| ≤ B` on `[a,b]`. -/
lemma l2V_growth {ν : ℝ} (hν : 0 ≤ ν) {v₀ : Pt 2 → Pt 2} {g : ℝ → Pt 2 → Pt 2}
    {v : ℝ → Pt 2 → Pt 2} {p : ℝ → Pt 2 → ℝ} (hv : IsClassicalNS 1 ν v₀ g v p)
    (hgc : ∀ t, Continuous (g t)) {a b B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hB : ∀ t ∈ Icc a b, ∀ x, ‖g t x‖ ≤ B) :
    l2V (v b) ≤ l2V (v a) + 3 * B * (b - a) := by
  obtain ⟨β, hβ, -, reg, regp⟩ := hv.regular
  have hsub : Icc a b ×ˢ (univ : Set (Pt 2)) ⊆ Icc 0 1 ×ˢ univ :=
    prod_mono (Icc_subset_Icc ha hb) subset_rfl
  obtain ⟨hform, hcont⟩ := l2sqV_integral_form hab v (dt 1 v) (reg.continuousOn.mono hsub)
    ((reg.holder_dt.continuousOn hβ).mono hsub) (fun s hs x => by
      have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
      exact (reg.diff_t x s (Ioo_subset_Icc_self hs')).hasDerivWithinAt.hasDerivAt
        (Icc_mem_nhds hs'.1 hs'.2))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl, hab⟩ 0)
  have key := root_growth (n := 2) (c := 3 * B) hab (by norm_num) hform hcont
    (fun t _ => setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity) ?_
  · unfold l2V
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have e : (1 / ((2 : ℕ) : ℝ)) = 1 / 2 := by norm_num
    rw [e] at key
    exact key
  intro s hs Z hZ hfZ
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs.1.le, hs.2.le.trans hb⟩
  have hsab : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  have hv2 := reg.smooth_x s hs01
  have hE := spatial_energy_le ν 0 hν (v s) (v s) (fun _ => 0) (fun x => dt 1 v s x - g s x)
    (p s) (hv2.of_le (by norm_num)) (hv.periodic_u s hs01) (hv.div_free s hs01) hv2
    (hv.periodic_u s hs01) (hv.div_free s hs01) (regp.smooth_x s hs01) (hv.periodic_p s hs01)
    contDiff_const (fun x => by simpa using eucOp_zero) (fun x => by
      have := hv.eqn s hs01 x
      rw [conv_zero_right, add_zero]
      show dt 1 v s x - g s x + conv (v s) (v s) x + grad (p s) x = ν • lap (v s) x
      rw [show dt 1 v s x - g s x + conv (v s) (v s) x + grad (p s) x =
        (dt 1 v s x + conv (v s) (v s) x + grad (p s) x) - g s x by abel, this]
      abel)
  have cv := hv2.continuous
  have cdt := continuous_dt_slice hβ reg hs01
  have cg := hgc s
  have cdot : ∀ {F G : Pt 2 → Pt 2}, Continuous F → Continuous G →
      Continuous fun x => 2 * dot (F x) (G x) := fun hF hG => by
    unfold dot
    exact continuous_const.mul (continuous_finset_sum _ fun k _ =>
      ((continuous_apply k).comp hF).mul ((continuous_apply k).comp hG))
  have hsplit : ∫ x in cell 2, 2 * dot (v s x) (dt 1 v s x) =
      (∫ x in cell 2, 2 * dot (v s x) (dt 1 v s x - g s x)) +
        ∫ x in cell 2, 2 * dot (v s x) (g s x) := by
    rw [← icell_add (cdot cv (cdt.fun_sub cg)) (cdot cv cg)]
    congr 1; funext x; simp only [dot, Fin.sum_univ_two, Pi.sub_apply]; ring
  have hpt : ∀ x, 2 * dot (v s x) (g s x) ≤ B / Z * ∑ k, v s x k ^ 2 + 2 * B * Z := by
    intro x
    have g0 : |g s x 0| ≤ B := (abs_apply_le_norm _ 0).trans (hB s hsab x)
    have g1 : |g s x 1| ≤ B := (abs_apply_le_norm _ 1).trans (hB s hsab x)
    have amgm : ∀ y : ℝ, 2 * B * |y| ≤ B / Z * y ^ 2 + B * Z := by
      intro y
      have : 0 ≤ B / Z * (|y| - Z) ^ 2 := by positivity
      have e : B / Z * (|y| - Z) ^ 2 = B / Z * y ^ 2 + B * Z - 2 * B * |y| := by
        rw [sub_sq, sq_abs]; field_simp; ring
      linarith
    have p0 : v s x 0 * g s x 0 ≤ |v s x 0| * B := by
      calc v s x 0 * g s x 0 ≤ |v s x 0 * g s x 0| := le_abs_self _
        _ = |v s x 0| * |g s x 0| := abs_mul _ _
        _ ≤ |v s x 0| * B := mul_le_mul_of_nonneg_left g0 (abs_nonneg _)
    have p1 : v s x 1 * g s x 1 ≤ |v s x 1| * B := by
      calc v s x 1 * g s x 1 ≤ |v s x 1 * g s x 1| := le_abs_self _
        _ = |v s x 1| * |g s x 1| := abs_mul _ _
        _ ≤ |v s x 1| * B := mul_le_mul_of_nonneg_left g1 (abs_nonneg _)
    have a0 := amgm (v s x 0)
    have a1 := amgm (v s x 1)
    simp only [dot, Fin.sum_univ_two]
    nlinarith
  have csum : Continuous fun x => ∑ k, v s x k ^ 2 :=
    continuous_finset_sum _ fun k _ => ((continuous_apply k).comp cv).pow 2
  have hint : ∫ x in cell 2, 2 * dot (v s x) (g s x) ≤
      ∫ x in cell 2, (B / Z * ∑ k, v s x k ^ 2 + 2 * B * Z) :=
    icell_mono (cdot cv cg) ((continuous_const.mul csum).add continuous_const) hpt
  rw [icell_add (f := fun x => B / Z * ∑ k, v s x k ^ 2) (g := fun _ => 2 * B * Z)
    (continuous_const.mul csum) continuous_const, icell_mul (B / Z), icell_const] at hint
  have hl : ∫ x in cell 2, ∑ k, v s x k ^ 2 ≤ Z ^ 2 := hfZ
  have hBZ : B / Z * ∫ x in cell 2, ∑ k, v s x k ^ 2 ≤ B * Z := by
    calc B / Z * ∫ x in cell 2, ∑ k, v s x k ^ 2 ≤ B / Z * Z ^ 2 := by gcongr
      _ = B * Z := by field_simp
  simp only [mul_zero, zero_mul] at hE
  show ∫ x in cell 2, 2 * dot (v s x) (dt 1 v s x) ≤ ((2 : ℕ) : ℝ) * (3 * B) * Z ^ (2 - 1)
  rw [hsplit]
  norm_num
  nlinarith

/-! ### Stage-wise bounds -/

/-- `i⁶ 3⁻ⁱ ≤ K m⁶ 3⁻ᵐ` for `1 ≤ m ≤ i`. -/
lemma decay6 : ∃ K : ℝ, 0 ≤ K ∧ ∀ m i : ℕ, 1 ≤ m → m ≤ i →
    (i : ℝ) ^ 6 / 3 ^ i ≤ K * (m : ℝ) ^ 6 / 3 ^ m := by
  obtain ⟨K, hK0, hK⟩ := pow_le_three_pow 6
  refine ⟨3 * K, by positivity, fun m i hm hmi => ?_⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hmi
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : ((m + a : ℕ) : ℝ) ≤ m * ((1 + a : ℕ) : ℝ) := by
    push_cast; nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
  have h2 := hK (1 + a)
  rw [div_le_iff₀ (by positivity)]
  calc ((m + a : ℕ) : ℝ) ^ 6 ≤ (m * ((1 + a : ℕ) : ℝ)) ^ 6 := by gcongr
    _ = (m : ℝ) ^ 6 * ((1 + a : ℕ) : ℝ) ^ 6 := by ring
    _ ≤ (m : ℝ) ^ 6 * (K * 3 ^ (1 + a)) := by gcongr
    _ = 3 * K * (m : ℝ) ^ 6 / 3 ^ m * 3 ^ (m + a) := by
        rw [pow_add, pow_add]; field_simp

/-- The force at time `t ≥ s_m` is `O(m⁶ 3⁻ᵐ)`, and its curl at time `t ≤ s_{m+1}` is
`O(m⁶)`. -/
lemma force_decay : ∃ Bg Ac : ℝ, 0 ≤ Bg ∧ 0 ≤ Ac ∧ ∀ (w : Phase) (t : ℝ),
    (∀ m : ℕ, 1 ≤ m → sj m ≤ t → ∀ x, ‖gForce w t x‖ ≤ Bg * (m : ℝ) ^ 6 / 3 ^ m) ∧
    (∀ m : ℕ, 1 ≤ m → t ≤ sj (m + 1) → ∀ x, |curl2 (gForce w t) x| ≤ Ac * (m : ℝ) ^ 6) := by
  obtain ⟨Cb, Cc, hCb, hCc, hF⟩ := force_piece_bounds
  obtain ⟨K, hK0, hK⟩ := decay6
  have hτ : 0 < τstar := by norm_num [τstar]
  refine ⟨Cb / τstar ^ 2 * K, Cc / τstar ^ 2, by positivity, by positivity, fun w t => ?_⟩
  rcases hF w t with h | ⟨i, hi, ht, hb, hc⟩
  · refine ⟨fun m _ _ x => ?_, fun m _ _ x => ?_⟩
    · rw [h]; simp only [Pi.zero_apply, norm_zero]; positivity
    · rw [h]; simp [curl2, pd]; positivity
  · have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    have hδ : δs i = τstar / (i : ℝ) ^ 3 := rfl
    have hkk : kk i = 3 ^ i := by simp [kk, qq]
    refine ⟨fun m hm hmt x => ?_, fun m hm htm x => ?_⟩
    · have hmi : m ≤ i := by
        by_contra hlt
        push_neg at hlt
        have := sj_mono (show i + 1 ≤ m by omega)
        have := sj_lt_succ i hi
        linarith [ht.2]
      calc ‖gForce w t x‖ ≤ Cb / (kk i * δs i ^ 2) := hb x
        _ = Cb / τstar ^ 2 * ((i : ℝ) ^ 6 / 3 ^ i) := by rw [hδ, hkk]; field_simp
        _ ≤ Cb / τstar ^ 2 * (K * (m : ℝ) ^ 6 / 3 ^ m) :=
            mul_le_mul_of_nonneg_left (hK m i hm hmi) (by positivity)
        _ = Cb / τstar ^ 2 * K * (m : ℝ) ^ 6 / 3 ^ m := by ring
    · have him : i ≤ m := by
        by_contra hlt
        push_neg at hlt
        have := sj_mono (show m + 1 ≤ i by omega)
        linarith [ht.1]
      calc |curl2 (gForce w t) x| ≤ Cc / δs i ^ 2 := hc x
        _ = Cc / τstar ^ 2 * (i : ℝ) ^ 6 := by rw [hδ]; field_simp
        _ ≤ Cc / τstar ^ 2 * (m : ℝ) ^ 6 := by gcongr

/-- `A_j^{ν_N} = O(j⁶ 3⁻ʲ)` uniformly in `1 ≤ j ≤ N`. -/
lemma apulse_bound : ∃ cA : ℝ, 0 ≤ cA ∧ ∀ N j : ℕ, 1 ≤ j → j ≤ N →
    Apulse (nuN N) j ≤ cA * (j : ℝ) ^ 6 / 3 ^ j := by
  obtain ⟨C, hC⟩ := (viscosity_properties).2.2.2.2.2.1
  have hτ : 0 < τstar := by norm_num [τstar]
  set c := max C 0 / (4 * π ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c ^ (M₀ + 1) / τstar, by positivity, fun N j hj hjN => ?_⟩
  have hN : 1 ≤ N := hj.trans hjN
  have hνp := (viscosity_properties).2.2.1 N hN
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk := kk_pos' j
  have hδ := δs_pos j hj
  have hx : nuN N * kk j ^ 2 * δs j ≤ c := by
    have h1 := hC N hN j hj hjN
    unfold muJN at h1
    have h2 : C / N ≤ max C 0 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [le_max_left C 0, le_max_right C 0]
    rw [hc, le_div_iff₀ (by positivity)]
    nlinarith
  have hx0 : 0 ≤ nuN N * kk j ^ 2 * δs j := by positivity
  have hA : Apulse (nuN N) j = (nuN N * kk j ^ 2 * δs j) ^ (M₀ + 1) / (kk j * δs j) := by
    unfold Apulse
    field_simp
    ring
  have hkk : kk j = 3 ^ j := by simp [kk, qq]
  rw [hA]
  calc (nuN N * kk j ^ 2 * δs j) ^ (M₀ + 1) / (kk j * δs j) ≤ c ^ (M₀ + 1) / (kk j * δs j) := by
        gcongr
    _ = c ^ (M₀ + 1) / τstar * ((j : ℝ) ^ 3 / 3 ^ j) := by
        rw [hkk]; unfold δs; field_simp
    _ ≤ c ^ (M₀ + 1) / τstar * ((j : ℝ) ^ 6 / 3 ^ j) := by
        gcongr
        norm_num
    _ = c ^ (M₀ + 1) / τstar * (j : ℝ) ^ 6 / 3 ^ j := by ring

lemma l2V_zero : l2V (0 : Pt 2 → Pt 2) = 0 := by simp [l2V, l2sqV]

lemma vort4_zero : vort4 (0 : Pt 2 → Pt 2) = 0 := by simp [vort4, curl2, pd]

/-- The `L²` norm of the velocity after the start of stage `j ≤ N` is `O(j⁶ 3⁻ʲ)`. -/
lemma stage_L2 : ∃ D1 : ℝ, 0 ≤ D1 ∧ ∀ (w : Phase) (N : ℕ) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ), 1 ≤ N → IsClassicalNS 1 (nuN N) 0 (gForce w) v p →
    ∀ j : ℕ, 1 ≤ j → j ≤ N → ∀ t, sj j ≤ t → t ≤ 1 →
    l2V (v t) ≤ D1 * (j : ℝ) ^ 6 / 3 ^ j := by
  obtain ⟨Bg, Ac, hBg, hAc, hF⟩ := force_decay
  obtain ⟨cA, hcA, hA⟩ := apulse_bound
  obtain ⟨CR, hCR⟩ := global_reset
  refine ⟨3 * max CR 0 * cA + 3 * Bg, by positivity,
    fun w N v p hN hv j hj hjN t hjt ht1 => ?_⟩
  have hν := (viscosity_properties).2.2.1 N hN
  have hg := l2V_growth hν.le hv (fun s => (gForce_slice_props w s).2.1.continuous)
    (sj_bounds j).1 hjt ht1 (B := Bg * (j : ℝ) ^ 6 / 3 ^ j)
    (fun s hs x => (hF w s).1 j hj hs.1 x)
  have hE : l2V (v (sj j)) ≤ 3 * max CR 0 * cA * (j : ℝ) ^ 6 / 3 ^ j := by
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      rw [sj_one, hv.init, l2V_zero]
      positivity
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have h1 := hCR (nuN N) hν w v p hv i (by omega)
      have h2 := hA N i (by omega) (by omega)
      have hAp0 : 0 ≤ Apulse (nuN N) i := by unfold Apulse δs kk τstar; positivity
      have hii : (i : ℝ) ^ 6 ≤ ((i + 1 : ℕ) : ℝ) ^ 6 := by gcongr; linarith
      calc l2V (v (sj (i + 1))) ≤ CR * Apulse (nuN N) i := h1
        _ ≤ max CR 0 * Apulse (nuN N) i :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hAp0
        _ ≤ max CR 0 * (cA * (i : ℝ) ^ 6 / 3 ^ i) := by gcongr
        _ ≤ max CR 0 * (cA * ((i + 1 : ℕ) : ℝ) ^ 6 / 3 ^ i) := by gcongr
        _ = 3 * max CR 0 * cA * ((i + 1 : ℕ) : ℝ) ^ 6 / 3 ^ (i + 1) := by
            rw [pow_succ]; field_simp; ring
  have hts : t - sj j ≤ 1 := by linarith [(sj_bounds j).1]
  have hB0 : 0 ≤ Bg * (j : ℝ) ^ 6 / 3 ^ j := by positivity
  have h3 : 3 * (Bg * (j : ℝ) ^ 6 / 3 ^ j) * (t - sj j) ≤ 3 * (Bg * (j : ℝ) ^ 6 / 3 ^ j) :=
    mul_le_of_le_one_right (by positivity) hts
  calc l2V (v t) ≤ l2V (v (sj j)) + 3 * (Bg * (j : ℝ) ^ 6 / 3 ^ j) * (t - sj j) := hg
    _ ≤ 3 * max CR 0 * cA * (j : ℝ) ^ 6 / 3 ^ j + 3 * (Bg * (j : ℝ) ^ 6 / 3 ^ j) := by
        linarith
    _ = (3 * max CR 0 * cA + 3 * Bg) * (j : ℝ) ^ 6 / 3 ^ j := by ring

/-- The `L⁴` norm of the vorticity during stage `j ≤ N` (and after `T_N` for `j = N`) is
`O(j²⁴)`; stated for its square root. -/
lemma stage_vort : ∃ D2 : ℝ, 0 ≤ D2 ∧ ∀ (w : Phase) (N : ℕ) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ), 1 ≤ N → IsClassicalNS 1 (nuN N) 0 (gForce w) v p →
    ∀ j : ℕ, 1 ≤ j → j ≤ N → ∀ t, sj j ≤ t → t ≤ 1 → (j < N → t ≤ sj (j + 1)) →
    vort4 (v t) ^ (1 / 2 : ℝ) ≤ D2 * (j : ℝ) ^ 12 := by
  obtain ⟨Bg, Ac, hBg, hAc, hF⟩ := force_decay
  have hτ : 0 < τstar := by norm_num [τstar]
  refine ⟨Ac ^ 2 + 12 * π ^ 2 * τstar * Bg ^ 2, by positivity,
    fun w N v p hN hv j hj hjN t hjt ht1 hlt => ?_⟩
  have hν := (viscosity_properties).2.2.1 N hN
  have hgc : ∀ s, ContDiff ℝ 1 (gForce w s) := fun s =>
    (gForce_slice_props w s).2.1.of_le (by exact_mod_cast le_top)
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have early : ∀ s, 0 ≤ s → s ≤ sj (j + 1) → vort4 (v s) ^ (1 / 4 : ℝ) ≤ Ac * (j : ℝ) ^ 6 := by
    intro s hs0 hs
    have hs1 : s ≤ 1 := hs.trans (sj_succ_lt_one j).le
    have h := vort4_root4_growth hν.le hv hgc le_rfl hs0 hs1 (A := Ac * (j : ℝ) ^ 6)
      (fun r hr x => (hF w r).2 j hj (hr.2.trans hs) x)
    rw [hv.init, vort4_zero, Real.zero_rpow (by norm_num), zero_add, sub_zero] at h
    exact h.trans (mul_le_of_le_one_right (by positivity) hs1)
  have sq : ∀ s, vort4 (v s) ^ (1 / 2 : ℝ) = (vort4 (v s) ^ (1 / 4 : ℝ)) ^ 2 := by
    intro s
    rw [← Real.rpow_natCast, ← Real.rpow_mul (vort4_nonneg _)]
    norm_num
  have early2 : ∀ s, 0 ≤ s → s ≤ sj (j + 1) →
      vort4 (v s) ^ (1 / 2 : ℝ) ≤ Ac ^ 2 * (j : ℝ) ^ 12 := by
    intro s hs0 hs
    rw [sq]
    calc (vort4 (v s) ^ (1 / 4 : ℝ)) ^ 2 ≤ (Ac * (j : ℝ) ^ 6) ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg (vort4_nonneg _) _) (early s hs0 hs) 2
      _ = Ac ^ 2 * (j : ℝ) ^ 12 := by ring
  have hj12 : 0 ≤ (j : ℝ) ^ 12 := by positivity
  by_cases hts : t ≤ sj (j + 1)
  · calc vort4 (v t) ^ (1 / 2 : ℝ) ≤ Ac ^ 2 * (j : ℝ) ^ 12 :=
          early2 t ((sj_bounds j).1.trans hjt) hts
      _ ≤ (Ac ^ 2 + 12 * π ^ 2 * τstar * Bg ^ 2) * (j : ℝ) ^ 12 := by
          have : 0 ≤ 12 * π ^ 2 * τstar * Bg ^ 2 := by positivity
          gcongr; linarith
  · push_neg at hts
    obtain rfl : j = N := by
      by_contra hne
      exact absurd (hlt (by omega)) (not_le.2 hts)
    have h := vort4_sqrt_growth hν hv hgc (fun s => (gForce_slice_props w s).1)
      (sj_bounds _).1 hts.le ht1 (B := Bg * (j : ℝ) ^ 6 / 3 ^ j)
      (fun r hr x => (hF w r).1 j hj ((sj_mono (Nat.le_succ j)).trans hr.1) x)
    have h0 := early2 (sj (j + 1)) (sj_bounds _).1 le_rfl
    have hnu := (viscosity_properties).1 j hN
    have hj0 : (j : ℝ) ≠ 0 := by positivity
    have key : 3 * (Bg * (j : ℝ) ^ 6 / 3 ^ j) ^ 2 / nuN j =
        12 * π ^ 2 * τstar * Bg ^ 2 * (j : ℝ) ^ 10 := by
      rw [hnu, show ((qq : ℕ) : ℝ) = 3 by norm_num [qq],
        show (3 : ℝ) ^ (2 * j) = (3 ^ j) ^ 2 by rw [← pow_mul, mul_comm]]
      field_simp
      ring
    rw [key] at h
    have hts1 : t - sj (j + 1) ≤ 1 := by linarith [(sj_bounds (j + 1)).1]
    have h10 : (j : ℝ) ^ 10 ≤ (j : ℝ) ^ 12 := pow_le_pow_right₀ hj' (by norm_num)
    have hK0 : 0 ≤ 12 * π ^ 2 * τstar * Bg ^ 2 := by positivity
    have h4 : 12 * π ^ 2 * τstar * Bg ^ 2 * (j : ℝ) ^ 10 * (t - sj (j + 1)) ≤
        12 * π ^ 2 * τstar * Bg ^ 2 * (j : ℝ) ^ 12 := by
      calc 12 * π ^ 2 * τstar * Bg ^ 2 * (j : ℝ) ^ 10 * (t - sj (j + 1)) ≤
            12 * π ^ 2 * τstar * Bg ^ 2 * (j : ℝ) ^ 10 :=
            mul_le_of_le_one_right (by positivity) hts1
        _ ≤ 12 * π ^ 2 * τstar * Bg ^ 2 * (j : ℝ) ^ 12 := by gcongr
    nlinarith

/-! ### Proposition 6.2 -/

/-- **Proposition 6.2** (uniform horizontal bound).  There are `N₁` and `C` such that
`‖v_ω^{ν_N}‖_{L^∞([0,1]×𝕋²)} ≤ C` for all `ω` and all `N ≥ N₁`. -/
theorem uniform_horizontal_bound : ∃ (N₁ : ℕ) (C : ℝ), 1 ≤ N₁ ∧ ∀ (w : Phase) (N : ℕ), N₁ ≤ N →
    ∀ (v : ℝ → Pt 2 → Pt 2) (p : ℝ → Pt 2 → ℝ), IsClassicalNS 1 (nuN N) 0 (gForce w) v p →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, euclNorm (v t x) ≤ C := by
  obtain ⟨D1, hD1, hL⟩ := stage_L2
  obtain ⟨D2, hD2, hV⟩ := stage_vort
  obtain ⟨CI, hCI⟩ := interpolation_bound
  obtain ⟨K6, hK6, hk6⟩ := pow_le_three_pow 6
  obtain ⟨K18, hK18, hk18⟩ := pow_le_three_pow 18
  set M := max CI 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨1, M * (D1 * D2 * K18) ^ (1 / 3 : ℝ) + M * (D1 * K6), le_rfl,
    fun w N hN v p hv t ht x => ?_⟩
  have hP1 : sj 1 ≤ t := by rw [sj_one]; exact ht.1
  obtain ⟨j, hj, hjN, hjt, hlt⟩ : ∃ j, 1 ≤ j ∧ j ≤ N ∧ sj j ≤ t ∧ (j < N → t ≤ sj (j + 1)) :=
    ⟨Nat.findGreatest (fun k => sj k ≤ t) N, Nat.le_findGreatest hN hP1,
      Nat.findGreatest_le N, Nat.findGreatest_spec (P := fun k => sj k ≤ t) hN hP1,
      fun hlt => le_of_lt (not_le.1 (Nat.findGreatest_is_greatest (P := fun k => sj k ≤ t) (n := N)
        (Nat.lt_succ_self _)
        (by omega)))⟩
  have hL1 := hL w N v p hN hv j hj hjN t hjt ht.2
  have hV1 := hV w N v p hN hv j hj hjN t hjt ht.2 hlt
  obtain ⟨β, hβ, -, reg, -⟩ := hv.regular
  have hvt := reg.smooth_x t ht
  have hI := hCI (v t) (hvt.of_le (by norm_num)) (hv.periodic_u t ht) (hv.div_free t ht) x
  set L := l2V (v t) with hLdef
  set V := vort4 (v t) with hVdef
  change euclNorm (v t x) ≤ CI * L ^ (1 / 3 : ℝ) * (V ^ (1 / 4 : ℝ)) ^ (2 / 3 : ℝ) + CI * L at hI
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hV0 : 0 ≤ V := vort4_nonneg _
  have e : L ^ (1 / 3 : ℝ) * (V ^ (1 / 4 : ℝ)) ^ (2 / 3 : ℝ) = (L * V ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_mul hV0, Real.mul_rpow hL0 (Real.rpow_nonneg hV0 _), ← Real.rpow_mul hV0]
    norm_num
  have hLQ : L * V ^ (1 / 2 : ℝ) ≤ D1 * D2 * K18 :=
    calc L * V ^ (1 / 2 : ℝ) ≤ (D1 * (j : ℝ) ^ 6 / 3 ^ j) * (D2 * (j : ℝ) ^ 12) :=
          mul_le_mul hL1 hV1 (Real.rpow_nonneg hV0 _) (by positivity)
      _ = D1 * D2 * ((j : ℝ) ^ 18 / 3 ^ j) := by ring
      _ ≤ D1 * D2 * K18 := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          exact hk18 j
  have hLb : L ≤ D1 * K6 := hL1.trans (by
    rw [mul_div_assoc]
    gcongr
    rw [div_le_iff₀ (by positivity)]
    exact hk6 j)
  have hQ0 : 0 ≤ L * V ^ (1 / 2 : ℝ) := mul_nonneg hL0 (Real.rpow_nonneg hV0 _)
  calc euclNorm (v t x) ≤ CI * L ^ (1 / 3 : ℝ) * (V ^ (1 / 4 : ℝ)) ^ (2 / 3 : ℝ) + CI * L := hI
    _ = CI * (L * V ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) + CI * L := by rw [mul_assoc, e]
    _ ≤ M * (L * V ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) + M * L := by
        gcongr ?_ + ?_
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hQ0 _)
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL0
    _ ≤ M * (D1 * D2 * K18) ^ (1 / 3 : ℝ) + M * (D1 * K6) := by
        gcongr

end AnomDiss
