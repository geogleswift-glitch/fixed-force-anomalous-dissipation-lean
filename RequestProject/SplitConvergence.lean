module

public import RequestProject.SplitFlow

/-!
# Convergence of the Lie splitting for a cell solution

For a classical cell solution `h` of `∂ₛh + B·∇h = κΔh` (`κ = μ/4π²`) the split operator with
`n` steps applied to the quasi-periodic exponential converges uniformly to `h(1)`, with rate
`n^{-β/2}`.  The proof is a local error estimate for one step (Taylor expansion in space and the
mean value theorem in time) followed by a telescoping sum, using that each step is a
sup-norm contraction.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- Local error of one splitting step for a solution `h` of the advection–diffusion equation. -/
theorem cell_local_error {V : ℝ → Pt 2 → Pt 2} {M K : ℝ≥0} (hV : GoodField V M K) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|)
    {h : ℝ → Pt 2 → ℂ} {β D0 D1 D2 H Hd κ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hsm : ∀ t ∈ Icc (0:ℝ) 1, ContDiff ℝ 2 (h t))
    (hD0 : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖h t x‖ ≤ D0)
    (hD1 : ∀ t ∈ Icc (0:ℝ) 1, ∀ j x, ‖pd j (h t) x‖ ≤ D1)
    (hD2 : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j x, ‖pd i (pd j (h t)) x‖ ≤ D2)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j x y,
      ‖pd i (pd j (h t)) x - pd i (pd j (h t)) y‖ ≤ H * ‖x - y‖ ^ β)
    (hdt : ∀ x, ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun s => h s x) (dt 1 h t x) (Icc 0 1) t)
    (hHd : ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ x y,
      ‖dt 1 h t x - dt 1 h s y‖ ≤ Hd * (‖x - y‖ ^ β + |t - s| ^ (β / 2)))
    (heq : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, dt 1 h t x + conv (V t) (h t) x = κ • lap (h t) x)
    {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1 : t₁ ≤ 1)
    (hlam : K * (t₁ - t₀) * Real.exp (K * (t₁ - t₀)) ≤ 1)
    (v : ℝ≥0) (hv : (v : ℝ) = 2 * κ * (t₁ - t₀)) (y : Pt 2) :
    ‖heatOp v (h t₀ ∘ gflow V t₁ t₀) y - h t₁ y‖ ≤
      (2 * D1 * (K * (t₁ - t₀) * Real.exp (K * (t₁ - t₀))) * ∫ ζ, ‖ζ‖ ^ (1 : ℝ) ∂(gauss2 v) +
        6 * D2 * (K * (t₁ - t₀) * Real.exp (K * (t₁ - t₀))) * ∫ ζ, ‖ζ‖ ^ (2 : ℝ) ∂(gauss2 v) +
        32 * H * ∫ ζ, ‖ζ‖ ^ (2 + β) ∂(gauss2 v)) +
      (Hd * (t₁ - t₀) * (t₁ - t₀) ^ (β / 2) + (4 * H * (M * (t₁ - t₀)) ^ (2 + β) +
        2 * D2 * (M * (t₁ - t₀)) ^ 2) + 2 * D1 * ((Lt + K * M) * (t₁ - t₀) ^ 2) +
        (t₁ - t₀) * (Hd * (M * (t₁ - t₀)) ^ β)) := by
  have hHd0 : 0 ≤ Hd := by
    have := hHd 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ 0 0
    rw [sub_self, norm_zero, Real.zero_rpow hβ0.ne', zero_add] at this
    norm_num at this
    exact (norm_nonneg _).trans this
  set a := t₁ - t₀ with ha
  have ha0 : 0 ≤ a := by linarith
  have ht₀ : t₀ ∈ Icc (0:ℝ) 1 := ⟨h0, h01.trans h1⟩
  have ht₁ : t₁ ∈ Icc (0:ℝ) 1 := ⟨h0.trans h01, h1⟩
  set f := h t₀ with hf
  set ψ := gflow V t₁ t₀ with hψ
  set z := ψ y with hz
  set lam := K * a * Real.exp (K * a) with hlamdef
  have hlam0 : 0 ≤ lam := by positivity
  -- the heat-step expansion
  have hψl : ∀ x x', ‖(ψ x - x) - (ψ x' - x')‖ ≤ lam * ‖x - x'‖ := by
    intro x x'
    have := hV.norm_gflow_sub_sub_le t₁ t₀ x x'
    rwa [abs_sub_comm, ← ha, abs_of_nonneg ha0] at this
  have hA := heat_step_expansion (hsm t₀ ht₀) hβ0 hβ1 (hD0 t₀ ht₀) (hD1 t₀ ht₀) (hD2 t₀ ht₀)
    (hH t₀ ht₀) (hV.continuous_gflow t₁ t₀) hlam0 hlam hψl v y
  -- the transport / time part
  have hvk : (v : ℝ) / 2 = a * κ := by rw [hv]; ring
  have hB : ‖f z + ((v : ℝ) / 2) • lap f z - h t₁ y‖ ≤
      Hd * a * a ^ (β / 2) + (4 * H * (M * a) ^ (2 + β) + 2 * D2 * (M * a) ^ 2) +
        2 * D1 * ((Lt + K * M) * a ^ 2) + a * (Hd * (M * a) ^ β) := by
    set δ := y - z with hδ
    have hδM : ‖δ‖ ≤ M * a := by
      have := hV.norm_gflow_sub_le t₁ t₀ y
      rw [norm_sub_rev, abs_sub_comm, ← ha, abs_of_nonneg ha0] at this
      exact this
    -- (B1) time increment
    have hB1 : ‖h t₁ y - h t₀ y - a • dt 1 h t₀ y‖ ≤ Hd * a * a ^ (β / 2) := by
      have hsub : Icc t₀ t₁ ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc h0 h1
      have hd : ∀ s ∈ Icc t₀ t₁, HasDerivWithinAt (fun s => h s y - (s - t₀) • dt 1 h t₀ y)
          (dt 1 h s y - dt 1 h t₀ y) (Icc t₀ t₁) s := by
        intro s hs
        have h2 := ((hasDerivAt_id s).sub_const t₀).smul_const (dt 1 h t₀ y)
        have := ((hdt y s (hsub hs)).mono hsub).fun_sub h2.hasDerivWithinAt
        simpa using this
      have hb : ∀ s ∈ Ico t₀ t₁, ‖dt 1 h s y - dt 1 h t₀ y‖ ≤ Hd * a ^ (β / 2) := by
        intro s hs
        have := hHd s (hsub (Ico_subset_Icc_self hs)) t₀ ht₀ y y
        rw [sub_self, norm_zero, Real.zero_rpow hβ0.ne', zero_add] at this
        refine this.trans ?_
        gcongr
        rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
      have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t₁ ⟨h01, le_rfl⟩
      simp only [sub_self, zero_smul, sub_zero] at this
      calc ‖h t₁ y - h t₀ y - a • dt 1 h t₀ y‖ = ‖h t₁ y - (t₁ - t₀) • dt 1 h t₀ y - h t₀ y‖ := by
            congr 1; rw [ha]; abel
        _ ≤ Hd * a ^ (β / 2) * (t₁ - t₀) := this
        _ = Hd * a * a ^ (β / 2) := by rw [← ha]; ring
    -- (B2) spatial Taylor expansion to first order
    have hH0 : 0 ≤ H := by
      have := hH t₀ ht₀ 0 0 (Pi.single 0 1) 0
      have h1 : (0:ℝ) ≤ H * ‖(Pi.single 0 1 : Pt 2) - 0‖ ^ β := (norm_nonneg _).trans this
      rwa [sub_zero, Pi.norm_single, norm_one, Real.one_rpow, mul_one] at h1
    set Lδ : ℂ := ∑ j, δ j • pd j f z with hLδ
    have hB2 : ‖h t₀ y - f z - Lδ‖ ≤ 4 * H * (M * a) ^ (2 + β) + 2 * D2 * (M * a) ^ 2 := by
      have hT := taylor2_holder (hsm t₀ ht₀) hβ0.le (hH t₀ ht₀) z δ
      have hzδ : z + δ = y := by simp [hδ]
      rw [hzδ] at hT
      set Qδ : ℂ := (1 / 2 : ℝ) • ∑ j, ∑ i, (δ j * δ i) • pd i (pd j f) z
      have hQ : ‖Qδ‖ ≤ 2 * D2 * ‖δ‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
        have hterm : ∀ i j, ‖(δ j * δ i) • pd i (pd j f) z‖ ≤ ‖δ‖ ^ 2 * D2 := by
          intro i j
          rw [norm_smul, norm_mul, sq]
          exact mul_le_mul (mul_le_mul (norm_le_pi_norm δ j) (norm_le_pi_norm δ i)
            (norm_nonneg _) (norm_nonneg _)) (hD2 t₀ ht₀ i j z) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        calc 1 / 2 * ‖∑ j, ∑ i, (δ j * δ i) • pd i (pd j f) z‖
            ≤ 1 / 2 * ∑ j : Fin 2, ∑ i : Fin 2, ‖δ‖ ^ 2 * D2 := by
              gcongr
              exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
                (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i j))
          _ = 2 * D2 * ‖δ‖ ^ 2 := by simp; ring
      have e : h t₀ y - f z - Lδ = (f y - f z - Lδ - Qδ) + Qδ := by rw [hf]; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add (hT.trans ?_) (hQ.trans ?_))
      · gcongr
      · have hD2n : 0 ≤ D2 := (norm_nonneg _).trans (hD2 t₀ ht₀ 0 0 0)
        gcongr
    -- (B3) the transport increment
    have hB3 : ‖Lδ - a • conv (V t₀) f z‖ ≤ 2 * D1 * ((Lt + K * M) * a ^ 2) := by
      have hstep := hV.norm_inv_step_le hLt h01 y
      rw [← ha] at hstep
      have e : Lδ - a • conv (V t₀) f z = ∑ j, (δ - a • V t₀ z) j • pd j f z := by
        simp only [hLδ, conv, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, ← sub_smul,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ j, ‖(δ - a • V t₀ z) j • pd j f z‖ ≤ (Lt + K * M) * a ^ 2 * D1 := by
        intro j
        rw [norm_smul]
        exact mul_le_mul ((norm_le_pi_norm _ j).trans hstep) (hD1 t₀ ht₀ j z) (norm_nonneg _)
          ((norm_nonneg _).trans hstep)
      calc ∑ j, ‖(δ - a • V t₀ z) j • pd j f z‖ ≤ ∑ j : Fin 2, (Lt + K * M) * a ^ 2 * D1 :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = 2 * D1 * ((Lt + K * M) * a ^ 2) := by simp; ring
    -- (B4) the time derivative at two nearby points
    have hB4 : ‖a • (dt 1 h t₀ y - dt 1 h t₀ z)‖ ≤ a * (Hd * (M * a) ^ β) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
      gcongr
      have := hHd t₀ ht₀ t₀ ht₀ y z
      rw [sub_self, abs_zero, Real.zero_rpow (by linarith), add_zero] at this
      refine this.trans ?_
      gcongr
    have hpde := heq t₀ ht₀ z
    have e : f z + ((v : ℝ) / 2) • lap f z - h t₁ y =
        -((h t₁ y - h t₀ y - a • dt 1 h t₀ y) + (h t₀ y - f z - Lδ) +
          (Lδ - a • conv (V t₀) f z) + a • (dt 1 h t₀ y - dt 1 h t₀ z)) -
        a • (dt 1 h t₀ z + conv (V t₀) (h t₀) z - κ • lap (h t₀) z) := by
      rw [hvk, mul_smul]
      simp only [smul_sub, smul_add]
      abel
    rw [e, hpde, sub_self, smul_zero, sub_zero, norm_neg]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add₃_le).trans ?_) hB4)
    exact add_le_add (add_le_add hB1 hB2) hB3
  calc ‖heatOp v (h t₀ ∘ gflow V t₁ t₀) y - h t₁ y‖
      = ‖(heatOp v (f ∘ ψ) y - f (ψ y) - ((v : ℝ) / 2) • lap f (ψ y)) +
          (f z + ((v : ℝ) / 2) • lap f z - h t₁ y)‖ := by
        congr 1; simp only [hz]; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hA hB)

lemma rpow_le_of_le_one {a p q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : 0 ≤ q) (hpq : q ≤ p) :
    a ^ p ≤ a ^ q :=
  Real.rpow_le_rpow_of_exponent_ge' ha0 ha1 hq hpq

lemma gauss2_moment_le_of_le {v : ℝ≥0} {a p : ℝ} (hp : 0 < p) (hva : (v : ℝ) ≤ a) :
    ∫ ζ, ‖ζ‖ ^ p ∂(gauss2 v) ≤ 2 * gmom p * a ^ (p / 2) := by
  refine (integral_gauss2_norm_rpow_le v hp).trans ?_
  have := gmom_nonneg p
  gcongr

/-- The local error is `O((t₁ - t₀)^{1 + β/2})`. -/
theorem cell_local_error_rate {V : ℝ → Pt 2 → Pt 2} {M K : ℝ≥0} (hV : GoodField V M K)
    {Lt : ℝ} (hLt0 : 0 ≤ Lt) (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|)
    {h : ℝ → Pt 2 → ℂ} {β D0 D1 D2 H Hd κ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hκ1 : κ ≤ 1 / 2)
    (hsm : ∀ t ∈ Icc (0:ℝ) 1, ContDiff ℝ 2 (h t))
    (hD0 : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖h t x‖ ≤ D0)
    (hD1 : ∀ t ∈ Icc (0:ℝ) 1, ∀ j x, ‖pd j (h t) x‖ ≤ D1)
    (hD2 : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j x, ‖pd i (pd j (h t)) x‖ ≤ D2)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j x y,
      ‖pd i (pd j (h t)) x - pd i (pd j (h t)) y‖ ≤ H * ‖x - y‖ ^ β)
    (hdt : ∀ x, ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun s => h s x) (dt 1 h t x) (Icc 0 1) t)
    (hHd : ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ x y,
      ‖dt 1 h t x - dt 1 h s y‖ ≤ Hd * (‖x - y‖ ^ β + |t - s| ^ (β / 2)))
    (heq : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, dt 1 h t x + conv (V t) (h t) x = κ • lap (h t) x) :
    ∃ C : ℝ, ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ → t₁ ≤ 1 →
      K * (t₁ - t₀) * Real.exp (K * (t₁ - t₀)) ≤ 1 →
      ∀ v : ℝ≥0, (v : ℝ) = 2 * κ * (t₁ - t₀) → ∀ y,
        ‖heatOp v (h t₀ ∘ gflow V t₁ t₀) y - h t₁ y‖ ≤ C * (t₁ - t₀) ^ (1 + β / 2) := by
  have hD1n : 0 ≤ D1 := (norm_nonneg _).trans (hD1 0 ⟨le_rfl, zero_le_one⟩ 0 0)
  have hD2n : 0 ≤ D2 := (norm_nonneg _).trans (hD2 0 ⟨le_rfl, zero_le_one⟩ 0 0 0)
  have hHn : 0 ≤ H := by
    have := hH 0 ⟨le_rfl, zero_le_one⟩ 0 0 (Pi.single 0 1) 0
    have h1 : (0:ℝ) ≤ H * ‖(Pi.single 0 1 : Pt 2) - 0‖ ^ β := (norm_nonneg _).trans this
    rwa [sub_zero, Pi.norm_single, norm_one, Real.one_rpow, mul_one] at h1
  have hHd0 : 0 ≤ Hd := by
    have := hHd 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ 0 0
    rw [sub_self, norm_zero, Real.zero_rpow hβ0.ne', zero_add] at this
    norm_num at this
    exact (norm_nonneg _).trans this
  have g1 := gmom_nonneg 1
  have g2 := gmom_nonneg 2
  have g3 := gmom_nonneg (2 + β)
  set E := Real.exp (K : ℝ) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨4 * D1 * K * E * gmom 1 + 12 * D2 * K * E * gmom 2 + 64 * H * gmom (2 + β) + Hd +
    4 * H * (M : ℝ) ^ (2 + β) + 2 * D2 * (M : ℝ) ^ 2 + 2 * D1 * (Lt + K * M) +
    Hd * (M : ℝ) ^ β, fun t₀ t₁ h0 h01 h1 hlam v hv y => ?_⟩
  have key := cell_local_error hV hLt hβ0 hβ1 hsm hD0 hD1 hD2 hH hdt hHd heq h0 h01 h1 hlam v
    hv y
  refine key.trans ?_
  set a := t₁ - t₀ with ha
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hva : (v : ℝ) ≤ a := by rw [hv]; nlinarith
  set q := 1 + β / 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hpow : ∀ p, q ≤ p → a ^ p ≤ a ^ q := fun p hp => rpow_le_of_le_one ha0 ha1 hq0 hp
  have hexp : Real.exp (K * a) ≤ E := by
    rw [hE]; exact Real.exp_le_exp.2 (mul_le_of_le_one_right K.2 ha1)
  have hlamb : K * a * Real.exp (K * a) ≤ K * E * a := by
    have : (0:ℝ) ≤ K := K.2
    calc K * a * Real.exp (K * a) ≤ K * a * E := by gcongr
      _ = K * E * a := by ring
  have m1 := gauss2_moment_le_of_le (v := v) one_pos hva
  have m2 := gauss2_moment_le_of_le (v := v) two_pos hva
  have m3 := gauss2_moment_le_of_le (v := v) (show (0:ℝ) < 2 + β by linarith) hva
  have hK0 : (0:ℝ) ≤ K := K.2
  have hM0 : (0:ℝ) ≤ M := M.2
  -- powers of `a`
  have e32 : a * a ^ ((1:ℝ) / 2) = a ^ ((3:ℝ) / 2) := by
    rw [← Real.rpow_one_add' ha0 (by norm_num)]; norm_num
  have e2 : a * a = a ^ (2:ℝ) := by rw [Real.rpow_two, sq]
  have p32 : a ^ ((3:ℝ) / 2) ≤ a ^ q := hpow _ (by rw [hq]; linarith)
  have p2 : a ^ (2:ℝ) ≤ a ^ q := hpow _ (by rw [hq]; linarith)
  have p3 : a ^ ((2 + β) / 2) = a ^ q := by rw [hq]; ring_nf
  have p4 : a * a ^ (β / 2) = a ^ q := by
    rw [hq, Real.rpow_add' ha0 (by positivity), Real.rpow_one]
  have p5 : (M * a) ^ (2 + β) ≤ (M : ℝ) ^ (2 + β) * a ^ q := by
    rw [Real.mul_rpow hM0 ha0]
    exact mul_le_mul_of_nonneg_left (hpow _ (by linarith)) (by positivity)
  have p6 : (M * a) ^ 2 ≤ (M : ℝ) ^ 2 * a ^ q := by
    rw [mul_pow]; gcongr; rw [← Real.rpow_natCast]; push_cast; exact p2
  have p7 : a ^ 2 ≤ a ^ q := by rw [← Real.rpow_natCast]; push_cast; exact p2
  have p8 : a * (M * a) ^ β ≤ (M : ℝ) ^ β * a ^ q := by
    rw [Real.mul_rpow hM0 ha0]
    have : a * a ^ β = a ^ (1 + β) := by rw [Real.rpow_add' ha0 (by positivity), Real.rpow_one]
    calc a * ((M:ℝ) ^ β * a ^ β) = (M:ℝ) ^ β * (a * a ^ β) := by ring
      _ ≤ (M:ℝ) ^ β * a ^ q := by
        rw [this]
        exact mul_le_mul_of_nonneg_left (hpow _ (by linarith)) (by positivity)
  have T1 : 2 * D1 * (K * a * Real.exp (K * a)) * ∫ ζ, ‖ζ‖ ^ (1 : ℝ) ∂(gauss2 v) ≤
      4 * D1 * K * E * gmom 1 * a ^ q := by
    calc 2 * D1 * (K * a * Real.exp (K * a)) * ∫ ζ, ‖ζ‖ ^ (1 : ℝ) ∂(gauss2 v)
        ≤ 2 * D1 * (K * E * a) * (2 * gmom 1 * a ^ ((1:ℝ) / 2)) := by
          gcongr
      _ = 4 * D1 * K * E * gmom 1 * (a * a ^ ((1:ℝ) / 2)) := by ring
      _ ≤ 4 * D1 * K * E * gmom 1 * a ^ q := by rw [e32]; gcongr
  have T2 : 6 * D2 * (K * a * Real.exp (K * a)) * ∫ ζ, ‖ζ‖ ^ (2 : ℝ) ∂(gauss2 v) ≤
      12 * D2 * K * E * gmom 2 * a ^ q := by
    calc 6 * D2 * (K * a * Real.exp (K * a)) * ∫ ζ, ‖ζ‖ ^ (2 : ℝ) ∂(gauss2 v)
        ≤ 6 * D2 * (K * E * a) * (2 * gmom 2 * a ^ ((2:ℝ) / 2)) := by
          gcongr
      _ = 12 * D2 * K * E * gmom 2 * (a * a) := by norm_num; ring
      _ ≤ 12 * D2 * K * E * gmom 2 * a ^ q := by rw [e2]; gcongr
  have T3 : 32 * H * ∫ ζ, ‖ζ‖ ^ (2 + β) ∂(gauss2 v) ≤ 64 * H * gmom (2 + β) * a ^ q := by
    calc 32 * H * ∫ ζ, ‖ζ‖ ^ (2 + β) ∂(gauss2 v) ≤ 32 * H * (2 * gmom (2 + β) * a ^ q) := by
          rw [← p3]; gcongr
      _ = 64 * H * gmom (2 + β) * a ^ q := by ring
  have T4 : Hd * a * a ^ (β / 2) = Hd * a ^ q := by rw [mul_assoc, p4]
  have T5 : 4 * H * (M * a) ^ (2 + β) ≤ 4 * H * (M : ℝ) ^ (2 + β) * a ^ q := by
    rw [mul_assoc (4 * H)]; gcongr
  have T6 : 2 * D2 * (M * a) ^ 2 ≤ 2 * D2 * (M : ℝ) ^ 2 * a ^ q := by
    rw [mul_assoc (2 * D2)]; gcongr
  have T7 : 2 * D1 * ((Lt + K * M) * a ^ 2) ≤ 2 * D1 * (Lt + K * M) * a ^ q := by
    rw [mul_assoc (2 * D1)]; gcongr
  have T8 : a * (Hd * (M * a) ^ β) ≤ Hd * (M : ℝ) ^ β * a ^ q := by
    calc a * (Hd * (M * a) ^ β) = Hd * (a * (M * a) ^ β) := by ring
      _ ≤ Hd * ((M : ℝ) ^ β * a ^ q) := by gcongr
      _ = Hd * (M : ℝ) ^ β * a ^ q := by ring
  rw [T4]
  linarith [T1, T2, T3, T5, T6, T7, T8]

/-! ### Telescoping -/

lemma splitOp_succ (μ : ℝ) (n : ℕ) (ψ : ℕ → Pt 2 → Pt 2) (j : ℕ) (g : Pt 2 → ℂ) :
    splitOp μ n ψ (j + 1) g = heatOp (splitVar μ n) (splitOp μ n ψ j g ∘ ψ (j + 1)) := rfl

lemma splitOp_zero (μ : ℝ) (n : ℕ) (ψ : ℕ → Pt 2 → Pt 2) (g : Pt 2 → ℂ) :
    splitOp μ n ψ 0 g = g := rfl

/-- The split operator preserves continuity and sup-norm bounds. -/
lemma splitOp_cont_bdd (μ : ℝ) (n : ℕ) {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, Continuous (ψ i))
    {g : Pt 2 → ℂ} (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (j : ℕ) :
    Continuous (splitOp μ n ψ j g) ∧ ∀ x, ‖splitOp μ n ψ j g x‖ ≤ B := by
  induction j with
  | zero => exact ⟨hg, hB⟩
  | succ j ih =>
    rw [splitOp_succ]
    exact ⟨continuous_heatOp (ih.1.comp (hψ _)) (fun x => ih.2 _) _,
      fun x => norm_heatOp_le (fun y => ih.2 _) _ x⟩

/-- Telescoping: local errors `ε` add up. -/
lemma splitOp_error_le (μ : ℝ) (n : ℕ) {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, Continuous (ψ i))
    {h : ℝ → Pt 2 → ℂ} {D0 : ℝ} (hcont : ∀ j : ℕ, j ≤ n → Continuous (h (j / n)))
    (hbd : ∀ j : ℕ, j ≤ n → ∀ x, ‖h (j / n) x‖ ≤ D0)
    {g : Pt 2 → ℂ} (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (hg0 : g = h 0) {ε : ℝ}
    (hloc : ∀ j : ℕ, j < n → ∀ y,
      ‖heatOp (splitVar μ n) (h (j / n) ∘ ψ (j + 1)) y - h ((j + 1 : ℕ) / n) y‖ ≤ ε) :
    ∀ j : ℕ, j ≤ n → ∀ y, ‖splitOp μ n ψ j g y - h (j / n) y‖ ≤ j * ε := by
  intro j
  induction j with
  | zero => intro _ y; simp [splitOp_zero, hg0]
  | succ j ih =>
    intro hj y
    have hjn : j ≤ n := by omega
    have hP := splitOp_cont_bdd μ n hψ hg hB j
    set E : Pt 2 → ℂ := fun x => splitOp μ n ψ j g x - h (j / n) x with hE
    have hEc : Continuous E := hP.1.sub (hcont j hjn)
    have hEb : ∀ x, ‖E x‖ ≤ j * ε := ih hjn
    have hsplit : splitOp μ n ψ j g ∘ ψ (j + 1) =
        fun x => E (ψ (j + 1) x) + (h (j / n) ∘ ψ (j + 1)) x := by
      funext x; simp [hE]
    have hadd : heatOp (splitVar μ n) (fun x => E (ψ (j + 1) x) + (h (j / n) ∘ ψ (j + 1)) x) y =
        heatOp (splitVar μ n) (fun x => E (ψ (j + 1) x)) y +
          heatOp (splitVar μ n) (h (j / n) ∘ ψ (j + 1)) y :=
      heatOp_add (hEc.comp (hψ _)) ((hcont j hjn).comp (hψ _)) (fun x => hEb _)
        (fun x => hbd j hjn _) _ _
    rw [splitOp_succ, hsplit, hadd]
    have h1 := norm_heatOp_le (g := fun x => E (ψ (j + 1) x)) (fun x => hEb _) (splitVar μ n) y
    have h2 := hloc j (by omega) y
    calc ‖heatOp (splitVar μ n) (fun x => E (ψ (j + 1) x)) y +
          heatOp (splitVar μ n) (h (j / n) ∘ ψ (j + 1)) y - h ((j + 1 : ℕ) / n) y‖
        = ‖heatOp (splitVar μ n) (fun x => E (ψ (j + 1) x)) y +
          (heatOp (splitVar μ n) (h (j / n) ∘ ψ (j + 1)) y - h ((j + 1 : ℕ) / n) y)‖ := by
          congr 1; abel
      _ ≤ j * ε + ε := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = ((j + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-! ### The canonical splitting and its convergence -/

variable {L M : ℕ} {S : ℕ → ℝ}

/-- The canonical inverse flow maps of the splitting with `n` steps:
`ψ_i = Φ_{i/n → (i-1)/n}` for the field `B_{μ,ω}`. -/
def canonPsi (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (n : ℕ) (i : ℕ) :
    Pt 2 → Pt 2 :=
  gflow (splitField cf μ w) ((i : ℝ) / n) (((i : ℝ) - 1) / n)

lemma exists_bound_of_forall2 {P : Fin 2 → Fin 2 → ℝ → Prop}
    (h : ∀ i j, ∃ C, P i j C) (hmono : ∀ i j C C', C ≤ C' → P i j C → P i j C') :
    ∃ C, ∀ i j, P i j C := by
  choose C hC using h
  refine ⟨∑ i, ∑ j, |C i j|, fun i j => hmono i j _ _ ?_ (hC i j)⟩
  calc C i j ≤ |C i j| := le_abs_self _
    _ ≤ ∑ j', |C i j'| := Finset.single_le_sum (f := fun j' => |C i j'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |C i' j'| := Finset.single_le_sum (f := fun i' => ∑ j', |C i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- **Uniform convergence of the splitting** for a cell solution: the split operator with `n`
steps applied to `e_ξ` is within `C n^{-β/2}` of `h(1)`. -/
theorem split_cell_uniform (cf : ControlFamily L M S) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (w : BlockParam L) (ξ : Pt 2) {h : ℝ → Pt 2 → ℂ}
    (hcell : IsCellSolution (dampedB cf μ w) μ ξ h) :
    ∃ C β : ℝ, 0 < β ∧ ∀ n : ℕ, 1 ≤ n → ∀ y,
      ‖splitOp μ n (canonPsi cf μ w n) n (expChar ξ) y - h 1 y‖ ≤ C * (n : ℝ) ^ (-(β / 2)) := by
  obtain ⟨β, hβ0, hβ1, hreg⟩ := hcell.regular
  obtain ⟨D0, hD0⟩ := hreg.bdd
  obtain ⟨D1, hD1⟩ : ∃ C, ∀ t ∈ Icc (0:ℝ) 1, ∀ j x, ‖pd j (h t) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := exists_bound_of_forall2 (P := fun i _ C =>
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖pd i (h t) x‖ ≤ C) (fun i _ => hreg.bdd_d1 i)
      (fun i j C C' hCC' hP t ht x => (hP t ht x).trans hCC')
    exact ⟨C, fun t ht j x => hC j 0 t ht x⟩
  obtain ⟨D2, hD2⟩ : ∃ C, ∀ t ∈ Icc (0:ℝ) 1, ∀ i j x, ‖pd i (pd j (h t)) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := exists_bound_of_forall2 (P := fun i j C =>
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖pd i (pd j (h t)) x‖ ≤ C) (fun i j => hreg.bdd_d2 i j)
      (fun i j C C' hCC' hP t ht x => (hP t ht x).trans hCC')
    exact ⟨C, fun t ht i j x => hC i j t ht x⟩
  obtain ⟨H, hHpar⟩ : ∃ C, ∀ i j, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ x y,
      ‖pd i (pd j (h t)) x - pd i (pd j (h s)) y‖ ≤ C * (‖x - y‖ ^ β + |t - s| ^ (β / 2)) := by
    refine exists_bound_of_forall2 (P := fun i j C => ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1,
      ∀ x y, ‖pd i (pd j (h t)) x - pd i (pd j (h s)) y‖ ≤
        C * (‖x - y‖ ^ β + |t - s| ^ (β / 2))) (fun i j => hreg.holder_d2 i j) ?_
    intro i j C C' hCC' hP t ht s hs x y
    exact (hP t ht s hs x y).trans (by gcongr)
  have hH : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j x y,
      ‖pd i (pd j (h t)) x - pd i (pd j (h t)) y‖ ≤ H * ‖x - y‖ ^ β := by
    intro t ht i j x y
    have := hHpar i j t ht t ht x y
    rwa [sub_self, abs_zero, Real.zero_rpow (by linarith), add_zero] at this
  obtain ⟨Hd, hHd⟩ := hreg.holder_dt
  have hdt : ∀ x, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt (fun s => h s x) (dt 1 h t x) (Icc 0 1) t :=
    fun x t ht => (hreg.diff_t x t ht).hasDerivWithinAt
  set κ := μ / (4 * π ^ 2) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg hμ.1 (by positivity)
  have hκ1 : κ ≤ 1 / 2 := by
    rw [hκ, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, hμ.2]
  have hV := splitField_good cf hμ w
  have heq : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      dt 1 h t x + conv (splitField cf μ w t) (h t) x = κ • lap (h t) x := by
    intro t ht x
    rw [splitField_eq_of_mem cf μ w ht]
    exact hcell.eqn t ht x
  have hLt0 : 0 ≤ splitLt cf := by
    have := coefDerivBound_nonneg cf; have := coefBound_nonneg cf
    simp only [splitLt]; positivity
  obtain ⟨Cst, hCst⟩ := cell_local_error_rate hV hLt0 (splitField_time_lip cf hμ w) hβ0
    hβ1.le hκ1 hreg.smooth_x hD0 hD1 hD2 hH hdt hHd heq
  -- threshold for the step size
  set K : ℝ := (splitK cf : ℝ) with hK
  have hK0 : 0 ≤ K := (splitK cf).2
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (K * Real.exp K)
  have hD00 : 0 ≤ D0 := (norm_nonneg _).trans (hD0 0 ⟨le_rfl, zero_le_one⟩ 0)
  have hψc : ∀ n i, Continuous (canonPsi cf μ w n i) := fun n i => hV.continuous_gflow _ _
  have hmemj : ∀ n j : ℕ, 1 ≤ n → j ≤ n → (j : ℝ) / n ∈ Icc (0:ℝ) 1 := by
    intro n j hn hj
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    refine ⟨by positivity, (div_le_one hn').2 (by exact_mod_cast hj)⟩
  refine ⟨max Cst 0 + (1 + D0) * (N₀ : ℝ) ^ (β / 2), β, hβ0, fun n hn y => ?_⟩
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 ≤ (n : ℝ) ^ (-(β / 2)) := by positivity
  have hP := splitOp_cont_bdd μ n (hψc n) (continuous_expChar ξ)
    (fun x => (norm_expChar ξ x).le) n
  rcases lt_or_ge n N₀ with hsmall | hlarge
  · -- few steps: crude bound
    have h1 : ‖splitOp μ n (canonPsi cf μ w n) n (expChar ξ) y - h 1 y‖ ≤ 1 + D0 :=
      (norm_sub_le _ _).trans (add_le_add (hP.2 y) (hD0 1 ⟨zero_le_one, le_rfl⟩ y))
    refine h1.trans ?_
    have h2 : 1 ≤ (N₀ : ℝ) ^ (β / 2) * (n : ℝ) ^ (-(β / 2)) := by
      rw [Real.rpow_neg hn'.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow hn'.le (by exact_mod_cast hsmall.le) (by linarith)
    calc 1 + D0 ≤ (1 + D0) * ((N₀ : ℝ) ^ (β / 2) * (n : ℝ) ^ (-(β / 2))) := by
          nlinarith
      _ ≤ (max Cst 0 + (1 + D0) * (N₀ : ℝ) ^ (β / 2)) * (n : ℝ) ^ (-(β / 2)) := by
          have := le_max_right Cst 0
          nlinarith
  · -- many steps: telescoping the local errors
    have hstep : ∀ j : ℕ, j < n → ∀ y,
        ‖heatOp (splitVar μ n) (h (j / n) ∘ canonPsi cf μ w n (j + 1)) y -
          h ((j + 1 : ℕ) / n) y‖ ≤ Cst * (1 / (n : ℝ)) ^ (1 + β / 2) := by
      intro j hj y
      have ht1 : ((j + 1 : ℕ) : ℝ) / n - (j : ℝ) / n = 1 / n := by
        push_cast; field_simp; ring
      have hpsi : canonPsi cf μ w n (j + 1) = gflow (splitField cf μ w) (((j + 1 : ℕ) : ℝ) / n)
          ((j : ℝ) / n) := by
        simp only [canonPsi]; congr 2; push_cast; ring
      rw [hpsi]
      have key := hCst ((j : ℝ) / n) (((j + 1 : ℕ) : ℝ) / n) (hmemj n j hn hj.le).1
        (by rw [← sub_nonneg, ht1]; positivity) (hmemj n (j + 1) hn hj).2 ?_ (splitVar μ n)
        ?_ y
      · rwa [ht1] at key
      · rw [ht1]
        have e1 : Real.exp (K * (1 / n)) ≤ Real.exp K := by
          gcongr
          exact mul_le_of_le_one_right hK0 ((div_le_one hn').2 hn1)
        calc K * (1 / (n : ℝ)) * Real.exp (K * (1 / n)) ≤ K * (1 / n) * Real.exp K := by gcongr
          _ = K * Real.exp K / n := by ring
          _ ≤ 1 := by
            rw [div_le_one hn']
            exact hN₀.trans (by exact_mod_cast hlarge)
      · rw [ht1, splitVar, Real.coe_toNNReal _ (by positivity)]
        ring
    have herr := splitOp_error_le μ n (hψc n) (D0 := D0)
      (fun j hj => (hreg.smooth_x _ (hmemj n j hn hj)).continuous)
      (fun j hj => hD0 _ (hmemj n j hn hj)) (continuous_expChar ξ)
      (fun x => (norm_expChar ξ x).le) hcell.init.symm hstep n le_rfl y
    have hnn : (n : ℝ) / n = 1 := div_self hn'.ne'
    rw [hnn] at herr
    refine herr.trans ?_
    have e : (n : ℝ) * (Cst * (1 / (n : ℝ)) ^ (1 + β / 2)) = Cst * (n : ℝ) ^ (-(β / 2)) := by
      rw [one_div, Real.inv_rpow hn'.le, ← Real.rpow_neg hn'.le]
      calc (n : ℝ) * (Cst * (n : ℝ) ^ (-(1 + β / 2))) =
            Cst * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 + β / 2))) := by rw [Real.rpow_one]; ring
        _ = Cst * (n : ℝ) ^ (-(β / 2)) := by
            rw [← Real.rpow_add hn']; congr 2; ring
    rw [e]
    have h3 : Cst ≤ max Cst 0 + (1 + D0) * (N₀ : ℝ) ^ (β / 2) := by
      have := le_max_left Cst 0
      have : 0 ≤ (1 + D0) * (N₀ : ℝ) ^ (β / 2) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right h3 hpos

end AnomDiss
