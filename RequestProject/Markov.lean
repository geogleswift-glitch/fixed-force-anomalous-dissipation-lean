module

public import RequestProject.Linfty
public import RequestProject.EmbeddingCalc

/-!
# Section 7: averaged Fourier-energy recursion

Fourier coefficients and Parseval's identity on `𝕋²`, the physical pulse operators, their
averaged kernels, the initial frequency, and the abstract weighted energy recursion.  The
averaged terminal estimate, the phase selection and the embedding into three dimensions are in
`RequestProject.Selection`.

Solution operators are defined by choosing (with `Classical.epsilon`) a classical solution;
under `ExternalScalar` such a solution exists and is unique, so these definitions agree with the
paper's operators whenever they are used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss


/-- The physical pulse operator `T_{j,N}^{ω_j}` across `I_j` applied to `h`: the value at time
`s_j + δ_j` of the solution of `∂ₜϑ + V_j^{ν_N}·∇ϑ = ν_NΔϑ` with value `h` at time `s_j`
(Definition 7.1). -/
def pulseOp (N j : ℕ) (b : BlockParam L₀) (h : Pt 2 → ℂ) : Pt 2 → ℂ :=
  Classical.epsilon fun out => ∃ θ : ℝ → Pt 2 → ℂ,
    IsClassicalScalar (δs j) (nuN N) (fun t => VpulseB (nuN N) j b (sj j + t)) h θ ∧
      θ (δs j) = out

/-- The matrix entry `⟨T_{j,N}^{ω_j} e_ℓ, e_m⟩`. -/
def pulseEntry (N j : ℕ) (b : BlockParam L₀) (ℓ m : Fin 2 → ℤ) : ℂ :=
  fc (pulseOp N j b (expChar (intVec ℓ))) m

/-- The squared heat multiplier `d_{j,N}(m) = e^{-8π²ν_Nη_j|m|²}` across `J_j`. -/
def heatFactor (N j : ℕ) (m : Fin 2 → ℤ) : ℝ :=
  Real.exp (-(8 * π ^ 2 * nuN N * ηs j * euclNorm (intVec m) ^ 2))

/- **Lemma 7.2** (residue classes) is stated and proved as `residue_classes` in
`RequestProject/Residue.lean`. -/

/- **Lemma 7.3** (phase diagonalization) is used inside the proof of `kernel_properties` in
`RequestProject/Kernel.lean`. -/

/-- The averaged kernel `K_{j,N}(ℓ,m) = 𝔼_{ω_j}|⟨T_{j,N}^{ω_j}e_ℓ, e_m⟩|²` (Definition 7.4). -/
def kernelK (N j : ℕ) (ℓ m : Fin 2 → ℤ) : ℝ :=
  ∫ b, ‖pulseEntry N j b ℓ m‖ ^ 2 ∂(blockMeasure L₀)

/-- The comparison scalar of Definition 5.5 (chosen; unique under `ExternalScalar`). -/
def compScalar (N : ℕ) (w : Phase) (θ₀ : Pt 2 → ℝ) : ℝ → Pt 2 → ℝ :=
  Classical.epsilon (IsComparisonScalar N w θ₀)

/- **Lemma 7.5** (kernel properties) is stated and proved as `kernel_properties` in
`RequestProject/Kernel.lean`. -/

/-! ### Lemma 7.6: the initial frequency and the initial scalar -/

/-- The initial frequency `ℓ₀ = (n, 0)` with `n` so large that `W_{k_1}(ℓ₀) ≤ ε/8`. -/
def ell0 (ε : ℝ) : Fin 2 → ℤ :=
  ![(⌈Rε ε * kk 1 * (8 / ε) ^ (1 / σ₀)⌉₊ + 1 : ℕ), 0]

/-- The initial scalar `θ₀(x) = √2 cos(2π ℓ₀·x)`. -/
def theta0 (ε : ℝ) (x : Pt 2) : ℝ := Real.sqrt 2 * Real.cos (2 * π * dot (intVec (ell0 ε)) x)

lemma integral_unit_exp (k : ℤ) :
    ∫ t in Icc (0:ℝ) 1, Complex.exp (2 * π * Complex.I * k * t) = if k = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hk
  · simp [hk]
  · have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hk]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * π * Complex.I * k * ((1:ℝ):ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one, show (2 * π * Complex.I * k : ℂ) = k * (2 * π * Complex.I)
        by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [this]; simp

lemma restrict_cell_eq_pi :
    (volume : Measure (Pt 2)).restrict (cell 2) =
      Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Icc 0 1)) := by
  have hcell : cell 2 = Set.univ.pi (fun _ : Fin 2 => Icc (0:ℝ) 1) := by
    rw [cell, ← Set.pi_univ_Icc]; rfl
  rw [hcell, volume_pi, Measure.restrict_pi_pi]


lemma integral_cell_expChar (m : Fin 2 → ℤ) :
    ∫ x in cell 2, expChar (intVec m) x = if m = 0 then 1 else 0 := by
  simp_rw [expChar_intVec_eq_prod]
  rw [restrict_cell_eq_pi, integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * m i * t))]
  simp only [integral_unit_exp, Fin.prod_univ_two]
  have hm : m = 0 ↔ m 0 = 0 ∧ m 1 = 0 := ⟨fun h => by simp [h], fun ⟨h0, h1⟩ => by
    funext i; fin_cases i <;> simp [h0, h1]⟩
  by_cases h0 : m 0 = 0 <;> by_cases h1 : m 1 = 0 <;> simp [hm, h0, h1]


lemma intVec_add' (m n : Fin 2 → ℤ) : intVec (m + n) = intVec m + intVec n := by
  funext i; simp [intVec]

lemma intVec_neg (m : Fin 2 → ℤ) : intVec (-m) = -intVec m := by
  funext i; simp [intVec]



lemma theta0_complex (ε : ℝ) (x : Pt 2) :
    ((theta0 ε x : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
      (expChar (intVec (ell0 ε)) x + expChar (intVec (-ell0 ε)) x) := by
  rw [theta0, intVec_neg, expChar, expChar]
  have hd : dot (-intVec (ell0 ε)) x = -dot (intVec (ell0 ε)) x := by
    simp [dot, Finset.sum_neg_distrib]
  rw [hd]
  push_cast
  rw [Complex.cos]
  ring_nf

lemma fc_theta0 (ε : ℝ) (ℓ : Fin 2 → ℤ) :
    fc (fun x => (theta0 ε x : ℂ)) ℓ = ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
      ((if ell0 ε - ℓ = 0 then 1 else 0) + (if -ell0 ε - ℓ = 0 then 1 else 0)) := by
  rw [fc]
  have e : ∀ x, ((theta0 ε x : ℝ) : ℂ) * expChar (-intVec ℓ) x = ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
      (expChar (intVec (ell0 ε - ℓ)) x + expChar (intVec (-ell0 ε - ℓ)) x) := by
    intro x
    rw [theta0_complex, mul_assoc, add_mul, expChar_mul, expChar_mul, sub_eq_add_neg,
      sub_eq_add_neg, intVec_add', intVec_add', intVec_neg, intVec_neg ℓ]
  simp_rw [e]
  have hi : ∀ m, IntegrableOn (expChar (intVec m)) (cell 2) :=
    fun m => (continuous_expChar _).continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_const_mul, integral_add (hi _) (hi _), integral_cell_expChar, integral_cell_expChar]


lemma ell0_ne_zero (ε : ℝ) : ell0 ε ≠ 0 := by
  intro h
  have := congr_fun h 0
  simp [ell0] at this
  omega

lemma ell0_ne_neg (ε : ℝ) : ell0 ε ≠ -ell0 ε := by
  intro h
  have := congr_fun h 0
  simp [ell0] at this
  omega

lemma normSq_fc_theta0 (ε : ℝ) (ℓ : Fin 2 → ℤ) :
    ‖fc (fun x => (theta0 ε x : ℂ)) ℓ‖ ^ 2 = if ℓ = ell0 ε ∨ ℓ = -ell0 ε then 1 / 2 else 0 := by
  rw [fc_theta0]
  have h2 : ‖((Real.sqrt 2 / 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne := ell0_ne_neg ε
  have hne0 := ell0_ne_zero ε
  by_cases h1 : ℓ = ell0 ε
  · subst h1
    have : ¬ (-ell0 ε - ell0 ε = 0) := fun h => hne (neg_eq_iff_eq_neg.1 (sub_eq_zero.1 h))
    rw [if_pos (sub_self _), if_neg this, add_zero, mul_one, h2, if_pos (Or.inl rfl)]
  · by_cases h3 : ℓ = -ell0 ε
    · subst h3
      have : ¬ (ell0 ε - -ell0 ε = 0) := fun h => hne (sub_eq_zero.1 h)
      rw [if_neg this, if_pos (sub_self _), zero_add, mul_one, h2, if_pos (Or.inr rfl)]
    · have a1 : ¬ (ell0 ε - ℓ = 0) := fun h => h1 (sub_eq_zero.1 h).symm
      have a2 : ¬ (-ell0 ε - ℓ = 0) := fun h => h3 (sub_eq_zero.1 h).symm
      simp [a1, a2, h1, h3]


lemma weight_ell0_le (ε : ℝ) (hε0 : 0 < ε) :
    weightW σ₀ (Rε ε) (kk 1) (intVec (ell0 ε)) ≤ ε / 8 := by
  have ha0 : 0 ≤ Rε ε * kk 1 := mul_nonneg (le_trans (Real.sqrt_nonneg _) (le_max_right _ _))
    (by unfold kk; positivity)
  have hb0 : 0 < (8 / ε) ^ (1 / σ₀) := by positivity
  set n0 : ℕ := ⌈Rε ε * kk 1 * (8 / ε) ^ (1 / σ₀)⌉₊ + 1 with hn0
  have hell : ell0 ε = ![(n0 : ℤ), 0] := rfl
  have hn0pos : (0 : ℝ) < n0 := by positivity
  have hnorm : euclNorm (intVec (ell0 ε)) = n0 := by
    rw [hell]; simp [euclNorm, intVec, Fin.sum_univ_two]
  have hlt : Rε ε * kk 1 * (8 / ε) ^ (1 / σ₀) < n0 := by
    rw [hn0]; push_cast; linarith [Nat.le_ceil (Rε ε * kk 1 * (8 / ε) ^ (1 / σ₀))]
  have hne : intVec (ell0 ε) ≠ 0 := by
    intro h
    have := congr_fun h 0
    rw [hell] at this
    simp [intVec] at this
  rw [weightW, if_neg hne, hnorm]
  refine (min_le_right _ _).trans ?_
  have h1 : Rε ε * kk 1 / n0 ≤ 1 / (8 / ε) ^ (1 / σ₀) := by
    rw [div_le_div_iff₀ hn0pos hb0]; linarith
  calc (Rε ε * kk 1 / n0) ^ σ₀ ≤ (1 / (8 / ε) ^ (1 / σ₀)) ^ σ₀ :=
        Real.rpow_le_rpow (div_nonneg ha0 hn0pos.le) h1 σ₀_pos.le
    _ = ε / 8 := by
        rw [Real.div_rpow zero_le_one hb0.le, Real.one_rpow, ← Real.rpow_mul (by positivity),
          one_div_mul_cancel σ₀_pos.ne', Real.rpow_one]
        field_simp


lemma theta0_contDiff (ε : ℝ) : ContDiff ℝ ∞ (theta0 ε) := by
  unfold theta0 dot
  fun_prop

lemma theta0_periodic (ε : ℝ) : IsPeriodic (theta0 ε) := by
  intro x n
  unfold theta0
  congr 1
  have : dot (intVec (ell0 ε)) (x + intVec n) =
      dot (intVec (ell0 ε)) x + ((∑ i, ell0 ε i * n i : ℤ) : ℝ) := by
    simp [dot, intVec, mul_add, Finset.sum_add_distrib]
  rw [this, mul_add, mul_comm (2 * π) ((∑ i, ell0 ε i * n i : ℤ) : ℝ)]
  exact Real.cos_add_int_mul_two_pi _ _

/-- **Lemma 7.6** (initial frequency).  `ℓ₀ ≠ 0`, `W_{k_1}(ℓ₀) ≤ ε/8`; `θ₀` is real, smooth,
periodic, `‖θ₀‖₂ = 1`, `‖θ₀‖_∞ = √2`, and its Fourier energy is `1/2` at each of `±ℓ₀`. -/
theorem initial_frequency (ε : ℝ) (hε0 : 0 < ε) :
    ell0 ε ≠ 0 ∧ weightW σ₀ (Rε ε) (kk 1) (intVec (ell0 ε)) ≤ ε / 8 ∧
    ContDiff ℝ ∞ (theta0 ε) ∧ IsPeriodic (theta0 ε) ∧ l2sq (theta0 ε) = 1 ∧
    (∀ x, |theta0 ε x| ≤ Real.sqrt 2) ∧ theta0 ε 0 = Real.sqrt 2 ∧
    ∀ ℓ, ‖fc (fun x => (theta0 ε x : ℂ)) ℓ‖ ^ 2 =
      if ℓ = ell0 ε ∨ ℓ = -ell0 ε then 1 / 2 else 0 := by
  refine ⟨ell0_ne_zero ε, weight_ell0_le ε hε0, theta0_contDiff ε, theta0_periodic ε, ?_, ?_, ?_,
    normSq_fc_theta0 ε⟩
  · have hp := parseval_cell (theta0 ε) (theta0_contDiff ε).continuous (theta0_periodic ε)
    simp_rw [normSq_fc_theta0] at hp
    have hs : HasSum (fun ℓ : Fin 2 → ℤ => if ℓ = ell0 ε ∨ ℓ = -ell0 ε then (1 / 2 : ℝ) else 0)
        1 := by
      have := (hasSum_ite_eq (ell0 ε) (1 / 2 : ℝ)).add (hasSum_ite_eq (-ell0 ε) (1 / 2 : ℝ))
      rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at this
      refine this.congr_fun fun ℓ => ?_
      by_cases h1 : ℓ = ell0 ε
      · subst h1; simp [ell0_ne_neg]
      · by_cases h2 : ℓ = -ell0 ε
        · subst h2; simp [(ell0_ne_neg ε).symm]
        · simp [h1, h2]
    exact hp.unique hs
  · intro x
    unfold theta0
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_cos_le_one _)
  · simp [theta0, dot]

/-- If `|v| < Rk` then `W_k(v) = 1`. -/
lemma weightW_eq_one {σ R k : ℝ} (hσ : 0 < σ) (v : Pt 2)
    (hv : euclNorm v < R * k) : weightW σ R k v = 1 := by
  unfold weightW
  split_ifs with h
  · rfl
  · have hpos : 0 < euclNorm v := by
      unfold euclNorm
      apply Real.sqrt_pos.2
      by_contra hc
      push_neg at hc
      apply h
      have h0 : ∑ i, v i ^ 2 = 0 := le_antisymm hc (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 h0 i (Finset.mem_univ _)
      simpa using this
    have h1 : 1 < R * k / euclNorm v := by rw [one_lt_div hpos]; exact hv
    have h2 : 1 ≤ (R * k / euclNorm v) ^ σ := Real.one_le_rpow h1.le hσ.le
    exact min_eq_left h2

/-- **Lemma 7.7** (weighted energy recursion), in `[0,∞]`-valued form.  If `p₀ ≥ 0` has total
mass `≤ 1` and vanishes on `|ℓ| < Rk_1`, the kernels are substochastic and satisfy the drift
condition, `0 ≤ d_{j,N} ≤ 1`, `d_{N,N} ≤ ρ` on `|m| ≥ Rk_{N+1}`, and
`p_j(m) = d_{j,N}(m) ∑_ℓ K_{j,N}(ℓ,m) p_{j-1}(ℓ)`, then
`∑ₘ p_N(m) ≤ ½ ∑_ℓ W_{k_1}(ℓ) p₀(ℓ) + ρ`. -/
theorem weighted_energy_recursion (σ R : ℝ) (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    (K : ℕ → (Fin 2 → ℤ) → (Fin 2 → ℤ) → ℝ≥0∞) (dd : ℕ → (Fin 2 → ℤ) → ℝ≥0∞)
    (p : ℕ → (Fin 2 → ℤ) → ℝ≥0∞) (ρ : ℝ≥0∞)
    (hK : ∀ j, 1 ≤ j → j ≤ N → ∀ ℓ, ∑' m, K j ℓ m ≤ 1)
    (hdrift : ∀ j, 1 ≤ j → j ≤ N → ∀ ℓ, R * kk j ≤ euclNorm (intVec ℓ) →
      ∑' m, ENNReal.ofReal (weightW σ R (kk (j + 1)) (intVec m)) * K j ℓ m ≤
        ENNReal.ofReal (weightW σ R (kk j) (intVec ℓ)) / 2)
    (hd : ∀ j, 1 ≤ j → j ≤ N → ∀ m, dd j m ≤ 1)
    (hp0 : ∑' ℓ, p 0 ℓ ≤ 1) (hp0low : ∀ ℓ, euclNorm (intVec ℓ) < R * kk 1 → p 0 ℓ = 0)
    (hrec : ∀ j, 1 ≤ j → j ≤ N → ∀ m, p j m = dd j m * ∑' ℓ, K j ℓ m * p (j - 1) ℓ)
    (hlast : ∀ m, R * kk (N + 1) ≤ euclNorm (intVec m) → dd N m ≤ ρ) :
    ∑' m, p N m ≤ (∑' ℓ, ENNReal.ofReal (weightW σ R (kk 1) (intVec ℓ)) * p 0 ℓ) / 2 + ρ := by
  classical
  -- notation
  let hi : ℕ → (Fin 2 → ℤ) → Prop := fun j m => R * kk j ≤ euclNorm (intVec m)
  let W : ℕ → (Fin 2 → ℤ) → ℝ≥0∞ := fun j m => ENNReal.ofReal (weightW σ R (kk j) (intVec m))
  have hWlow : ∀ j m, ¬ hi j m → W j m = 1 := by
    intro j m h
    simp only [W, hi] at h ⊢
    rw [weightW_eq_one hσ _ (not_le.1 h), ENNReal.ofReal_one]
  -- the high-frequency part
  let q : ℕ → (Fin 2 → ℤ) → ℝ≥0∞ := fun j => Nat.rec (motive := fun _ => (Fin 2 → ℤ) → ℝ≥0∞)
    (p 0) (fun j qj m => if hi (j + 2) m then dd (j + 1) m * ∑' ℓ, K (j + 1) ℓ m * qj ℓ else 0) j
  have hq0 : q 0 = p 0 := rfl
  have hqs : ∀ j m, q (j + 1) m =
      if hi (j + 2) m then dd (j + 1) m * ∑' ℓ, K (j + 1) ℓ m * q j ℓ else 0 := fun j m => rfl
  -- the removed part
  let u : ℕ → (Fin 2 → ℤ) → ℝ≥0∞ := fun j => Nat.rec (motive := fun _ => (Fin 2 → ℤ) → ℝ≥0∞)
    0 (fun j uj m => dd (j + 1) m * (∑' ℓ, K (j + 1) ℓ m * uj ℓ) +
      (if hi (j + 2) m then 0 else dd (j + 1) m * ∑' ℓ, K (j + 1) ℓ m * q j ℓ)) j
  have hu0 : u 0 = 0 := rfl
  have hus : ∀ j m, u (j + 1) m = dd (j + 1) m * (∑' ℓ, K (j + 1) ℓ m * u j ℓ) +
      (if hi (j + 2) m then 0 else dd (j + 1) m * ∑' ℓ, K (j + 1) ℓ m * q j ℓ) := fun j m => rfl
  -- Claim A
  have hA : ∀ j, j ≤ N → ∀ m, p j m = q j m + u j m := by
    intro j
    induction j with
    | zero => intro _ m; simp [hq0, hu0]
    | succ j ih =>
      intro hj m
      rw [hrec (j + 1) (by omega) hj m, Nat.add_sub_cancel, hqs, hus]
      have : (fun ℓ => K (j + 1) ℓ m * p j ℓ) =
          fun ℓ => K (j + 1) ℓ m * q j ℓ + K (j + 1) ℓ m * u j ℓ := by
        funext ℓ; rw [ih (by omega) ℓ, mul_add]
      rw [this, ENNReal.tsum_add, mul_add]
      split_ifs <;> ring
  -- support of q
  have hS : ∀ j ℓ, ¬ hi (j + 1) ℓ → q j ℓ = 0 := by
    intro j ℓ h
    cases j with
    | zero => exact hp0low ℓ (not_le.1 h)
    | succ j => rw [hqs]; simp [h]
  let a : ℕ → ℝ≥0∞ := fun j => ∑' m, W (j + 1) m * q j m
  let b : ℕ → ℝ≥0∞ := fun j => ∑' m, (if hi (j + 2) m then 0 else ∑' ℓ, K (j + 1) ℓ m * q j ℓ)
  -- Claim B
  have hB : ∀ j, j + 1 ≤ N → b j + a (j + 1) ≤ a j / 2 := by
    intro j hj
    simp only [a, b]
    rw [← ENNReal.tsum_add]
    calc ∑' m, ((if hi (j + 2) m then 0 else ∑' ℓ, K (j + 1) ℓ m * q j ℓ) +
          W (j + 1 + 1) m * q (j + 1) m)
        ≤ ∑' m, W (j + 2) m * ∑' ℓ, K (j + 1) ℓ m * q j ℓ := by
          refine ENNReal.tsum_le_tsum (fun m => ?_)
          rw [hqs]
          by_cases h : hi (j + 2) m
          · simp only [h, if_true, zero_add]
            rw [← mul_assoc, mul_comm (W _ m), mul_assoc]
            exact mul_le_of_le_one_left zero_le (hd (j + 1) (by omega) hj m)
          · simp only [h, if_false, mul_zero, add_zero, hWlow (j + 2) m h, one_mul]
            exact le_rfl
      _ = ∑' ℓ, q j ℓ * ∑' m, W (j + 2) m * K (j + 1) ℓ m := by
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          congr 1; funext ℓ; congr 1; funext m; ring
      _ ≤ ∑' ℓ, q j ℓ * (W (j + 1) ℓ / 2) := by
          refine ENNReal.tsum_le_tsum (fun ℓ => ?_)
          by_cases h : hi (j + 1) ℓ
          · exact mul_le_mul_right (hdrift (j + 1) (by omega) hj ℓ h) _
          · rw [hS j ℓ h]; simp
      _ = (∑' m, W (j + 1) m * q j m) / 2 := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.tsum_mul_left]
          congr 1; funext ℓ; rw [ENNReal.div_eq_inv_mul]; ring
  -- Claim C
  have hC : ∀ j, j ≤ N → ∑' m, u j m ≤ ∑ i ∈ Finset.range j, b i := by
    intro j
    induction j with
    | zero => intro _; simp [hu0]
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ]
      calc ∑' m, u (j + 1) m
          ≤ ∑' m, ((∑' ℓ, K (j + 1) ℓ m * u j ℓ) +
              (if hi (j + 2) m then 0 else ∑' ℓ, K (j + 1) ℓ m * q j ℓ)) := by
            refine ENNReal.tsum_le_tsum (fun m => ?_)
            rw [hus]
            gcongr
            · exact mul_le_of_le_one_left zero_le (hd (j + 1) (by omega) hj m)
            · split_ifs
              · exact le_rfl
              · exact mul_le_of_le_one_left zero_le (hd (j + 1) (by omega) hj m)
        _ = (∑' ℓ, u j ℓ * ∑' m, K (j + 1) ℓ m) + b j := by
            rw [ENNReal.tsum_add]
            congr 1
            simp_rw [← ENNReal.tsum_mul_left]
            rw [ENNReal.tsum_comm]
            congr 1; funext ℓ; congr 1; funext m; ring
        _ ≤ (∑' ℓ, u j ℓ) + b j := by
            gcongr with ℓ
            exact mul_le_of_le_one_right zero_le (hK (j + 1) (by omega) hj ℓ)
        _ ≤ _ := by gcongr; exact ih (by omega)
  -- Claim D
  have hD : ∀ j, j ≤ N → ∑' m, q j m ≤ 1 := by
    intro j
    induction j with
    | zero => intro _; rw [hq0]; exact hp0
    | succ j ih =>
      intro hj
      calc ∑' m, q (j + 1) m ≤ ∑' m, ∑' ℓ, K (j + 1) ℓ m * q j ℓ := by
            refine ENNReal.tsum_le_tsum (fun m => ?_)
            rw [hqs]
            split_ifs
            · exact mul_le_of_le_one_left zero_le (hd (j + 1) (by omega) hj m)
            · exact zero_le
        _ = ∑' ℓ, q j ℓ * ∑' m, K (j + 1) ℓ m := by
            rw [ENNReal.tsum_comm]
            congr 1; funext ℓ; rw [← ENNReal.tsum_mul_left]; congr 1; funext m; ring
        _ ≤ ∑' ℓ, q j ℓ := by
            gcongr with ℓ
            exact mul_le_of_le_one_right zero_le (hK (j + 1) (by omega) hj ℓ)
        _ ≤ 1 := ih (by omega)
  -- Claim D'
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hD' : ∑' m, q (n + 1) m ≤ ρ := by
    calc ∑' m, q (n + 1) m ≤ ∑' m, ρ * ∑' ℓ, K (n + 1) ℓ m * q n ℓ := by
          refine ENNReal.tsum_le_tsum (fun m => ?_)
          rw [hqs]
          split_ifs with h
          · exact mul_le_mul_left (hlast m h) _
          · exact zero_le
      _ = ρ * ∑' ℓ, q n ℓ * ∑' m, K (n + 1) ℓ m := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
          congr 2; funext ℓ; rw [← ENNReal.tsum_mul_left]; congr 1; funext m; ring
      _ ≤ ρ * ∑' ℓ, q n ℓ := by
          gcongr with ℓ
          exact mul_le_of_le_one_right zero_le (hK (n + 1) (by omega) le_rfl ℓ)
      _ ≤ ρ * 1 := by gcongr; exact hD n (by omega)
      _ = ρ := mul_one ρ
  -- Claim E
  have hE : ∀ j, 1 ≤ j → j ≤ n + 1 → ∑ i ∈ Finset.range j, b i + a j ≤ a 0 / 2 := by
    intro j hj1
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simpa using hB 0 hj
      · rw [Finset.sum_range_succ, add_assoc]
        calc ∑ i ∈ Finset.range j, b i + (b j + a (j + 1))
            ≤ ∑ i ∈ Finset.range j, b i + a j / 2 := by gcongr; exact hB j hj
          _ ≤ ∑ i ∈ Finset.range j, b i + a j := by gcongr; exact ENNReal.half_le_self
          _ ≤ a 0 / 2 := ih hjpos (by omega)
  -- conclusion
  calc ∑' m, p (n + 1) m = ∑' m, (q (n + 1) m + u (n + 1) m) := by
        congr 1; funext m; exact hA (n + 1) le_rfl m
    _ = ∑' m, q (n + 1) m + ∑' m, u (n + 1) m := ENNReal.tsum_add
    _ ≤ ρ + ∑ i ∈ Finset.range (n + 1), b i := add_le_add hD' (hC (n + 1) le_rfl)
    _ ≤ ρ + a 0 / 2 := by
        gcongr
        exact le_trans le_self_add (hE (n + 1) (by omega) le_rfl)
    _ = _ := by rw [add_comm]; simp [a, W, hq0]

end AnomDiss
