module

public import RequestProject.DiffusiveFourier
public import RequestProject.NegMoment
public import RequestProject.ControlsFinal

/-!
# Section 4: global parameters, probability space, and fixed forcing

All global parameters of Definition 4.1 are fixed here, once and for all, by choosing witnesses
of the existence statements of Section 2 and Section 3 (`q = 3`, `σ`, `L`, `S_a`, `Λ`, `M`,
`μ_*`, `R₀`).  The parameter `R` depends on `ε` (`Rε`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-! ### Definition 4.1: global parameters -/

/-- `q = 3`. -/
def qq : ℕ := 3

lemma qq_ge : 3 ≤ qq := le_rfl

/-- The exponent `σ` supplied by Lemma 2.5 for `q = 3`. -/
def σ₀ : ℝ := Classical.choose (lemma_negative qq qq_ge)

/-- The block length `L` supplied by Lemma 2.5 for `q = 3`. -/
def L₀ : ℕ := Classical.choose (Classical.choose_spec (lemma_negative qq qq_ge)).2.2

lemma σ₀_pos : 0 < σ₀ := (Classical.choose_spec (lemma_negative qq qq_ge)).1

lemma σ₀_lt_one : σ₀ < 1 := (Classical.choose_spec (lemma_negative qq qq_ge)).2.1

lemma L₀_pos : 1 ≤ L₀ :=
  (Classical.choose_spec (Classical.choose_spec (lemma_negative qq qq_ge)).2.2).1

lemma negMoment₀ : NegMomentBound qq σ₀ L₀ :=
  (Classical.choose_spec (Classical.choose_spec (lemma_negative qq qq_ge)).2.2).2

/-- The spatial bounds `S_a` of Lemma 2.13. -/
def S₀ : ℕ → ℝ := Classical.choose (controls_exist L₀)

lemma S₀_nonneg (a : ℕ) : 0 ≤ S₀ a := (Classical.choose_spec (controls_exist L₀)).1 a

/-- `Λ = 2 S_1`. -/
def Λ₀ : ℝ := 2 * S₀ 1

/-- The number `M` of vanishing moments, chosen so that `(2M+1) log q > Λ`. -/
def M₀ : ℕ := ⌈Λ₀ / Real.log 3⌉₊ + 1

lemma M₀_pos : 1 ≤ M₀ := by unfold M₀; omega

/-- The control family of Lemma 2.13 with `M = M₀` vanishing moments. -/
def cf₀ : ControlFamily L₀ M₀ S₀ :=
  Classical.choice ((Classical.choose_spec (controls_exist L₀)).2 M₀ M₀_pos)

/-- `μ_*` from Proposition 3.11. -/
def μstar : ℝ :=
  Classical.choose (diffusive_fourier qq qq_ge σ₀ σ₀_pos σ₀_lt_one L₀ negMoment₀ cf₀)

/-- `R₀` from Proposition 3.11. -/
def R₀ : ℝ :=
  Classical.choose
    (Classical.choose_spec (diffusive_fourier qq qq_ge σ₀ σ₀_pos σ₀_lt_one L₀ negMoment₀ cf₀))

/-- The parameter `R ≥ R₀` with `e^{-2R²q²} ≤ ε/16`. -/
def Rε (ε : ℝ) : ℝ := max R₀ (Real.sqrt (Real.log (16 / ε)))

/-! ### Definition 4.2: the probability space -/

/-- The phase space `Ω = Ω_b^ℕ` (the coordinate `ω 0` is unused; the blocks are
`ω 1, ω 2, …`). -/
abbrev Phase := ℕ → BlockParam L₀

/-- The product probability measure on `Ω`. -/
def phaseMeasure : Measure Phase := Measure.infinitePi fun _ : ℕ => blockMeasure L₀

instance : IsProbabilityMeasure phaseMeasure := by unfold phaseMeasure; infer_instance

/-! ### Definition 4.3: stage scales -/

/-- `τ_* = 1/32`. -/
def τstar : ℝ := 1 / 32

/-- `k_j = q^j`. -/
def kk (j : ℕ) : ℝ := (qq : ℝ) ^ j

/-- `δ_j = τ_* j⁻³`. -/
def δs (j : ℕ) : ℝ := τstar / (j : ℝ) ^ 3

/-- `η_j = τ_* j⁻²`. -/
def ηs (j : ℕ) : ℝ := τstar / (j : ℝ) ^ 2

/-- `s_j = ∑_{1 ≤ i < j} (δ_i + η_i)` (so `s_1 = 0`, `s_{j+1} = s_j + δ_j + η_j`). -/
def sj (j : ℕ) : ℝ := ∑ i ∈ Finset.Ico 1 j, (δs i + ηs i)

/-- `T_N = s_{N+1}`. -/
def TN (N : ℕ) : ℝ := sj (N + 1)

/-- `T_* = ∑_{j ≥ 1} (δ_j + η_j)`. -/
def Tstar : ℝ := ∑' i : ℕ, (δs (i + 1) + ηs (i + 1))

/-- The pulse interval `I_j = [s_j, s_j + δ_j]`. -/
def Ij (j : ℕ) : Set ℝ := Icc (sj j) (sj j + δs j)

/-- The quiet interval `J_j = [s_j + δ_j, s_{j+1}]`. -/
def Jj (j : ℕ) : Set ℝ := Icc (sj j + δs j) (sj (j + 1))

/-- **Lemma 4.4.** `0 < T_* < 1`. -/
theorem accumulation_time : 0 < Tstar ∧ Tstar < 1 := by
  have h2 : HasSum (fun i : ℕ => 1 / ((i:ℝ)+1)^2) (π^2/6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hs3 : Summable (fun i : ℕ => 1 / ((i:ℝ)+1)^3) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2.summable
    have h1 : (1:ℝ) ≤ (i:ℝ)+1 := by linarith [i.cast_nonneg (α := ℝ)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 3 by norm_num)]
  have hle : ∑' i : ℕ, 1 / ((i:ℝ)+1)^3 ≤ π^2/6 := by
    rw [← h2.tsum_eq]
    refine hs3.tsum_le_tsum (fun i => ?_) h2.summable
    have h1 : (1:ℝ) ≤ (i:ℝ)+1 := by linarith [i.cast_nonneg (α := ℝ)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_right₀ h1 (show 2 ≤ 3 by norm_num)]
  have heq : Tstar = τstar * (∑' i : ℕ, 1 / ((i:ℝ)+1)^3) + τstar * (π^2/6) := by
    unfold Tstar δs ηs
    rw [← h2.tsum_eq, ← tsum_mul_left, ← tsum_mul_left,
      ← (hs3.mul_left _).tsum_add (h2.summable.mul_left _)]
    congr 1; ext i; push_cast; ring
  have hpi : π < 3.15 := pi_lt_d2
  have hpos3 : 0 < ∑' i : ℕ, 1 / ((i:ℝ)+1)^3 := by
    refine hs3.tsum_pos (fun i => by positivity) 0 (by norm_num)
  unfold τstar at heq
  constructor
  · rw [heq]; positivity
  · rw [heq]; nlinarith [pi_pos]

lemma stage_nonneg (i : ℕ) : 0 ≤ δs i + ηs i := by unfold δs ηs τstar; positivity

lemma summable_stage : Summable (fun i : ℕ => δs (i + 1) + ηs (i + 1)) := by
  by_contra h
  have := tsum_eq_zero_of_not_summable h
  have h1 := accumulation_time.1
  unfold Tstar at h1
  linarith

lemma sj_bounds (j : ℕ) : 0 ≤ sj j ∧ sj j ≤ Tstar := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => stage_nonneg i)
  · unfold sj Tstar
    rw [Finset.sum_Ico_eq_sum_range]
    have := summable_stage.sum_le_tsum (Finset.range (j - 1)) (fun i _ => stage_nonneg (i+1))
    simpa [add_comm] using this

lemma TN_bounds (N : ℕ) : 0 ≤ TN N ∧ TN N ≤ 1 :=
  ⟨(sj_bounds _).1, (sj_bounds _).2.trans accumulation_time.2.le⟩

/-! ### Definition 4.5: the fixed horizontal force -/

open Classical in
/-- The force `g_ω(t,x) = (k_j δ_j²)⁻¹ (∂ₛ b_{ω_j})((t - s_j)/δ_j, k_j x)` for `t ∈ I_j`, and
`0` elsewhere. -/
def gForce (w : Phase) (t : ℝ) (x : Pt 2) : Pt 2 :=
  ∑' j : ℕ, if 1 ≤ j ∧ t ∈ Ij j then
    (1 / (kk j * δs j ^ 2)) • bDot cf₀ (w j) ((t - sj j) / δs j) (kk j • x) else 0

/- **Lemma 4.6** (regularity of the force) is stated and proved as `force_regularity` in
`RequestProject/ForceRegularity.lean`. -/

/-! ### Definition 4.7: comparison viscosities -/

/-- `ν_N = 1/(4π² k_N² η_N)`. -/
def nuN (N : ℕ) : ℝ := 1 / (4 * π ^ 2 * kk N ^ 2 * ηs N)

/-- The dimensionless pulse diffusivity `μ_{j,N} = 4π² ν_N k_j² δ_j`. -/
def muJN (j N : ℕ) : ℝ := 4 * π ^ 2 * nuN N * kk j ^ 2 * δs j

lemma nat_cube_le (j a : ℕ) (hj : 1 ≤ j) : (j + a) ^ 3 ≤ j ^ 3 * 9 ^ a := by
  have h1 : (1 + a) ^ 3 ≤ 9 ^ a := by
    induction a with
    | zero => simp
    | succ n ih =>
      have : (1 + (n+1))^3 ≤ 9 * (1+n)^3 := by
        ring_nf; nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2), Nat.zero_le n]
      calc (1 + (n+1))^3 ≤ 9 * (1+n)^3 := this
        _ ≤ 9 * 9^n := by omega
        _ = 9^(n+1) := by ring
  have h2 : j + a ≤ j * (1 + a) := by nlinarith
  calc (j+a)^3 ≤ (j*(1+a))^3 := Nat.pow_le_pow_left h2 3
    _ = j^3 * (1+a)^3 := by ring
    _ ≤ j^3 * 9^a := Nat.mul_le_mul_left _ h1

/-- **Lemma 4.8** (viscosities).  `ν_N = N²/(4π²τ_* q^{2N})`, `μ_{j,N} = q^{-2(N-j)}N²/j³`,
`(ν_N)` is positive, strictly decreasing and tends to zero, `max_{j ≤ N} μ_{j,N} ≤ C_q/N`,
and `μ_{j,N} ≤ μ_*` for all `j ≤ N` once `N` is large. -/
theorem viscosity_properties :
    (∀ N : ℕ, 1 ≤ N → nuN N = (N : ℝ) ^ 2 / (4 * π ^ 2 * τstar * (qq : ℝ) ^ (2 * N))) ∧
    (∀ j N : ℕ, 1 ≤ j → j ≤ N →
      muJN j N = (qq : ℝ) ^ (-(2 * ((N : ℝ) - j))) * (N : ℝ) ^ 2 / (j : ℝ) ^ 3) ∧
    (∀ N : ℕ, 1 ≤ N → 0 < nuN N) ∧ StrictAntiOn nuN (Ici 1) ∧ Tendsto nuN atTop (𝓝 0) ∧
    (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ j, 1 ≤ j → j ≤ N → muJN j N ≤ C / N) ∧
    (∀ m : ℝ, 0 < m → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ j, 1 ≤ j → j ≤ N → muJN j N ≤ m) := by
  have hq : (qq : ℝ) = 3 := by norm_num [qq]
  have hnu : ∀ N : ℕ, 1 ≤ N →
      nuN N = (N : ℝ) ^ 2 / (4 * π ^ 2 * τstar * (qq : ℝ) ^ (2 * N)) := by
    intro N hN
    have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    unfold nuN kk ηs
    field_simp
    ring
  have hmu : ∀ j N : ℕ, 1 ≤ j → j ≤ N → muJN j N = (N:ℝ)^2 * 9^j / (9^N * (j:ℝ)^3) := by
    intro j N hj hjN
    have hj' : (j:ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    unfold muJN
    rw [hnu N (by omega)]
    unfold kk δs τstar
    rw [hq]
    have : (3:ℝ)^(2*N) = 9^N := by rw [pow_mul]; norm_num
    have h2 : ((3:ℝ)^j)^2 = 9^j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, h2]
    field_simp
  have hmubound : ∀ N : ℕ, 1 ≤ N → ∀ j, 1 ≤ j → j ≤ N → muJN j N ≤ 1 / N := by
    intro N _ j hj hjN
    rw [hmu j N hj hjN]
    obtain ⟨a, rfl⟩ : ∃ a, N = j + a := ⟨N - j, by omega⟩
    have key := nat_cube_le j a hj
    have key' : ((j:ℝ) + a)^3 ≤ (j:ℝ)^3 * 9^a := by exact_mod_cast key
    have hjpos : (0:ℝ) < j := by exact_mod_cast hj
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    rw [pow_add]
    nlinarith [pow_pos (show (0:ℝ) < 9 by norm_num) j, pow_pos (show (0:ℝ) < 9 by norm_num) a]
  have hpos : ∀ N : ℕ, 1 ≤ N → 0 < nuN N := by
    intro N hN
    rw [hnu N hN]
    have : (0:ℝ) < N := by exact_mod_cast hN
    rw [hq]; unfold τstar
    exact div_pos (pow_pos this 2) (by positivity)
  refine ⟨hnu, ?_, hpos, ?_, ?_, ⟨1, hmubound⟩, ?_⟩
  · intro j N hj hjN
    rw [hmu j N hj hjN]
    have : (qq:ℝ) ^ (-(2 * ((N : ℝ) - j))) = 9^j / 9^N := by
      rw [hq]
      have e : -(2 * ((N : ℝ) - j)) = ((2*j : ℕ) : ℝ) - ((2*N : ℕ) : ℝ) := by push_cast; ring
      rw [e, Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast, pow_mul,
        pow_mul]
      norm_num
    rw [this]
    field_simp
  · have step : ∀ N, 1 ≤ N → nuN (N+1) < nuN N := by
      intro N hN
      rw [hnu N hN, hnu (N+1) (by omega), hq]
      have hNpos : (0:ℝ) < N := by exact_mod_cast hN
      have hπ : 0 < π := pi_pos
      rw [div_lt_div_iff₀ (by unfold τstar; positivity) (by unfold τstar; positivity)]
      have : (3:ℝ)^(2*(N+1)) = 9 * 3^(2*N) := by ring
      rw [this]
      push_cast
      have h3 : (0:ℝ) < 3^(2*N) := by positivity
      unfold τstar
      have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
      have : ((N:ℝ)+1)^2 < 9 * N^2 := by nlinarith
      nlinarith [mul_pos (mul_pos (mul_pos (show (0:ℝ) < 4 by norm_num) (pow_pos hπ 2))
        (show (0:ℝ) < 1/32 by norm_num)) h3]
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    induction b, hab using Nat.le_induction with
    | base => exact step a ha
    | succ n hn ih => exact (step n (by omega)).trans (ih (by omega))
  · have h := tendsto_pow_const_div_const_pow_of_one_lt 2 (show (1:ℝ) < 9 by norm_num)
    have h' := h.const_mul (1 / (4 * π ^ 2 * τstar))
    rw [mul_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hnu N hN, hq]
    have : (3:ℝ)^(2*N) = 9^N := by rw [pow_mul]; norm_num
    rw [this]
    field_simp
  · intro m hm
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1/m)
    refine ⟨N₀, fun N hN j hj hjN => (hmubound N (by
      have : (0:ℝ) < N₀ := lt_trans (by positivity) hN₀
      have : 0 < N₀ := by exact_mod_cast this
      omega) j hj hjN).trans ?_⟩
    have hNpos : (0:ℝ) < N := by
      have : (0:ℝ) < 1/m := by positivity
      have : (N₀:ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [div_le_iff₀ hNpos]
    have : (N₀:ℝ) ≤ N := by exact_mod_cast hN
    have := (div_lt_iff₀ hm).1 (lt_of_lt_of_le hN₀ this)
    linarith

/- **Proposition 4.9** (true horizontal solutions) is stated and proved as
`true_horizontal_existence` in `RequestProject/TrueHorizontal.lean`. -/

end AnomDiss
