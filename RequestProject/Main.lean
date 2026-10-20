module

public import RequestProject.Selection
public import RequestProject.TrueHorizontal
public import RequestProject.UniformBound

/-!
# Section 8: proof of the main theorem (Theorem 1.8)

**Theorem 1.8.**  For every `ε ∈ (0,1)` there exist a real divergence-free field
`u₀ ∈ C^∞(𝕋³;ℝ³)` with `‖u₀‖_{L²(𝕋³)} = 1`, a real force
`f ∈ ⋂_{0<α<1} C_c^∞((0,1); C^α_σ(𝕋³))` and a strictly decreasing sequence `ν_m → 0` such that,
for every `m`, the forced Navier–Stokes system with viscosity `ν_m`, force `f` and initial datum
`u₀` has a classical solution `u_m` on `[0,1]` with `sup_m ‖u_m‖_{L^∞([0,1]×𝕋³)} < ∞` and
`ν_m ∫₀¹ ‖∇u_m(t)‖²_{L²(𝕋³)} dt ≥ (1-ε)/2`.

The two external results of the paper are explicit hypotheses of the theorem.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

namespace AnomDiss

/-! ### Auxiliary facts used in the final assembly -/

lemma volume_cell (d : ℕ) : volume (cell d) = 1 := by
  simp [cell, Real.volume_Icc_pi]

lemma holderNorm_embedU_le (α : ℝ) (hα : 0 ≤ α) (A : Pt 2 → Pt 2) :
    holderNorm α (embedU A 0) ≤ holderNorm α A := by
  unfold holderNorm
  gcongr
  · refine iSup_le fun x => le_iSup_of_le (proj3 x) ?_
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ((norm_embedU_le A 0 x).trans ?_)
    simp
  · refine iSup_le fun x => iSup_le fun y => le_iSup_of_le (proj3 x) (le_iSup_of_le (proj3 y) ?_)
    refine ENNReal.div_le_div ?_ ?_
    · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ((norm_embedU_sub_le A A 0 0 x y).trans ?_)
      simp
    · refine ENNReal.rpow_le_rpow ?_ hα
      rw [← proj3_sub, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (norm_proj3_le _)

/-- The three-dimensional force obtained from an admissible two-dimensional force is
admissible. -/
lemma embed_force_admissible (g : ℝ → Pt 2 → Pt 2) (hg : IsAdmissibleForce g) :
    IsAdmissibleForce (fun t => embedU (g t) 0) := by
  have hz : embedU (0 : Pt 2 → Pt 2) (0 : Pt 2 → ℝ) = 0 := by
    funext x; ext k; fin_cases k <;> simp [embedU]
  refine ⟨⟨fun t => isPeriodic_embedU (hg.periodic t) (fun _ _ => rfl),
    fun t => contDiff_embedU (hg.smooth_slice t) contDiff_const, fun t x => ?_, ?_⟩, ?_⟩
  · rw [divergence_embedU ((hg.smooth_slice t).differentiable (by simp))
      (by exact differentiable_const _)]
    exact hg.div_free t _
  · intro α hα0 hα1
    obtain ⟨D, hD0, hDfin, hDlim⟩ := hg.smooth_holder α hα0 hα1
    refine ⟨fun r t => embedU (D r t) 0,
      by show (fun t => embedU (D 0 t) 0) = _; rw [hD0], fun r t =>
      lt_of_le_of_lt (holderNorm_embedU_le α hα0.le _) (hDfin r t), fun r t => ?_⟩
    have hlin : ∀ h : ℝ, h⁻¹ • (embedU (D r (t + h)) 0 - embedU (D r t) 0) -
        embedU (D (r + 1) t) 0 = embedU (h⁻¹ • (D r (t + h) - D r t) - D (r + 1) t) 0 := by
      intro h; funext x; ext k; fin_cases k <;> simp [embedU]
    simp_rw [hlin]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hDlim r t)
      (fun h => zero_le) (fun h => holderNorm_embedU_le α hα0.le _)
  · obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hg.compact_support
    exact ⟨a, b, ha, hab, hb, fun t ht => by simp only [hsupp t ht, hz]⟩

/-- Properties of the initial datum `u₀ = (0, 0, θ₀)`. -/
lemma embed_initial (θ₀ : Pt 2 → ℝ) (hθ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) :
    ContDiff ℝ ∞ (embedU 0 θ₀) ∧ IsPeriodic (embedU 0 θ₀) ∧
    (∀ x, divergence (embedU 0 θ₀) x = 0) ∧ l2sqV (embedU 0 θ₀) = l2sq θ₀ := by
  refine ⟨contDiff_embedU contDiff_const hθ, isPeriodic_embedU (fun _ _ => rfl) hp,
    fun x => ?_, ?_⟩
  · rw [divergence_embedU (by exact differentiable_const _) (hθ.differentiable (by simp))]
    simp [divergence, pd_zero_fun]
  · unfold l2sqV l2sq
    have : (fun x => ∑ k, embedU 0 θ₀ x k ^ 2) = fun x => (fun y => θ₀ y ^ 2) (proj3 x) := by
      funext x; simp [embedU, Fin.sum_univ_three]
    rw [this]
    exact integral_cell3 (fun y => θ₀ y ^ 2)

/-- Sup-norm bound for `u = (v₁, v₂, θ)`. -/
lemma embedU_norm_le (v : Pt 2 → Pt 2) (θ : Pt 2 → ℝ) (x : Pt 3) (C₁ C₂ : ℝ)
    (hv : euclNorm (v (proj3 x)) ≤ C₁) (hθ : |θ (proj3 x)| ≤ C₂) :
    ‖embedU v θ x‖ ≤ C₁ + C₂ := by
  have h1 : 0 ≤ C₁ := le_trans (Real.sqrt_nonneg _) hv
  have h2 : 0 ≤ C₂ := le_trans (abs_nonneg _) hθ
  refine (pi_norm_le_iff_of_nonneg (by linarith)).2 (fun i => ?_)
  rw [Real.norm_eq_abs]
  fin_cases i <;> simp [embedU]
  · linarith [abs_le_euclNorm (v (proj3 x)) 0]
  · linarith [abs_le_euclNorm (v (proj3 x)) 1]
  · linarith

lemma intervalIntegrable_of_holder {f : ℝ → ℝ} {T K γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ)
    (h : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, |f t - f s| ≤ K * |t - s| ^ γ) :
    IntervalIntegrable f volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hT]
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun s => K * |s - t| ^ γ) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have : Tendsto (fun s => K * |s - t| ^ γ) (𝓝 t) (𝓝 (K * |t - t| ^ γ)) := by
      apply Tendsto.const_mul
      exact ((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
        (fun _ => Or.inr hγ.le)).tendsto t
    simp only [sub_self, abs_zero, Real.zero_rpow hγ.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Real.norm_eq_abs]
  exact h s hs t ht

lemma intervalIntegrable_cell {G : ℝ → Pt 2 → ℝ} {T K γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ)
    (hc : ∀ t ∈ Icc 0 T, Continuous (G t))
    (h : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x, |G t x - G s x| ≤ K * |t - s| ^ γ) :
    IntervalIntegrable (fun t => ∫ x in cell 2, G t x) volume 0 T := by
  have hi : ∀ t ∈ Icc 0 T, IntegrableOn (G t) (cell 2) := fun t ht => (hc t ht).integrableOn_Icc
  refine intervalIntegrable_of_holder (K := K) hT hγ (fun t ht s hs => ?_)
  rw [← integral_sub (hi t ht) (hi s hs), ← Real.norm_eq_abs]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cell 2)
    (f := fun x => G t x - G s x) (C := K * |t - s| ^ γ) (by rw [volume_cell]; simp)
    (fun x _ => by rw [Real.norm_eq_abs]; exact h t ht s hs x)
  simpa [Measure.real, volume_cell] using this

lemma sq_sub_sq_le {a b B C : ℝ} (ha : |a| ≤ B) (hb : |b| ≤ B) (hab : |a - b| ≤ C) :
    |a ^ 2 - b ^ 2| ≤ 2 * B * C := by
  have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [this, abs_mul]
  have h1 : |a + b| ≤ 2 * B := by
    calc |a + b| ≤ |a| + |b| := abs_add_le a b
      _ ≤ 2 * B := by linarith
  have hC : 0 ≤ C := le_trans (abs_nonneg _) hab
  nlinarith [abs_nonneg (a - b), abs_nonneg (a + b)]

/-- For `u ∈ C^{1+β/2,2+β}`, `t ↦ ‖∇u(t)‖₂²` is integrable on `[0,T]`. -/
lemma intervalIntegrable_gradSqV (T β : ℝ) (hT : 0 ≤ T) (hβ : 0 < β) (u : ℝ → Pt 2 → Pt 2)
    (hu : IsParabolicC12 T β u) :
    IntervalIntegrable (fun t => ∫ x in cell 2, gradSqV (u t) x) volume 0 T := by
  have hB : ∀ i, ∃ B, ∀ t ∈ Icc 0 T, ∀ x, ‖pd i (u t) x‖ ≤ B := fun i => hu.bdd_d1 i
  have hH : ∀ i, ∃ C, ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x,
      ‖pd i (u t) x - pd i (u s) x‖ ≤ C * |t - s| ^ ((1 + β) / 2) :=
    fun i => hu.holder_d1_time i
  choose B hB using hB
  choose C hC using hH
  set B0 := ∑ i, |B i|
  set C0 := ∑ i, |C i|
  have hB0 : ∀ i t, t ∈ Icc 0 T → ∀ x k, |pd i (u t) x k| ≤ B0 := by
    intro i t ht x k
    calc |pd i (u t) x k| ≤ ‖pd i (u t) x‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ k
      _ ≤ B i := hB i t ht x
      _ ≤ |B i| := le_abs_self _
      _ ≤ B0 := Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
  have hC0 : ∀ i t, t ∈ Icc 0 T → ∀ s, s ∈ Icc 0 T → ∀ x k,
      |pd i (u t) x k - pd i (u s) x k| ≤ C0 * |t - s| ^ ((1 + β) / 2) := by
    intro i t ht s hs x k
    have hp : 0 ≤ |t - s| ^ ((1 + β) / 2) := by positivity
    calc |pd i (u t) x k - pd i (u s) x k| ≤ ‖pd i (u t) x - pd i (u s) x‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (pd i (u t) x - pd i (u s) x) k
      _ ≤ C i * |t - s| ^ ((1 + β) / 2) := hC i t ht s hs x
      _ ≤ |C i| * |t - s| ^ ((1 + β) / 2) := mul_le_mul_of_nonneg_right (le_abs_self _) hp
      _ ≤ C0 * |t - s| ^ ((1 + β) / 2) := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)) hp
  refine intervalIntegrable_cell (K := 4 * (2 * B0 * C0)) (γ := (1 + β) / 2) hT (by linarith)
    (fun t ht => ?_) ?_
  · unfold gradSqV
    have : ∀ i, Continuous (pd i (u t)) := fun i =>
      continuous_pd ((hu.smooth_x t ht).of_le (by norm_num)) i
    fun_prop
  · intro t ht s hs x
    unfold gradSqV
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Fin 2, |∑ k, pd i (u t) x k ^ 2 - ∑ k, pd i (u s) x k ^ 2| ≤
        2 * (2 * B0 * (C0 * |t - s| ^ ((1 + β) / 2))) := by
      intro i
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k : Fin 2, |pd i (u t) x k ^ 2 - pd i (u s) x k ^ 2|
          ≤ ∑ k : Fin 2, 2 * B0 * (C0 * |t - s| ^ ((1 + β) / 2)) :=
            Finset.sum_le_sum (fun k _ => sq_sub_sq_le (hB0 i t ht x k) (hB0 i s hs x k)
              (hC0 i t ht s hs x k))
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    calc ∑ i : Fin 2, |∑ k, pd i (u t) x k ^ 2 - ∑ k, pd i (u s) x k ^ 2|
        ≤ ∑ i : Fin 2, 2 * (2 * B0 * (C0 * |t - s| ^ ((1 + β) / 2))) :=
          Finset.sum_le_sum (fun i _ => this i)
      _ = 4 * (2 * B0 * C0) * |t - s| ^ ((1 + β) / 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- For `θ ∈ C^{1+β/2,2+β}`, `t ↦ ‖∇θ(t)‖₂²` is integrable on `[0,T]`. -/
lemma intervalIntegrable_gradSq (T β : ℝ) (hT : 0 ≤ T) (hβ : 0 < β) (θ : ℝ → Pt 2 → ℝ)
    (hθ : IsParabolicC12 T β θ) :
    IntervalIntegrable (fun t => ∫ x in cell 2, gradSq (θ t) x) volume 0 T := by
  have hB : ∀ i, ∃ B, ∀ t ∈ Icc 0 T, ∀ x, ‖pd i (θ t) x‖ ≤ B := fun i => hθ.bdd_d1 i
  have hH : ∀ i, ∃ C, ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x,
      ‖pd i (θ t) x - pd i (θ s) x‖ ≤ C * |t - s| ^ ((1 + β) / 2) :=
    fun i => hθ.holder_d1_time i
  choose B hB using hB
  choose C hC using hH
  set B0 := ∑ i, |B i|
  set C0 := ∑ i, |C i|
  have hB0 : ∀ i t, t ∈ Icc 0 T → ∀ x, |pd i (θ t) x| ≤ B0 := by
    intro i t ht x
    calc |pd i (θ t) x| = ‖pd i (θ t) x‖ := (Real.norm_eq_abs _).symm
      _ ≤ B i := hB i t ht x
      _ ≤ |B i| := le_abs_self _
      _ ≤ B0 := Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
  have hC0 : ∀ i t, t ∈ Icc 0 T → ∀ s, s ∈ Icc 0 T → ∀ x,
      |pd i (θ t) x - pd i (θ s) x| ≤ C0 * |t - s| ^ ((1 + β) / 2) := by
    intro i t ht s hs x
    have hp : 0 ≤ |t - s| ^ ((1 + β) / 2) := by positivity
    calc |pd i (θ t) x - pd i (θ s) x| = ‖pd i (θ t) x - pd i (θ s) x‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ C i * |t - s| ^ ((1 + β) / 2) := hC i t ht s hs x
      _ ≤ |C i| * |t - s| ^ ((1 + β) / 2) := mul_le_mul_of_nonneg_right (le_abs_self _) hp
      _ ≤ C0 * |t - s| ^ ((1 + β) / 2) := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)) hp
  refine intervalIntegrable_cell (K := 2 * (2 * B0 * C0)) (γ := (1 + β) / 2) hT (by linarith)
    (fun t ht => ?_) ?_
  · unfold gradSq
    have : ∀ i, Continuous (pd i (θ t)) := fun i =>
      continuous_pd ((hθ.smooth_x t ht).of_le (by norm_num)) i
    fun_prop
  · intro t ht s hs x
    unfold gradSq
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin 2, |pd i (θ t) x ^ 2 - pd i (θ s) x ^ 2|
        ≤ ∑ i : Fin 2, 2 * B0 * (C0 * |t - s| ^ ((1 + β) / 2)) :=
          Finset.sum_le_sum (fun i _ => sq_sub_sq_le (hB0 i t ht x) (hB0 i s hs x)
            (hC0 i t ht s hs x))
      _ = 2 * (2 * B0 * C0) * |t - s| ^ ((1 + β) / 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- `T_N ≤ 1`. -/
lemma TN_le_one (N : ℕ) : 0 ≤ TN N ∧ TN N ≤ 1 := TN_bounds N

/-! ### The main theorem -/

/-- **Theorem 1.8** (anomalous dissipation with a single forcing). -/
theorem main_theorem (hNS : ExternalNS2D) (hSc : ExternalScalar) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x := by
  obtain ⟨N₁, Cv, hN₁, hbound⟩ := uniform_horizontal_bound
  obtain ⟨wstar, Nseq, hmono, hge, hsel⟩ := phase_selection hSc ε hε0 hε1 N₁
  obtain ⟨-, -, hθs, hθp, hθl2, hθmax, -, -⟩ := initial_frequency ε hε0
  obtain ⟨-, -, hνpos, hνanti, hνlim, -, -⟩ := viscosity_properties
  have hN1 : ∀ m, 1 ≤ Nseq m := fun m => le_trans hN₁ (hge m)
  set ν : ℕ → ℝ := fun m => nuN (Nseq m) with hνdef
  have hνm : ∀ m, 0 < ν m := fun m => hνpos _ (hN1 m)
  have hex := fun m => true_horizontal_existence hNS hSc (ν m) (hνm m) wstar
  choose v p hv hreg hE hsc using hex
  choose θ hθ huniq hmax hen using fun m => hsc m (theta0 ε) hθs hθp
  obtain ⟨hu0s, hu0p, hu0d, hu0l⟩ := embed_initial (theta0 ε) hθs hθp
  refine ⟨embedU 0 (theta0 ε), fun t => embedU (gForce wstar t) 0, ν, hu0s, hu0p, hu0d,
    by rw [hu0l, hθl2], embed_force_admissible _ (force_regularity.1 wstar).1, hνm, ?_, ?_,
    fun m t => embedU (v m t) (θ m t), fun m t x => p m t (proj3 x), ?_, ?_, ?_⟩
  · intro a b hab
    exact hνanti (mem_Ici.2 (hN1 a)) (mem_Ici.2 (hN1 b)) (hmono hab)
  · exact hνlim.comp hmono.tendsto_atTop
  · intro m
    obtain ⟨β, hβ0, hβ1, hθreg⟩ := (hθ m).regular
    exact (two_to_three_embedding 1 (ν m) β one_pos hβ0 hβ1 0 (gForce wstar) (v m) (p m) (hv m)
      (hreg m β hβ0 hβ1).1 (hreg m β hβ0 hβ1).2 (theta0 ε) (θ m) (hθ m) hθreg).1
  · refine ⟨Cv + Real.sqrt 2, fun m t ht x => ?_⟩
    exact embedU_norm_le _ _ x _ _
      (hbound wstar (Nseq m) (hge m) (v m) (p m) (hv m) t ht (proj3 x))
      (hmax m (Real.sqrt 2) hθmax t ht (proj3 x))
  · intro m
    obtain ⟨β, hβ0, hβ1, hθreg⟩ := (hθ m).regular
    have hemb := two_to_three_embedding 1 (ν m) β one_pos hβ0 hβ1 0 (gForce wstar) (v m) (p m)
      (hv m) (hreg m β hβ0 hβ1).1 (hreg m β hβ0 hβ1).2 (theta0 ε) (θ m) (hθ m) hθreg
    have h1 : (∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (embedU (v m t) (θ m t)) x) =
        ∫ t in (0 : ℝ)..1, ((∫ x in cell 2, gradSqV (v m t) x) +
          ∫ x in cell 2, gradSq (θ m t) x) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le zero_le_one] at ht
      exact hemb.2 t ht
    have hA := intervalIntegrable_gradSqV 1 β zero_le_one hβ0 (v m) (hreg m β hβ0 hβ1).1
    have hB := intervalIntegrable_gradSq 1 β zero_le_one hβ0 (θ m) hθreg
    obtain ⟨hT0, hT1⟩ := TN_le_one (Nseq m)
    have hBsplit : (∫ t in (0 : ℝ)..1, ∫ x in cell 2, gradSq (θ m t) x) =
        (∫ t in (0 : ℝ)..TN (Nseq m), ∫ x in cell 2, gradSq (θ m t) x) +
          ∫ t in TN (Nseq m)..1, ∫ x in cell 2, gradSq (θ m t) x := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact hB.mono_set (by rw [uIcc_of_le hT0, uIcc_of_le zero_le_one]
                              exact Icc_subset_Icc le_rfl hT1)
      · exact hB.mono_set (by rw [uIcc_of_le hT1, uIcc_of_le zero_le_one]
                              exact Icc_subset_Icc hT0 le_rfl)
    have hAnn : 0 ≤ ∫ t in (0 : ℝ)..1, ∫ x in cell 2, gradSqV (v m t) x := by
      refine intervalIntegral.integral_nonneg zero_le_one (fun t _ => ?_)
      refine setIntegral_nonneg measurableSet_Icc (fun x _ => ?_)
      unfold gradSqV
      positivity
    have hBnn : 0 ≤ ∫ t in TN (Nseq m)..1, ∫ x in cell 2, gradSq (θ m t) x := by
      refine intervalIntegral.integral_nonneg hT1 (fun t _ => ?_)
      refine setIntegral_nonneg measurableSet_Icc (fun x _ => ?_)
      unfold gradSq
      positivity
    have hdiss := hen m (TN (Nseq m)) ⟨hT0, hT1⟩
    have hsel' := hsel m (v m) (p m) (hv m) (θ m) (hθ m)
    rw [hθl2] at hdiss
    unfold dissipation at hdiss
    show (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1,
      ∫ x in cell 3, gradSqV (embedU (v m t) (θ m t)) x
    rw [h1, intervalIntegral.integral_add hA hB, hBsplit]
    have hνpos' := hνm m
    nlinarith [mul_nonneg hνpos'.le hAnn, mul_nonneg hνpos'.le hBnn]

end AnomDiss
