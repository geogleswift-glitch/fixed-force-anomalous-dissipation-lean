module

public import RequestProject.ScalarStages

/-!
# Parabolic Hölder regularity of smooth periodic drifts

A drift `V(t,x)` which is jointly `C²` and `ℤ²`-periodic in `x` belongs to `C^{β/2,1+β}` on
`[0,T] × 𝕋²` for every `0 < β < 1`.  This is applied to the isolated pulses of Section 5.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

section generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A jointly `C¹` function on `ℝ × ℝ²`, periodic in the space variable, is bounded and
Lipschitz on `[0,T] × ℝ²`. -/
lemma joint_lip_bdd {T : ℝ} (F : ℝ × Pt 2 → E) (hF : ContDiff ℝ 1 F)
    (hp : ∀ t x (n : Fin 2 → ℤ), F (t, x + intVec n) = F (t, x)) :
    ∃ B L, 0 ≤ L ∧ (∀ p ∈ Icc 0 T ×ˢ (univ : Set (Pt 2)), ‖F p‖ ≤ B) ∧
      ∀ p ∈ Icc 0 T ×ˢ (univ : Set (Pt 2)), ∀ q ∈ Icc 0 T ×ˢ (univ : Set (Pt 2)),
        ‖F p - F q‖ ≤ L * ‖p - q‖ := by
  have hK : IsCompact (Icc 0 T ×ˢ cell 2) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn
    (hF.continuous_fderiv one_ne_zero).continuousOn
  have hshift : ∀ (n : Fin 2 → ℤ), F = fun q => F (q + ((0 : ℝ), intVec n)) := fun n => by
    funext q; obtain ⟨t, x⟩ := q; simp [hp]
  have hfp : ∀ t x (n : Fin 2 → ℤ), fderiv ℝ F (t, x + intVec n) = fderiv ℝ F (t, x) := by
    intro t x n
    conv_rhs => rw [hshift n]
    rw [fderiv_comp_add_right]
    simp
  have hrep : ∀ p ∈ Icc 0 T ×ˢ (univ : Set (Pt 2)), ∃ y ∈ cell 2, ∃ n : Fin 2 → ℤ,
      p = (p.1, y + intVec n) := fun p _ => by
    obtain ⟨y, hy, n, hn⟩ := exists_cell_rep p.2
    exact ⟨y, hy, n, by rw [← hn]⟩
  refine ⟨B, max L 0, le_max_right _ _, fun p hp' => ?_, fun p hp' q hq => ?_⟩
  · obtain ⟨y, hy, n, hn⟩ := hrep p hp'
    rw [hn, hp]
    exact hB (p.1, y) ⟨hp'.1, hy⟩
  · have := (convex_Icc (0:ℝ) T |>.prod (convex_univ (E := Pt 2))).norm_image_sub_le_of_norm_fderiv_le
      (f := F) (C := max L 0) (fun z _ => (hF.differentiable one_ne_zero) z) (fun z hz => by
        obtain ⟨y, hy, n, hn⟩ := hrep z hz
        rw [hn, hfp]
        exact (hL (z.1, y) ⟨hz.1, hy⟩).trans (le_max_left _ _)) hq hp'
    exact this

/-- `r ≤ T^{1-γ} r^γ` for `0 ≤ r ≤ T` and `0 ≤ γ ≤ 1`. -/
lemma le_rpow_bound {r T γ : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ T) (hγ1 : γ ≤ 1) :
    r ≤ T ^ (1 - γ) * r ^ γ := by
  rcases eq_or_lt_of_le hr0 with h | h
  · have hT : 0 ≤ T := hr0.trans hrT
    rw [← h]; exact mul_nonneg (Real.rpow_nonneg hT _) (Real.rpow_nonneg le_rfl _)
  · calc r = r ^ (1 - γ) * r ^ γ := by
          rw [← Real.rpow_add h]; simp
      _ ≤ T ^ (1 - γ) * r ^ γ := by
          gcongr

/-- Partial derivatives of a slice in terms of the joint derivative. -/
lemma pd_slice_eq (V : ℝ → Pt 2 → E) (t : ℝ) (x : Pt 2)
    (hd : DifferentiableAt ℝ (Function.uncurry V) (t, x)) (i : Fin 2) :
    pd i (V t) x = fderiv ℝ (Function.uncurry V) (t, x) ((0 : ℝ), eb i) := by
  have : V t = Function.uncurry V ∘ fun y => (t, y) := rfl
  unfold pd
  rw [this, fderiv_comp x hd (hasFDerivAt_prodMk_right t x).differentiableAt,
    (hasFDerivAt_prodMk_right t x).fderiv]
  rfl

/-- A jointly `C²` drift, periodic in space, is in `C^{β/2,1+β}` on `[0,T]`. -/
theorem parabolicC01_of_contDiff {T β : ℝ} (hT : 0 ≤ T) (hβ0 : 0 < β) (hβ1 : β < 1)
    (V : ℝ → Pt 2 → E) (hV : ContDiff ℝ 2 (Function.uncurry V))
    (hp : ∀ t, IsPeriodic (V t)) : IsParabolicC01 T β V := by
  have hpu : ∀ t x (n : Fin 2 → ℤ), Function.uncurry V (t, x + intVec n) =
      Function.uncurry V (t, x) := fun t x n => hp t x n
  obtain ⟨B, L, hL0, hB, hL⟩ := joint_lip_bdd (T := T) (Function.uncurry V)
    (hV.of_le (by norm_num)) hpu
  -- the spatial partial derivatives, as jointly defined functions
  set G : Fin 2 → ℝ × Pt 2 → E := fun i q => fderiv ℝ (Function.uncurry V) q ((0 : ℝ), eb i)
  have hG : ∀ i, ContDiff ℝ 1 (G i) := fun i =>
    (hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hGp : ∀ i t x (n : Fin 2 → ℤ), G i (t, x + intVec n) = G i (t, x) := by
    intro i t x n
    have hshift : Function.uncurry V = fun q => Function.uncurry V (q + ((0 : ℝ), intVec n)) := by
      funext q; obtain ⟨t, x⟩ := q; simp [hpu]
    simp only [G]
    conv_rhs => rw [hshift]
    rw [fderiv_comp_add_right]
    simp
  have hGe : ∀ i t x, pd i (V t) x = G i (t, x) := fun i t x =>
    pd_slice_eq V t x ((hV.differentiable (by norm_num)) _) i
  choose BG LG hLG0 hBG hLG using fun i => joint_lip_bdd (T := T) (G i) (hG i) (hGp i)
  have hmem : ∀ t ∈ Icc 0 T, ∀ x : Pt 2, (t, x) ∈ Icc 0 T ×ˢ (univ : Set (Pt 2)) :=
    fun t ht x => ⟨ht, mem_univ _⟩
  have hnorm_t : ∀ t s : ℝ, ∀ x : Pt 2, ‖((t, x) : ℝ × Pt 2) - (s, x)‖ = |t - s| := by
    intro t s x; simp [Prod.norm_def, Real.norm_eq_abs]
  have hnorm_x : ∀ s : ℝ, ∀ x y : Pt 2, ‖((s, x) : ℝ × Pt 2) - (s, y)‖ = ‖x - y‖ := by
    intro s x y; simp [Prod.norm_def]
  have hts : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, |t - s| ≤ T := fun t ht s hs => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  refine ⟨fun t _ => (hV.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num),
    ⟨B, fun t ht x => hB _ (hmem t ht x)⟩, ⟨L * T ^ (1 - β / 2), fun t ht s hs x => ?_⟩,
    fun i => ⟨BG i, fun t ht x => by dsimp only; rw [hGe]; exact hBG i _ (hmem t ht x)⟩,
    fun i => ⟨LG i * T ^ (1 - β / 2) + (2 * BG i + LG i), fun t ht s hs x y => ?_⟩⟩
  · have h1 := hL _ (hmem t ht x) _ (hmem s hs x)
    rw [hnorm_t] at h1
    calc ‖V t x - V s x‖ ≤ L * |t - s| := h1
      _ ≤ L * (T ^ (1 - β / 2) * |t - s| ^ (β / 2)) :=
          mul_le_mul_of_nonneg_left (le_rpow_bound (abs_nonneg _) (hts t ht s hs)
            (by linarith)) hL0
      _ = _ := by ring
  · dsimp only
    simp only [hGe]
    have h1 := hLG i _ (hmem t ht x) _ (hmem s hs x)
    rw [hnorm_t] at h1
    have h2 : ‖G i (s, x) - G i (s, y)‖ ≤ (2 * BG i + LG i) * ‖x - y‖ ^ β :=
      holder_of_lip_bdd (fun z => G i (s, z)) (hLG0 i) (fun z => hBG i _ (hmem s hs z))
        (fun z w => by have := hLG i _ (hmem s hs z) _ (hmem s hs w); rwa [hnorm_x] at this)
        hβ0.le hβ1.le x y
    have h3 : |t - s| ≤ T ^ (1 - β / 2) * |t - s| ^ (β / 2) :=
      le_rpow_bound (abs_nonneg _) (hts t ht s hs) (by linarith)
    have hx : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    have ht' : 0 ≤ |t - s| ^ (β / 2) := Real.rpow_nonneg (abs_nonneg _) _
    have hT' : 0 ≤ T ^ (1 - β / 2) := Real.rpow_nonneg hT _
    have hBG0 : 0 ≤ BG i := (norm_nonneg _).trans (hBG i _ (hmem 0 ⟨le_rfl, hT⟩ 0))
    calc ‖G i (t, x) - G i (s, y)‖
        = ‖(G i (t, x) - G i (s, x)) + (G i (s, x) - G i (s, y))‖ := by abel_nf
      _ ≤ ‖G i (t, x) - G i (s, x)‖ + ‖G i (s, x) - G i (s, y)‖ := norm_add_le _ _
      _ ≤ LG i * (T ^ (1 - β / 2) * |t - s| ^ (β / 2)) + (2 * BG i + LG i) * ‖x - y‖ ^ β :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3 (hLG0 i))) h2
      _ ≤ (LG i * T ^ (1 - β / 2) + (2 * BG i + LG i)) * (‖x - y‖ ^ β + |t - s| ^ (β / 2)) := by
          have := hLG0 i
          nlinarith [mul_nonneg (mul_nonneg this hT') hx, mul_nonneg (by linarith : 0 ≤ 2 * BG i + LG i) ht']

end generic

/-! ### Drifts built from the eigenfields -/

lemma pd_affine (F : Pt 2 → Pt 2) (hF : Differentiable ℝ F) (c k : ℝ) (z x : Pt 2) (i : Fin 2) :
    pd i (fun y => c • F (k • y - z)) x = (c * k) • pd i F (k • x - z) := by
  have ha : HasFDerivAt (fun y : Pt 2 => k • y - z) (k • ContinuousLinearMap.id ℝ (Pt 2)) x := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul k).sub_const z
  have h : HasFDerivAt (fun y => c • F (k • y - z))
      (c • (fderiv ℝ F (k • x - z)).comp (k • ContinuousLinearMap.id ℝ (Pt 2))) x :=
    ((hF _).hasFDerivAt.comp x ha).const_smul c
  unfold pd
  rw [h.fderiv]
  simp [smul_smul]

/-- Properties of a drift `V(t,x) = c · b_{a(t)}(kx - z)` with `b_c ∈ 𝓔`. -/
lemma trigDrift_props (a : ℝ → Fin 4 → ℝ) (ha : ContDiff ℝ 2 a) (c : ℝ) (k : ℕ) (z : Pt 2) :
    (∀ t, IsPeriodic (fun x => c • eField (a t) ((k : ℝ) • x - z))) ∧
    ContDiff ℝ 2 (Function.uncurry fun t (x : Pt 2) => c • eField (a t) ((k : ℝ) • x - z)) ∧
    (∀ t x, divergence (fun x => c • eField (a t) ((k : ℝ) • x - z)) x = 0) := by
  refine ⟨fun t x n => ?_, ?_, fun t x => ?_⟩
  · have e : (k : ℝ) • (x + intVec n) - z = ((k : ℝ) • x - z) + intVec ((k : ℤ) • n) := by
      funext i; simp [intVec]; ring
    simp only
    rw [e, (eigenspace_properties (a t)).2.1]
  · have : (Function.uncurry fun t (x : Pt 2) => c • eField (a t) ((k : ℝ) • x - z)) =
        fun p : ℝ × Pt 2 => c • ∑ i, a p.1 i • eBasis i ((k : ℝ) • p.2 - z) := by
      funext p; rfl
    rw [this]
    refine ContDiff.const_smul c (ContDiff.sum fun i _ => ?_)
    exact (contDiff_pi.1 (ha.comp (contDiff_fst (E := ℝ) (F := Pt 2))) i).smul
      (((contDiff_eBasis i).of_le (WithTop.coe_le_coe.2 le_top)).comp
        (((contDiff_snd (E := ℝ) (F := Pt 2)).const_smul (k : ℝ)).sub contDiff_const))
  · have hE := eigenspace_properties (a t)
    unfold divergence
    simp only [pd_affine _ (hE.1.differentiable (by simp)), Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    have := hE.2.2.2.1 ((k : ℝ) • x - z)
    unfold divergence at this
    rw [this, mul_zero]

lemma contDiff_dampedCoef {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) (μ : ℝ)
    (w : BlockParam L) (n : ℕ) : ContDiff ℝ n (dampedCoef cf μ w) := by
  have hd : deriv (dampedCoef cf μ w) = fun s => deriv (cf.coef w.1) s - μ • dampedCoef cf μ w s :=
    funext fun s => (hasDerivAt_dampedCoef cf μ w s).deriv
  have hdiff : Differentiable ℝ (dampedCoef cf μ w) := fun s =>
    (hasDerivAt_dampedCoef cf μ w s).differentiableAt
  have hc : ContDiff ℝ ∞ (deriv (cf.coef w.1)) :=
    (contDiff_infty_iff_deriv.1 (cf.contDiff_coef w.1)).2
  induction n with
  | zero => exact contDiff_zero.2 hdiff.continuous
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_deriv]
    refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
    rw [hd]
    exact (hc.of_le (WithTop.coe_le_coe.2 le_top)).sub (ih.const_smul μ)

end AnomDiss
