module

public import RequestProject.VortL4

/-!
# The vorticity `L⁴` estimates

* `vort4_root4_growth`: if `|curl g| ≤ A` on `[a,b]`, then
  `‖curl v(b)‖₄ ≤ ‖curl v(a)‖₄ + A (b - a)`;
* `vort4_sqrt_growth`: if `|g| ≤ B` on `[a,b]` and `ν > 0`, then
  `‖curl v(b)‖₄² ≤ ‖curl v(a)‖₄² + (3B²/ν)(b - a)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace AnomDiss

section main

variable {ν : ℝ} {v₀ : Pt 2 → Pt 2} {g : ℝ → Pt 2 → Pt 2} {v : ℝ → Pt 2 → Pt 2}
  {p : ℝ → Pt 2 → ℝ}

lemma l2sq_sq_eq (W : Pt 2 → ℝ) : l2sq (fun x => W x ^ 2) = ∫ x in cell 2, W x ^ 4 := by
  unfold l2sq; congr 1; funext x; ring

lemma mvort_props {φ : Pt 2 → ℝ} (k : IsKer φ) (hv : IsClassicalNS 1 ν v₀ g v p) {β : ℝ}
    (reg : IsParabolicC12 1 β v) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ 2 (mvort φ v s) ∧ IsPeriodic (mvort φ v s) := by
  refine ⟨?_, isPeriodic_mc φ (isPeriodic_curl2 (hv.periodic_u s hs))⟩
  have := contDiff_mc (n := 2) k.c2 k.2 (continuous_curl2 (reg.smooth_x s hs))
  exact this

/-- The integral form of the evolution of `∫ W⁴` for the mollified vorticity. -/
lemma mvort_integral_form {φ : Pt 2 → ℝ} (k : IsKer φ) {β : ℝ} (hβ : 0 < β)
    (reg : IsParabolicC12 1 β v) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∀ t ∈ Icc a b, l2sq (fun x => mvort φ v t x ^ 2) = l2sq (fun x => mvort φ v a x ^ 2) +
      ∫ s in a..t, ∫ x in cell 2, 2 * mvort φ v s x ^ 2 * (2 * mvort φ v s x * mvortT φ v s x)) ∧
    ContinuousOn (fun s => ∫ x in cell 2, 2 * mvort φ v s x ^ 2 *
      (2 * mvort φ v s x * mvortT φ v s x)) (Icc a b) := by
  have hsub : Icc a b ×ˢ (univ : Set (Pt 2)) ⊆ Icc 0 1 ×ˢ univ :=
    prod_mono (Icc_subset_Icc ha hb) subset_rfl
  have c1 := (continuousOn_mvort k reg).mono hsub
  have c2 := (continuousOn_mvortT k hβ reg).mono hsub
  have := l2sq_integral_form hab (fun s x => mvort φ v s x ^ 2)
    (fun s x => 2 * mvort φ v s x * mvortT φ v s x) (c1.pow 2) ((continuousOn_const.mul c1).mul c2)
    (fun s hs x => by
      have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
      convert (hasDerivAt_mvort k hβ reg hs' x).pow 2 using 1
      push_cast; ring)
  exact this

/-- Per-mollifier inviscid estimate. -/
lemma mvort_root4 {φ : Pt 2 → ℝ} (k : IsKer φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hφε : ∀ y, φ y ≠ 0 → ‖y‖ < ε) (hν : 0 ≤ ν)
    (hv : IsClassicalNS 1 ν v₀ g v p) {β : ℝ} (hβ : 0 < β) (reg : IsParabolicC12 1 β v)
    (regp : IsParabolicC01 1 β p) (hg : ∀ t, ContDiff ℝ 1 (g t)) {B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁)
    (hB₂0 : 0 ≤ B₂) (hB₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i x, ‖pd i (v t) x‖ ≤ B₁)
    (hB₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j x, ‖pd i (pd j (v t)) x‖ ≤ B₂) {a b A : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) (hA0 : 0 ≤ A) (hA : ∀ t ∈ Icc a b, ∀ x, |curl2 (g t) x| ≤ A) :
    (∫ x in cell 2, mvort φ v b x ^ 4) ^ (1 / ((4 : ℕ) : ℝ)) ≤
      (∫ x in cell 2, mvort φ v a x ^ 4) ^ (1 / ((4 : ℕ) : ℝ)) +
        (A + 8 * B₁ * B₂ * ε) * (b - a) := by
  obtain ⟨hform, hcont⟩ := mvort_integral_form k hβ reg ha hab hb
  have key := root_growth (n := 4) (c := A + 8 * B₁ * B₂ * ε) hab (by norm_num) hform hcont
    (fun t _ => setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) ?_
  · rwa [l2sq_sq_eq, l2sq_sq_eq] at key
  intro s hs Z hZ hfZ
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs.1.le, hs.2.le.trans hb⟩
  have hv2 := reg.smooth_x s hs01
  obtain ⟨hW2, hWp⟩ := mvort_props k hv reg hs01
  have hcg : ∀ j : Fin 2, Continuous (cmp (g s) j) := fun j =>
    (continuous_apply j).comp (hg s).continuous
  have cG : Continuous fun x => mc (pd 0 φ) (cmp (g s) 1) x - mc (pd 1 φ) (cmp (g s) 0) x :=
    (differentiable_mc (k.pd 0).c1 (k.pd 0).2 (hcg 1)).continuous.sub
      (differentiable_mc (k.pd 1).c1 (k.pd 1).2 (hcg 0)).continuous
  have cconv : Continuous (conv (v s) (curl2 (v s))) :=
    continuous_conv_of_C1 _ hv2.continuous _ (contDiff_curl2 hv2)
  have cR : Continuous fun x => conv (v s) (mvort φ v s) x - mc φ (conv (v s) (curl2 (v s))) x :=
    (continuous_conv_of_C1 _ hv2.continuous _ (hW2.of_le (by norm_num))).sub
      (differentiable_mc k.c1 k.2 cconv).continuous
  have hrate := rate_inviscid (hv2.of_le (by norm_num)) (hv.periodic_u s hs01) (hv.div_free s hs01)
    hW2 hWp cG cR hν (Wt := mvortT φ v s) (fun x => mvortT_eq k hv reg regp
      (fun t => (hg t).continuous) hs01 x) (a := A) (κ := 8 * B₁ * B₂ * ε) ?_ ?_
  · have hcube := integral_abs_cube_le hW2.continuous hZ (by rwa [l2sq_sq_eq] at hfZ)
    have hc0 : 0 ≤ A + 8 * B₁ * B₂ * ε := by positivity
    calc (∫ x in cell 2, 2 * mvort φ v s x ^ 2 * (2 * mvort φ v s x * mvortT φ v s x))
        ≤ 4 * (A + 8 * B₁ * B₂ * ε) * ∫ x in cell 2, |mvort φ v s x| ^ 3 := hrate
      _ ≤ 4 * (A + 8 * B₁ * B₂ * ε) * Z ^ 3 := by gcongr
      _ = ((4 : ℕ) : ℝ) * (A + 8 * B₁ * B₂ * ε) * Z ^ (4 - 1) := by norm_num
  · intro x
    rw [← mc_curl2 k (hg s) x]
    exact abs_mc_le k.cont k.2 hφ0 hφ1 (hA s ⟨hs.1.le, hs.2.le⟩) x
  · intro x
    have := commutator_bound k hφ0 hφ1 hφε hv2.continuous (contDiff_curl2 hv2)
      (by positivity : (0 : ℝ) ≤ 2 * B₁) (fun j x y => cmp_lip hv2 (hB₁ s hs01) j x y)
      (pd_curl2_abs_le hv2 (hB₂ s hs01)) x
    calc _ ≤ 2 * (2 * B₁ * ε * (2 * B₂)) := this
      _ = 8 * B₁ * B₂ * ε := by ring

/-- Per-mollifier viscous estimate. -/
lemma mvort_root2 {φ : Pt 2 → ℝ} (k : IsKer φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hφε : ∀ y, φ y ≠ 0 → ‖y‖ < ε) (hν : 0 < ν)
    (hv : IsClassicalNS 1 ν v₀ g v p) {β : ℝ} (hβ : 0 < β) (reg : IsParabolicC12 1 β v)
    (regp : IsParabolicC01 1 β p) (hg : ∀ t, ContDiff ℝ 1 (g t)) (hgp : ∀ t, IsPeriodic (g t))
    {B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂) (hB₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i x, ‖pd i (v t) x‖ ≤ B₁)
    (hB₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j x, ‖pd i (pd j (v t)) x‖ ≤ B₂) {a b B : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) (hB : ∀ t ∈ Icc a b, ∀ x, ‖g t x‖ ≤ B) :
    (∫ x in cell 2, mvort φ v b x ^ 4) ^ (1 / ((2 : ℕ) : ℝ)) ≤
      (∫ x in cell 2, mvort φ v a x ^ 4) ^ (1 / ((2 : ℕ) : ℝ)) +
        (3 * B ^ 2 / ν + 32 * B₁ ^ 2 * B₂ * ε) * (b - a) := by
  obtain ⟨hform, hcont⟩ := mvort_integral_form k hβ reg ha hab hb
  have key := root_growth (n := 2) (c := 3 * B ^ 2 / ν + 32 * B₁ ^ 2 * B₂ * ε) hab (by norm_num)
    hform hcont (fun t _ => setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) ?_
  · rwa [l2sq_sq_eq, l2sq_sq_eq] at key
  intro s hs Z hZ hfZ
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs.1.le, hs.2.le.trans hb⟩
  have hv2 := reg.smooth_x s hs01
  obtain ⟨hW2, hWp⟩ := mvort_props k hv reg hs01
  have hcg : ∀ j : Fin 2, Continuous (cmp (g s) j) := fun j =>
    (continuous_apply j).comp (hg s).continuous
  have hcgp : ∀ j : Fin 2, IsPeriodic (cmp (g s) j) := fun j x n => by simp [cmp, hgp s x n]
  have cconv : Continuous (conv (v s) (curl2 (v s))) :=
    continuous_conv_of_C1 _ hv2.continuous _ (contDiff_curl2 hv2)
  have cR : Continuous fun x => conv (v s) (mvort φ v s) x - mc φ (conv (v s) (curl2 (v s))) x :=
    (continuous_conv_of_C1 _ hv2.continuous _ (hW2.of_le (by norm_num))).sub
      (differentiable_mc k.c1 k.2 cconv).continuous
  have heq : ∀ x, mvortT φ v s x = -conv (v s) (mvort φ v s) x + ν * lap (mvort φ v s) x +
      ((pd 0 (mc φ (cmp (g s) 1)) x - pd 1 (mc φ (cmp (g s) 0)) x) +
        (conv (v s) (mvort φ v s) x - mc φ (conv (v s) (curl2 (v s))) x)) := by
    intro x
    rw [pd_mc k.c1 k.2 (hcg 1), pd_mc k.c1 k.2 (hcg 0)]
    exact mvortT_eq k hv reg regp (fun t => (hg t).continuous) hs01 x
  have hgb : ∀ j : Fin 2, ∀ x, |mc φ (cmp (g s) j) x| ≤ B := fun j x =>
    abs_mc_le k.cont k.2 hφ0 hφ1 (fun z => (abs_apply_le_norm _ j).trans
      (hB s ⟨hs.1.le, hs.2.le⟩ z)) x
  have hrate := rate_viscous (hv2.of_le (by norm_num)) (hv.periodic_u s hs01)
    (hv.div_free s hs01) hW2 hWp (contDiff_mc (n := 1) k.c1 k.2 (hcg 0))
    (contDiff_mc (n := 1) k.c1 k.2 (hcg 1)) (isPeriodic_mc φ (hcgp 0)) (isPeriodic_mc φ (hcgp 1))
    cR hν heq (hgb 0) (hgb 1) (κ := 8 * B₁ * B₂ * ε) ?_
  · have hM : ∀ x, |mvort φ v s x| ≤ 2 * B₁ := fun x =>
      abs_mc_le k.cont k.2 hφ0 hφ1 (fun z => curl2_abs_le (hB₁ s hs01) z) x
    have hsq := integral_sq_le_of_four hW2.continuous hZ (by rwa [l2sq_sq_eq] at hfZ)
    have hcube := integral_abs_cube_le_sup hW2.continuous hM
    have hκ0 : 0 ≤ 8 * B₁ * B₂ * ε := by positivity
    have hint0 : 0 ≤ ∫ x in cell 2, mvort φ v s x ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
    have hb6 : 0 ≤ 6 * B ^ 2 / ν := by positivity
    calc (∫ x in cell 2, 2 * mvort φ v s x ^ 2 * (2 * mvort φ v s x * mvortT φ v s x))
        ≤ 6 * B ^ 2 / ν * (∫ x in cell 2, mvort φ v s x ^ 2) +
          4 * (8 * B₁ * B₂ * ε) * ∫ x in cell 2, |mvort φ v s x| ^ 3 := hrate
      _ ≤ 6 * B ^ 2 / ν * Z + 4 * (8 * B₁ * B₂ * ε) * (2 * B₁ * Z) := by
          gcongr
          calc (∫ x in cell 2, |mvort φ v s x| ^ 3) ≤ 2 * B₁ * ∫ x in cell 2, mvort φ v s x ^ 2 :=
                hcube
            _ ≤ 2 * B₁ * Z := by gcongr
      _ = ((2 : ℕ) : ℝ) * (3 * B ^ 2 / ν + 32 * B₁ ^ 2 * B₂ * ε) * Z ^ (2 - 1) := by
          push_cast; ring
  · intro x
    have := commutator_bound k hφ0 hφ1 hφε hv2.continuous (contDiff_curl2 hv2)
      (by positivity : (0 : ℝ) ≤ 2 * B₁) (fun j x y => cmp_lip hv2 (hB₁ s hs01) j x y)
      (pd_curl2_abs_le hv2 (hB₂ s hs01)) x
    calc _ ≤ 2 * (2 * B₁ * ε * (2 * B₂)) := this
      _ = 8 * B₁ * B₂ * ε := by ring

/-- The mollified `L⁴` functional approximates the true one. -/
lemma mvort4_approx {φ : Pt 2 → ℝ} (k : IsKer φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1)
    {ε : ℝ} (hφε : ∀ y, φ y ≠ 0 → ‖y‖ < ε) {β : ℝ} (reg : IsParabolicC12 1 β v)
    {B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hB₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i x, ‖pd i (v t) x‖ ≤ B₁)
    (hB₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j x, ‖pd i (pd j (v t)) x‖ ≤ B₂) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |(∫ x in cell 2, mvort φ v t x ^ 4) - vort4 (v t)| ≤ (4 * (2 * B₁) ^ 3 * (4 * B₂)) * ε := by
  have hv2 := reg.smooth_x t ht
  have cw := continuous_curl2 hv2
  have cW : Continuous (mvort φ v t) := (differentiable_mc k.c1 k.2 cw).continuous
  have hpt : ∀ x, |mvort φ v t x ^ 4 - curl2 (v t) x ^ 4| ≤ 4 * (2 * B₁) ^ 3 * (4 * B₂) * ε := by
    intro x
    have hM1 : |mvort φ v t x| ≤ 2 * B₁ :=
      abs_mc_le k.cont k.2 hφ0 hφ1 (fun z => curl2_abs_le (hB₁ t ht) z) x
    have hM2 := curl2_abs_le (hB₁ t ht) x
    have happ : |mvort φ v t x - curl2 (v t) x| ≤ 2 * (2 * B₂) * ε :=
      abs_mc_sub_le_lip k hφ0 hφ1 hφε cw (by positivity) (curl2_lip hv2 (hB₂ t ht)) x
    calc _ ≤ 4 * (2 * B₁) ^ 3 * |mvort φ v t x - curl2 (v t) x| := abs_four_sub_le hM1 hM2
      _ ≤ 4 * (2 * B₁) ^ 3 * (2 * (2 * B₂) * ε) := by gcongr
      _ = _ := by ring
  have hsub : (∫ x in cell 2, mvort φ v t x ^ 4) - vort4 (v t) =
      ∫ x in cell 2, (mvort φ v t x ^ 4 - curl2 (v t) x ^ 4) :=
    (icell_sub (cW.pow 4) (cw.pow 4)).symm
  rw [hsub, abs_le]
  constructor
  · have := icell_mono (f := fun _ => -(4 * (2 * B₁) ^ 3 * (4 * B₂) * ε))
      (g := fun x => mvort φ v t x ^ 4 - curl2 (v t) x ^ 4) continuous_const
      ((cW.pow 4).sub (cw.pow 4)) fun x => (abs_le.1 (hpt x)).1
    rw [icell_const] at this
    linarith
  · have := icell_mono (g := fun _ => 4 * (2 * B₁) ^ 3 * (4 * B₂) * ε)
      (f := fun x => mvort φ v t x ^ 4 - curl2 (v t) x ^ 4) ((cW.pow 4).sub (cw.pow 4))
      continuous_const fun x => (abs_le.1 (hpt x)).2
    rw [icell_const] at this
    linarith

/-- **Vorticity `L⁴` estimate, inviscid form.**  For a classical solution on `[0,1]` whose
force has `C¹` slices, `‖curl v(b)‖₄ ≤ ‖curl v(a)‖₄ + A (b - a)` whenever `|curl g| ≤ A` on
`[a,b]`. -/
theorem vort4_root4_growth (hν : 0 ≤ ν) (hv : IsClassicalNS 1 ν v₀ g v p)
    (hg : ∀ t, ContDiff ℝ 1 (g t)) {a b A : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hA : ∀ t ∈ Icc a b, ∀ x, |curl2 (g t) x| ≤ A) :
    vort4 (v b) ^ (1 / 4 : ℝ) ≤ vort4 (v a) ^ (1 / 4 : ℝ) + A * (b - a) := by
  obtain ⟨β, hβ, -, reg, regp⟩ := hv.regular
  obtain ⟨B₁, B₂, hB₁0, hB₂0, hB₁, hB₂⟩ := parabolic_deriv_bounds reg
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA a ⟨le_rfl, hab⟩ 0)
  have ha1 : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hb1 : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have := limit_root (n := 4) (c := A) (d := b - a) (K := 4 * (2 * B₁) ^ 3 * (4 * B₂))
    (K' := 8 * B₁ * B₂) (Ya := vort4 (v a)) (Yb := vort4 (v b)) (by norm_num) fun ε hε => by
      obtain ⟨φ, hφs, hφc, hφ0, hφ1, hφε⟩ := exists_mollifier hε
      have k : IsKer φ := ⟨hφs, hφc⟩
      refine ⟨∫ x in cell 2, mvort φ v a x ^ 4, ∫ x in cell 2, mvort φ v b x ^ 4,
        setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity,
        setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity,
        mvort4_approx k hφ0 hφ1 hφε reg hB₁0 hB₂0 hB₁ hB₂ ha1,
        mvort4_approx k hφ0 hφ1 hφε reg hB₁0 hB₂0 hB₁ hB₂ hb1, ?_⟩
      have h := mvort_root4 k hφ0 hφ1 hε.le hφε hν hv hβ reg regp hg hB₁0 hB₂0 hB₁ hB₂ ha hab hb
        hA0 hA
      calc _ ≤ _ := h
        _ = _ := by ring
  norm_num at this ⊢
  exact this

/-- **Vorticity `L⁴` estimate, viscous form.**  For a classical solution on `[0,1]` whose
force has periodic `C¹` slices, `‖curl v(b)‖₄² ≤ ‖curl v(a)‖₄² + (3B²/ν)(b - a)` whenever
`|g| ≤ B` on `[a,b]`. -/
theorem vort4_sqrt_growth (hν : 0 < ν) (hv : IsClassicalNS 1 ν v₀ g v p)
    (hg : ∀ t, ContDiff ℝ 1 (g t)) (hgp : ∀ t, IsPeriodic (g t)) {a b B : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) (hB : ∀ t ∈ Icc a b, ∀ x, ‖g t x‖ ≤ B) :
    vort4 (v b) ^ (1 / 2 : ℝ) ≤ vort4 (v a) ^ (1 / 2 : ℝ) + 3 * B ^ 2 / ν * (b - a) := by
  obtain ⟨β, hβ, -, reg, regp⟩ := hv.regular
  obtain ⟨B₁, B₂, hB₁0, hB₂0, hB₁, hB₂⟩ := parabolic_deriv_bounds reg
  have ha1 : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hb1 : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have := limit_root (n := 2) (c := 3 * B ^ 2 / ν) (d := b - a)
    (K := 4 * (2 * B₁) ^ 3 * (4 * B₂)) (K' := 32 * B₁ ^ 2 * B₂) (Ya := vort4 (v a))
    (Yb := vort4 (v b)) (by norm_num) fun ε hε => by
      obtain ⟨φ, hφs, hφc, hφ0, hφ1, hφε⟩ := exists_mollifier hε
      have k : IsKer φ := ⟨hφs, hφc⟩
      refine ⟨∫ x in cell 2, mvort φ v a x ^ 4, ∫ x in cell 2, mvort φ v b x ^ 4,
        setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity,
        setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity,
        mvort4_approx k hφ0 hφ1 hφε reg hB₁0 hB₂0 hB₁ hB₂ ha1,
        mvort4_approx k hφ0 hφ1 hφε reg hB₁0 hB₂0 hB₁ hB₂ hb1, ?_⟩
      have h := mvort_root2 k hφ0 hφ1 hε.le hφε hν hv hβ reg regp hg hgp hB₁0 hB₂0 hB₁ hB₂ ha
        hab hb hB
      calc _ ≤ _ := h
        _ = _ := by ring
  norm_num at this ⊢
  exact this

end main

end AnomDiss
