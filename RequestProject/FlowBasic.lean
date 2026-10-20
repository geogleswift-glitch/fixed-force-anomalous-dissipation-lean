module

public import Mathlib

/-!
# Global flows of bounded, Lipschitz, time-dependent vector fields

For a time-dependent vector field `V : ℝ → E → E` which is continuous in time, uniformly bounded
and uniformly Lipschitz in space, we construct the global flow `gflow V t₀ t x` (the value at time
`t` of the solution starting from `x` at time `t₀`) and prove its basic properties: the flow
equation, uniqueness, the cocycle law, Lipschitz bounds and closeness to the identity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Standing assumptions on a time-dependent vector field: continuity in time, a uniform bound
`M` and a uniform spatial Lipschitz constant `K`. -/
structure GoodField (V : ℝ → E → E) (M K : ℝ≥0) : Prop where
  cont : ∀ x, Continuous fun t => V t x
  bound : ∀ t x, ‖V t x‖ ≤ M
  lip : ∀ t, LipschitzWith K (V t)

namespace GoodField

variable {V : ℝ → E → E} {M K : ℝ≥0}

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma picard (hV : GoodField V M K) (t₀ : ℝ) (x : E) (T : ℝ≥0) :
    IsPicardLindelof V (tmin := t₀ - T) (tmax := t₀ + T)
      ⟨t₀, by constructor <;> simp⟩ x (M * T) 0 M K where
  lipschitzOnWith t _ := (hV.lip t).lipschitzOnWith
  continuousOn x _ := (hV.cont x).continuousOn
  norm_le t _ y _ := hV.bound t y
  mul_max_le := by
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_zero, sub_zero,
      NNReal.coe_mul, le_refl]

omit [CompleteSpace E] in
/-- Uniqueness of global solutions. -/
lemma unique (hV : GoodField V M K) {α β : ℝ → E} {t₀ : ℝ}
    (hα : ∀ t, HasDerivAt α (V t (α t)) t) (hβ : ∀ t, HasDerivAt β (V t (β t)) t)
    (h : α t₀ = β t₀) : α = β :=
  ODE_solution_unique_univ (s := fun _ => univ) (fun t => (hV.lip t).lipschitzOnWith)
    (fun t => ⟨hα t, trivial⟩) (fun t => ⟨hβ t, trivial⟩) h

omit [CompleteSpace E] in
/-- Two solutions on a closed interval around `t₀` which agree at `t₀` agree on the interval. -/
lemma eqOn_Icc (hV : GoodField V M K) {α β : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (V t (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (V t (β t)) (Icc a b) t)
    (h : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  have hαc : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousWithinAt
  have hβc : ContinuousOn β (Icc a b) := fun t ht => (hβ t ht).continuousWithinAt
  intro t ht
  rcases le_total t₀ t with h1 | h1
  · have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    have key := ODE_solution_unique (v := V) (K := K) (fun s => hV.lip s)
      (hαc.mono hsub) (fun s hs => ?_) (hβc.mono hsub) (fun s hs => ?_) h
    · exact key ⟨h1, ht.2⟩
    · refine (hα s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hs.1, hs.2⟩
    · refine (hβ s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hs.1, hs.2⟩
  · have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    have key := ODE_solution_unique_of_mem_Icc_left (v := V) (K := K) (s := fun _ => univ)
      (fun s _ => (hV.lip s).lipschitzOnWith)
      (hαc.mono hsub) (fun s hs => ?_) (fun _ _ => trivial) (hβc.mono hsub) (fun s hs => ?_)
      (fun _ _ => trivial) h
    · exact key ⟨ht.1, h1⟩
    · refine (hα s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans ht₀.2⟩
    · refine (hβ s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans ht₀.2⟩

/-- Global existence of solutions. -/
lemma exists_global (hV : GoodField V M K) (t₀ : ℝ) (x : E) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t, HasDerivAt α (V t (α t)) t := by
  have hloc : ∀ T : ℝ≥0, ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt α (V t (α t)) (Icc (t₀ - T) (t₀ + T)) t := fun T =>
    (hV.picard t₀ x T).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hα using hloc
  have hmem : ∀ T : ℝ≥0, t₀ ∈ Icc (t₀ - T) (t₀ + T) := fun T => by constructor <;> simp
  -- agreement of the local solutions
  have hagree : ∀ T T' : ℝ≥0, T ≤ T' → EqOn (α T) (α T') (Icc (t₀ - T) (t₀ + T)) := by
    intro T T' hTT'
    have hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T') (t₀ + T') :=
      Icc_subset_Icc (by linarith [NNReal.coe_le_coe.2 hTT']) (by linarith [NNReal.coe_le_coe.2 hTT'])
    refine hV.eqOn_Icc (hmem T) (hα T) (fun t ht => ?_) ((hα0 T).trans (hα0 T').symm)
    exact (hα T' t (hsub ht)).mono hsub
  set τ : ℝ → ℝ≥0 := fun t => ⟨|t - t₀| + 1, by positivity⟩ with hτ
  refine ⟨fun t => α (τ t) t, ?_, fun t => ?_⟩
  · simpa using hα0 (τ t₀)
  · set T : ℝ≥0 := ⟨|t - t₀| + 2, by positivity⟩
    have hT : t ∈ Ioo (t₀ - T) (t₀ + T) := by
      change t₀ - (|t - t₀| + 2) < t ∧ t < t₀ + (|t - t₀| + 2)
      constructor <;> linarith [le_abs_self (t - t₀), neg_le_abs (t - t₀)]
    have hev : (fun s => α (τ s) s) =ᶠ[𝓝 t] α T := by
      have hU : ∀ᶠ s in 𝓝 t, |s - t₀| < |t - t₀| + 1 := by
        have hc : Continuous fun s => |s - t₀| := by fun_prop
        exact hc.continuousAt.eventually_lt continuousAt_const (by linarith)
      filter_upwards [hU] with s hs
      refine hagree (τ s) T ?_ ?_
      · show |s - t₀| + 1 ≤ |t - t₀| + 2; linarith
      · change t₀ - (|s - t₀| + 1) ≤ s ∧ s ≤ t₀ + (|s - t₀| + 1)
        constructor <;> linarith [le_abs_self (s - t₀), neg_le_abs (s - t₀)]
    have hd := (hα T t (Ioo_subset_Icc_self hT)).hasDerivAt (Icc_mem_nhds hT.1 hT.2)
    have heq : α (τ t) t = α T t := hev.eq_of_nhds
    show HasDerivAt (fun s => α (τ s) s) (V t (α (τ t) t)) t
    rw [heq]
    exact hd.congr_of_eventuallyEq hev

end GoodField

open Classical in
/-- The global flow: `gflow V t₀ t x` is the value at time `t` of the solution of `ẏ = V(t, y)`
with `y(t₀) = x` (and `x` itself if no global solution exists). -/
def gflow (V : ℝ → E → E) (t₀ t : ℝ) (x : E) : E :=
  if h : ∃ α : ℝ → E, α t₀ = x ∧ ∀ s, HasDerivAt α (V s (α s)) s then h.choose t else x

namespace GoodField

variable {V : ℝ → E → E} {M K : ℝ≥0}

lemma gflow_spec (hV : GoodField V M K) (t₀ : ℝ) (x : E) :
    gflow V t₀ t₀ x = x ∧ ∀ t, HasDerivAt (fun s => gflow V t₀ s x) (V t (gflow V t₀ t x)) t := by
  have h := hV.exists_global t₀ x
  simp only [gflow, dif_pos h]
  exact h.choose_spec

lemma gflow_self (hV : GoodField V M K) (t₀ : ℝ) (x : E) : gflow V t₀ t₀ x = x :=
  (hV.gflow_spec t₀ x).1

lemma hasDerivAt_gflow (hV : GoodField V M K) (t₀ t : ℝ) (x : E) :
    HasDerivAt (fun s => gflow V t₀ s x) (V t (gflow V t₀ t x)) t :=
  (hV.gflow_spec t₀ x).2 t

lemma continuous_gflow_time (hV : GoodField V M K) (t₀ : ℝ) (x : E) :
    Continuous fun s => gflow V t₀ s x :=
  continuous_iff_continuousAt.2 fun t => (hV.hasDerivAt_gflow t₀ t x).continuousAt

/-- Any global solution is given by the flow. -/
lemma eq_gflow (hV : GoodField V M K) {α : ℝ → E} {t₀ : ℝ}
    (hα : ∀ t, HasDerivAt α (V t (α t)) t) : α = fun t => gflow V t₀ t (α t₀) :=
  hV.unique hα (fun t => hV.hasDerivAt_gflow t₀ t _) (hV.gflow_self t₀ _).symm

/-- The cocycle law `Φ_{t₁ → t₂} ∘ Φ_{t₀ → t₁} = Φ_{t₀ → t₂}`. -/
lemma gflow_gflow (hV : GoodField V M K) (t₀ t₁ t₂ : ℝ) (x : E) :
    gflow V t₁ t₂ (gflow V t₀ t₁ x) = gflow V t₀ t₂ x := by
  have h := hV.eq_gflow (t₀ := t₁) (fun t => hV.hasDerivAt_gflow t₀ t x)
  exact (congrFun h t₂).symm

lemma gflow_inv (hV : GoodField V M K) (t₀ t₁ : ℝ) (x : E) :
    gflow V t₁ t₀ (gflow V t₀ t₁ x) = x := by
  rw [hV.gflow_gflow, hV.gflow_self]

/-- The flow moves points by at most `M |t - t₀|`. -/
lemma norm_gflow_sub_le (hV : GoodField V M K) (t₀ t : ℝ) (x : E) :
    ‖gflow V t₀ t x - x‖ ≤ M * |t - t₀| := by
  have hd : ∀ s, HasDerivAt (fun s => gflow V t₀ s x) (V s (gflow V t₀ s x)) s :=
    fun s => hV.hasDerivAt_gflow t₀ s x
  rcases le_total t₀ t with h | h
  · have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => gflow V t₀ s x) (f' := fun s => V s (gflow V t₀ s x)) (C := M)
      (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => hV.bound _ _) t ⟨h, le_rfl⟩
    beta_reduce at key
    rw [hV.gflow_self] at key
    rwa [abs_of_nonneg (sub_nonneg.2 h)]
  · have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => gflow V t₀ s x) (f' := fun s => V s (gflow V t₀ s x)) (C := M)
      (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => hV.bound _ _) t₀ ⟨h, le_rfl⟩
    beta_reduce at key
    rw [hV.gflow_self, norm_sub_rev] at key
    rwa [abs_of_nonpos (sub_nonpos.2 h), neg_sub]

/-- Forward Lipschitz bound for the flow. -/
lemma dist_gflow_le_of_le (hV : GoodField V M K) {t₀ t : ℝ} (h : t₀ ≤ t) (x y : E) :
    dist (gflow V t₀ t x) (gflow V t₀ t y) ≤ dist x y * Real.exp (K * (t - t₀)) := by
  have hd : ∀ z s, HasDerivAt (fun s => gflow V t₀ s z) (V s (gflow V t₀ s z)) s :=
    fun z s => hV.hasDerivAt_gflow t₀ s z
  have := dist_le_of_trajectories_ODE (v := V) (K := K) (a := t₀) (b := t)
    (f := fun s => gflow V t₀ s x) (g := fun s => gflow V t₀ s y) (δ := dist x y)
    (fun s => hV.lip s) (hV.continuous_gflow_time t₀ x).continuousOn
    (fun s _ => (hd x s).hasDerivWithinAt) (hV.continuous_gflow_time t₀ y).continuousOn
    (fun s _ => (hd y s).hasDerivWithinAt) (by simp [hV.gflow_self]) t ⟨h, le_rfl⟩
  exact this

/-- The time-reversed field. -/
def revField (V : ℝ → E → E) (c : ℝ) : ℝ → E → E := fun s y => -V (c - s) y

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma revField_good (hV : GoodField V M K) (c : ℝ) : GoodField (revField V c) M K where
  cont x := ((hV.cont x).comp (continuous_const.sub continuous_id)).neg
  bound t x := by simpa [revField] using hV.bound (c - t) x
  lip t := by
    show LipschitzWith K (fun y => -V (c - t) y)
    exact (hV.lip (c - t)).neg

lemma gflow_rev (hV : GoodField V M K) (t₀ t : ℝ) (x : E) :
    gflow V t₀ t x = gflow (revField V (2 * t₀)) t₀ (2 * t₀ - t) x := by
  have hR := hV.revField_good (2 * t₀)
  have hα : ∀ s, HasDerivAt (fun s => gflow V t₀ (2 * t₀ - s) x)
      (revField V (2 * t₀) s (gflow V t₀ (2 * t₀ - s) x)) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (2 * t₀)
    have h1 := (hV.hasDerivAt_gflow t₀ (2 * t₀ - s) x).scomp s h2
    simpa [revField, Function.comp_def] using h1
  have := hR.eq_gflow (t₀ := t₀) hα
  have h2 := congrFun this (2 * t₀ - t)
  simp only [sub_sub_cancel, show 2 * t₀ - t₀ = t₀ by ring, hV.gflow_self] at h2
  exact h2

/-- Two-sided Lipschitz bound for the flow. -/
lemma dist_gflow_le (hV : GoodField V M K) (t₀ t : ℝ) (x y : E) :
    dist (gflow V t₀ t x) (gflow V t₀ t y) ≤ dist x y * Real.exp (K * |t - t₀|) := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact hV.dist_gflow_le_of_le h x y
  · rw [hV.gflow_rev t₀ t x, hV.gflow_rev t₀ t y, abs_of_nonpos (sub_nonpos.2 h)]
    have := (hV.revField_good (2 * t₀)).dist_gflow_le_of_le (t₀ := t₀) (t := 2 * t₀ - t)
      (by linarith) x y
    convert this using 3; ring

lemma lipschitz_gflow (hV : GoodField V M K) (t₀ t : ℝ) :
    LipschitzWith (⟨Real.exp (K * |t - t₀|), (Real.exp_pos _).le⟩ : ℝ≥0) (gflow V t₀ t) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [mul_comm]; exact hV.dist_gflow_le t₀ t x y

lemma continuous_gflow (hV : GoodField V M K) (t₀ t : ℝ) : Continuous (gflow V t₀ t) :=
  (hV.lipschitz_gflow t₀ t).continuous

/-- `Φ - id` is Lipschitz with a small constant over short times. -/
lemma norm_gflow_sub_sub_le (hV : GoodField V M K) (t₀ t : ℝ) (x y : E) :
    ‖(gflow V t₀ t x - x) - (gflow V t₀ t y - y)‖ ≤
      K * |t - t₀| * Real.exp (K * |t - t₀|) * ‖x - y‖ := by
  set D : ℝ → E := fun s => (gflow V t₀ s x - x) - (gflow V t₀ s y - y) with hD
  have hd : ∀ s, HasDerivAt D (V s (gflow V t₀ s x) - V s (gflow V t₀ s y)) s := by
    intro s
    have := ((hV.hasDerivAt_gflow t₀ s x).sub_const x).sub
      ((hV.hasDerivAt_gflow t₀ s y).sub_const y)
    exact this
  have hbd : ∀ s ∈ uIcc t₀ t, ‖V s (gflow V t₀ s x) - V s (gflow V t₀ s y)‖ ≤
      K * Real.exp (K * |t - t₀|) * ‖x - y‖ := by
    intro s hs
    have h1 := (hV.lip s).dist_le_mul (gflow V t₀ s x) (gflow V t₀ s y)
    have h2 := hV.dist_gflow_le t₀ s x y
    have h3 : Real.exp (K * |s - t₀|) ≤ Real.exp (K * |t - t₀|) := by
      have := abs_sub_left_of_mem_uIcc hs
      gcongr
    rw [← dist_eq_norm]
    calc dist (V s (gflow V t₀ s x)) (V s (gflow V t₀ s y))
        ≤ K * dist (gflow V t₀ s x) (gflow V t₀ s y) := h1
      _ ≤ K * (dist x y * Real.exp (K * |t - t₀|)) := by
          gcongr; exact h2.trans (by gcongr)
      _ = K * Real.exp (K * |t - t₀|) * ‖x - y‖ := by rw [dist_eq_norm]; ring
  have key := (convex_uIcc t₀ t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hbd left_mem_uIcc right_mem_uIcc
  have hD0 : D t₀ = 0 := by simp [hD, hV.gflow_self]
  rw [hD0, sub_zero, Real.norm_eq_abs] at key
  calc ‖D t‖ ≤ K * Real.exp (K * |t - t₀|) * ‖x - y‖ * |t - t₀| := key
    _ = _ := by ring

/-- One step of the inverse flow: `y - ψ(y) = (t₁ - t₀) V(t₀, ψ(y)) + O((t₁ - t₀)²)` where
`ψ = Φ_{t₁ → t₀}`, for a field which is moreover Lipschitz in time. -/
lemma norm_inv_step_le (hV : GoodField V M K) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (y : E) :
    ‖(y - gflow V t₁ t₀ y) - (t₁ - t₀) • V t₀ (gflow V t₁ t₀ y)‖ ≤
      (Lt + K * M) * (t₁ - t₀) ^ 2 := by
  set z := gflow V t₁ t₀ y with hz
  have hX1 : gflow V t₀ t₁ z = y := by rw [hz, hV.gflow_gflow, hV.gflow_self]
  set G : ℝ → E := fun s => gflow V t₀ s z - (s - t₀) • V t₀ z with hG
  have hd : ∀ s, HasDerivAt G (V s (gflow V t₀ s z) - V t₀ z) s := by
    intro s
    have h1 := ((hasDerivAt_id s).sub_const t₀).smul_const (V t₀ z)
    have := (hV.hasDerivAt_gflow t₀ s z).fun_sub h1
    simpa [G, Pi.sub_apply] using this
  have hbd : ∀ s ∈ Icc t₀ t₁, ‖V s (gflow V t₀ s z) - V t₀ z‖ ≤ (Lt + K * M) * (t₁ - t₀) := by
    intro s hs
    have e1 := hLt s t₀ (gflow V t₀ s z)
    have e2 := (hV.lip t₀).dist_le_mul (gflow V t₀ s z) z
    have e3 := hV.norm_gflow_sub_le t₀ s z
    rw [dist_eq_norm, dist_eq_norm] at e2
    have hs0 : |s - t₀| ≤ t₁ - t₀ := by
      rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have hLt0 : 0 ≤ Lt := by
      have := hLt (t₀ + 1) t₀ z
      have h0 : (0:ℝ) ≤ Lt * |t₀ + 1 - t₀| := (norm_nonneg _).trans this
      simpa using h0
    calc ‖V s (gflow V t₀ s z) - V t₀ z‖
        = ‖(V s (gflow V t₀ s z) - V t₀ (gflow V t₀ s z)) + (V t₀ (gflow V t₀ s z) - V t₀ z)‖ := by
          congr 1; abel
      _ ≤ Lt * |s - t₀| + K * (M * |s - t₀|) := by
          refine (norm_add_le _ _).trans (add_le_add e1 (e2.trans ?_))
          gcongr
      _ ≤ Lt * (t₁ - t₀) + K * (M * (t₁ - t₀)) := by gcongr
      _ = (Lt + K * M) * (t₁ - t₀) := by ring
  have key := (convex_Icc t₀ t₁).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hbd ⟨le_rfl, h⟩ ⟨h, le_rfl⟩
  have e : G t₁ - G t₀ = (y - z) - (t₁ - t₀) • V t₀ z := by
    simp only [hG, hX1, hV.gflow_self, sub_self, zero_smul, sub_zero]; abel
  rw [e, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at key
  calc _ ≤ (Lt + K * M) * (t₁ - t₀) * (t₁ - t₀) := key
    _ = _ := by ring

lemma gronwallBound_zero_le {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound 0 K ε x ≤ ε * x * Real.exp (K * x) := by
  rcases eq_or_lt_of_le hK with h | h
  · subst h; simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 h.ne']
    simp only [zero_mul, zero_add]
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have := Real.add_one_le_exp (-(K * x))
      have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (K * x)]
    calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) := by gcongr
      _ = ε * x * Real.exp (K * x) := by field_simp

/-- Dependence of the flow on the field (forward times). -/
lemma dist_gflow_field_le_of_le (hV : GoodField V M K) {W : ℝ → E → E} {M' K' : ℝ≥0}
    (hW : GoodField W M' K') {ε : ℝ} (hε0 : 0 ≤ ε) {t₀ t : ℝ} (h : t₀ ≤ t)
    (hε : ∀ s ∈ Icc t₀ t, ∀ x, ‖V s x - W s x‖ ≤ ε) (x : E) :
    dist (gflow V t₀ t x) (gflow W t₀ t x) ≤ ε * (t - t₀) * Real.exp (K * (t - t₀)) := by
  have key := dist_le_of_approx_trajectories_ODE (v := V) (K := K) (a := t₀) (b := t)
    (f := fun s => gflow V t₀ s x) (g := fun s => gflow W t₀ s x) (δ := 0)
    (εf := 0) (εg := ε) (f' := fun s => V s (gflow V t₀ s x))
    (g' := fun s => W s (gflow W t₀ s x))
    (fun s => hV.lip s) (hV.continuous_gflow_time t₀ x).continuousOn
    (fun s _ => (hV.hasDerivAt_gflow t₀ s x).hasDerivWithinAt) (fun s _ => by simp)
    (hW.continuous_gflow_time t₀ x).continuousOn
    (fun s _ => (hW.hasDerivAt_gflow t₀ s x).hasDerivWithinAt)
    (fun s hs => by
      rw [dist_eq_norm, norm_sub_rev]; exact hε s (Ico_subset_Icc_self hs) _)
    (by simp [hV.gflow_self, hW.gflow_self]) t ⟨h, le_rfl⟩
  rw [zero_add] at key
  exact key.trans (gronwallBound_zero_le K.2 hε0)

/-- Dependence of the flow on the field (both time directions). -/
lemma dist_gflow_field_le (hV : GoodField V M K) {W : ℝ → E → E} {M' K' : ℝ≥0}
    (hW : GoodField W M' K') {ε : ℝ} (hε0 : 0 ≤ ε) (t₀ t : ℝ)
    (hε : ∀ s ∈ uIcc t₀ t, ∀ x, ‖V s x - W s x‖ ≤ ε) (x : E) :
    dist (gflow V t₀ t x) (gflow W t₀ t x) ≤ ε * |t - t₀| * Real.exp (K * |t - t₀|) := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact hV.dist_gflow_field_le_of_le hW hε0 h
      (fun s hs x => hε s (Icc_subset_uIcc hs) x) x
  · rw [hV.gflow_rev t₀ t x, hW.gflow_rev t₀ t x, abs_of_nonpos (sub_nonpos.2 h)]
    have := (hV.revField_good (2 * t₀)).dist_gflow_field_le_of_le (hW.revField_good (2 * t₀))
      hε0 (t₀ := t₀) (t := 2 * t₀ - t) (by linarith) (fun s hs y => ?_) x
    · convert this using 3 <;> ring
    · have e : revField V (2 * t₀) s y - revField W (2 * t₀) s y =
          -(V (2 * t₀ - s) y - W (2 * t₀ - s) y) := by simp only [revField]; abel
      rw [e, norm_neg]
      refine hε _ ?_ y
      rw [uIcc_of_ge h]
      constructor <;> linarith [hs.1, hs.2]

end GoodField

end AnomDiss
