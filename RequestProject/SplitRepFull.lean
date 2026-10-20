module

public import RequestProject.Liouville
public import RequestProject.CompBounds
public import RequestProject.SplitRep

/-!
# Lemma 3.8 (splitting representation), all orders

For any splitting `ψ` of `B_{μ,ω}` with `n` steps, `P_n h = 𝔼_ζ[h ∘ Ψ_n]`; `Ψ_n` is a `C^∞`
area-preserving lift; and all derivatives of `Ψ_n` and `Ψ_n⁻¹` are bounded uniformly in
`μ ∈ [0,1]`, `ω`, `n` and the Gaussian increments.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {L M : ℕ} {S : ℕ → ℝ}

/-! ### Generic facts about compositions -/

lemma splitMap_congr {ψ ψ' : ℕ → Pt 2 → Pt 2} (ζ : ℕ → Pt 2) {j : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ j → ψ i = ψ' i) : splitMap ψ ζ j = splitMap ψ' ζ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [splitMap]
    rw [ih fun i h1 h2 => h i h1 (by omega), h (j + 1) (by omega) le_rfl]

lemma splitOp_congr (μ : ℝ) (n : ℕ) {ψ ψ' : ℕ → Pt 2 → Pt 2} (g : Pt 2 → ℂ) {j : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ j → ψ i = ψ' i) : splitOp μ n ψ j g = splitOp μ n ψ' j g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [splitOp]
    rw [ih fun i h1 h2 => h i h1 (by omega), h (j + 1) (by omega) le_rfl]

lemma splitInv_rightInverse (ψ g : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2)
    (hg : ∀ i x, ψ i (g i x) = x) (j : ℕ) :
    Function.RightInverse (splitInv g ζ j) (splitMap ψ ζ j) := by
  induction j with
  | zero => intro x; rfl
  | succ j ih =>
    intro x
    simp only [splitInv, splitMap, Function.comp_apply, sub_add_cancel, hg, ih _]

lemma splitMap_eq_compR (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (j : ℕ) :
    splitMap ψ ζ j = compR (fun i y => ψ i (y + ζ i)) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [splitMap, compR, ih]

lemma splitInv_eq_compL (g : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (j : ℕ) :
    splitInv g ζ j = compL (fun i z => g i z - ζ i) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [splitInv, compL, ih]

lemma contDiff_splitMap_infty {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (ζ : ℕ → Pt 2) (j : ℕ) : ContDiff ℝ ∞ (splitMap ψ ζ j) := by
  induction j with
  | zero => exact contDiff_id
  | succ j ih => exact ih.comp ((hψ _).comp (contDiff_id.add contDiff_const))

lemma det_jac_splitMap {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hdet : ∀ i x, (jac (ψ i) x).det = 1) (ζ : ℕ → Pt 2) (j : ℕ) (x : Pt 2) :
    (jac (splitMap ψ ζ j) x).det = 1 := by
  induction j generalizing x with
  | zero =>
    have : jac (splitMap ψ ζ 0) x = 1 := by
      ext a b; simp [jac, splitMap, Matrix.one_apply, Pi.single_apply]
    rw [this, Matrix.det_one]
  | succ j ih =>
    have hc : ContDiff ℝ 1 (splitMap ψ ζ j) := by
      clear ih
      induction j with
      | zero => exact contDiff_id
      | succ j ih2 => exact ih2.comp ((hψ _).comp (contDiff_id.add contDiff_const))
    set f : Pt 2 → Pt 2 := fun y => ψ (j + 1) (y + ζ (j + 1)) with hf
    have hfc : ContDiff ℝ 1 f := (hψ _).comp (contDiff_id.add contDiff_const)
    have hS : splitMap ψ ζ (j + 1) = splitMap ψ ζ j ∘ f := rfl
    rw [hS, jac_comp' ((hc.differentiable one_ne_zero) _) ((hfc.differentiable one_ne_zero) _),
      Matrix.det_mul, ih]
    have hjf : jac f x = jac (ψ (j + 1)) (x + ζ (j + 1)) := by
      ext a b; simp only [jac, Matrix.of_apply, hf]
      rw [fderiv_comp_add_right (f := ψ (j + 1))]
    rw [hjf, hdet, one_mul]

lemma iteratedFDeriv_sub_const_eq {g : Pt 2 → Pt 2} (c : Pt 2) {r : ℕ} (hr : 1 ≤ r) (x : Pt 2) :
    iteratedFDeriv ℝ r (fun z => g z - c) x = iteratedFDeriv ℝ r g x := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have : fderiv ℝ (fun z => g z - c) = fderiv ℝ g := funext fun y => fderiv_sub_const c
  simp only [Function.comp_apply, this]

/-! ### The splitting of `B_{μ,ω}` -/

/-- The canonical inverse flow maps `ψᵢ = Φ_{i/n → (i-1)/n}` of `B_{μ,ω}`. -/
def dampedPsi (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (n i : ℕ) : Pt 2 → Pt 2 :=
  gflow (dampedB cf μ w) ((i : ℝ) / n) (((i : ℝ) - 1) / n)

/-- The forward flow maps `Φ_{(i-1)/n → i/n}`. -/
def dampedPhi (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (n i : ℕ) : Pt 2 → Pt 2 :=
  gflow (dampedB cf μ w) (((i : ℝ) - 1) / n) ((i : ℝ) / n)

/-- A splitting of `B_{μ,ω}` consists of the canonical inverse flow maps. -/
lemma isSplitting_eq (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L)
    {n : ℕ} {ψ : ℕ → Pt 2 → Pt 2} (hψ : IsSplitting (dampedB cf μ w) n ψ) :
    ∀ i, 1 ≤ i → i ≤ n → ψ i = dampedPsi cf μ w n i := by
  intro i hi1 hin
  obtain ⟨Φ, h0, hd, hinv⟩ := hψ i hi1 hin
  have hG := (dampedB_smooth cf hμ w).toGood
  set t₀ : ℝ := ((i - 1 : ℝ) / n)
  set t₁ : ℝ := (i : ℝ) / n
  have hΦ : ∀ x, Φ t₁ x = gflow (dampedB cf μ w) t₀ t₁ x := by
    intro x
    have := hG.eq_gflow (t₀ := t₀) (fun s => hd s x)
    have h2 := congrFun this t₁
    rw [h2, h0]
  funext y
  have hy : Φ t₁ (gflow (dampedB cf μ w) t₁ t₀ y) = y := by
    rw [hΦ, hG.gflow_gflow, hG.gflow_self]
  have := (hinv (gflow (dampedB cf μ w) t₁ t₀ y)).1
  rw [hy] at this
  rw [this]
  rfl

lemma dampedPsi_dampedPhi (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L)
    (n i : ℕ) (x : Pt 2) : dampedPsi cf μ w n i (dampedPhi cf μ w n i x) = x :=
  (dampedB_smooth cf hμ w).toGood.gflow_inv _ _ x

lemma dampedPhi_dampedPsi (cf : ControlFamily L M S) {μ : ℝ} (hμ : 0 ≤ μ) (w : BlockParam L)
    (n i : ℕ) (x : Pt 2) : dampedPhi cf μ w n i (dampedPsi cf μ w n i x) = x :=
  (dampedB_smooth cf hμ w).toGood.gflow_inv _ _ x

lemma abs_step_le {n i : ℕ} (hn : 1 ≤ n) :
    |((i : ℝ) - 1) / n - (i : ℝ) / n| ≤ 1 / n ∧ |(i : ℝ) / n - ((i : ℝ) - 1) / n| ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ((i : ℝ) - 1) / n - (i : ℝ) / n = -(1 / n) := by field_simp; ring
  have e2 : (i : ℝ) / n - ((i : ℝ) - 1) / n = 1 / n := by field_simp; ring
  rw [e1, e2, abs_neg, abs_of_pos (by positivity)]
  exact ⟨le_rfl, le_rfl⟩

lemma one_div_le_one {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) / n ≤ 1 := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_one (by linarith)]; exact this

lemma dampedB_periodic (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L) (s : ℝ)
    (x : Pt 2) (m : Fin 2 → ℤ) : dampedB cf μ w s (x + intVec m) = dampedB cf μ w s x := by
  rw [dampedB_eq]; beta_reduce
  rw [show x + intVec m - w.2 = x - w.2 + intVec m by abel]
  exact (eigenspace_properties _).2.1 _ _


/-- **Lemma 3.8** (splitting representation): `P_n h = 𝔼_ζ[h ∘ Ψ_n]`; each `Ψ_n` is the lift of
an area-preserving diffeomorphism isotopic to the identity, with derivative bounds (for `Ψ_n` and
`Ψ_n⁻¹`) uniform in `n`, `ω`, `μ ∈ [0,1]` and the Gaussian variables. -/
theorem split_representation {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) :
    (∀ μ, 0 ≤ μ → ∀ w n ψ, 1 ≤ n → IsSplitting (dampedB cf μ w) n ψ →
      ∀ h : Pt 2 → ℂ, Continuous h → IsPeriodic h →
        splitOp μ n ψ n h = fun x => ∫ ζ, h (splitMap ψ ζ n x) ∂(gaussSeq (splitVar μ n))) ∧
    (∀ μ, 0 ≤ μ → ∀ w n ψ, 1 ≤ n → IsSplitting (dampedB cf μ w) n ψ → ∀ ζ,
      ContDiff ℝ ∞ (splitMap ψ ζ n) ∧ IsLift (splitMap ψ ζ n) ∧
        ∀ x, (jac (splitMap ψ ζ n) x).det = 1) ∧
    (∀ a : ℕ, 1 ≤ a → ∃ C, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ w n ψ, 1 ≤ n →
      IsSplitting (dampedB cf μ w) n ψ → ∀ ζ, ∃ Ψinv : Pt 2 → Pt 2,
        Function.LeftInverse Ψinv (splitMap ψ ζ n) ∧
        Function.RightInverse Ψinv (splitMap ψ ζ n) ∧
        ∀ x, ‖iteratedFDeriv ℝ a (splitMap ψ ζ n) x‖ ≤ C ∧
          ‖iteratedFDeriv ℝ a Ψinv x‖ ≤ C) := by
  refine ⟨?_, ?_, ?_⟩
  · -- representation
    intro μ hμ w n ψ hn hψ h hc hp
    have heq := isSplitting_eq cf hμ w hψ
    have hG := (dampedB_smooth cf hμ w).toGood
    obtain ⟨B, hB⟩ := periodic_bdd h hc hp
    rw [splitOp_congr μ n h heq]
    funext x
    rw [splitOp_eq_integral μ n (ψ := dampedPsi cf μ w n) (fun i => hG.continuous_gflow _ _) hc hB n x]
    congr 1; funext ζ
    rw [splitMap_congr ζ heq]
  · -- regularity, lift, area preservation
    intro μ hμ w n ψ hn hψ ζ
    have heq := isSplitting_eq cf hμ w hψ
    have hV := dampedB_smooth cf hμ w
    rw [splitMap_congr ζ heq]
    have hsm : ∀ i, ContDiff ℝ ∞ (dampedPsi cf μ w n i) := fun i =>
      contDiff_gflow_of_smooth hV ((abs_step_le hn).1.trans (one_div_le_one hn))
    refine ⟨contDiff_splitMap_infty hsm ζ n,
      splitMap_isLift _ ζ (fun i => gflow_isLift hV.toGood (dampedB_periodic cf μ w) _ _) n,
      det_jac_splitMap (fun i => (hsm i).of_le (by exact_mod_cast natCast_le_inf 1))
        (fun i x => det_jac_gflow hV (dampedB_traceFree cf hμ w) _ _ x) ζ n⟩
  · -- uniform bounds
    intro a ha
    obtain ⟨C0, hC00, hC0⟩ := gflow_smooth_bounds (E := Pt 2) a (dampedBd cf 1)
    obtain ⟨CR, hCR⟩ := compR_bounds (E := Pt 2) a zero_le_one hC00
    obtain ⟨CL, hCL⟩ := compL_bounds (E := Pt 2) a C0 zero_le_one
    refine ⟨max CR CL, fun μ hμ w n ψ hn hψ ζ => ?_⟩
    have heq := isSplitting_eq cf hμ.1 w hψ
    have hV := dampedB_smooth_unif cf hμ w
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set δ : ℝ := C0 / n with hδdef
    have hδ : 0 ≤ δ := by positivity
    have hnδ : (n : ℝ) * δ ≤ C0 := by rw [hδdef]; field_simp; rfl
    have hstep : C0 * (1 / n) = δ := by rw [hδdef]; ring
    rw [splitMap_congr ζ heq]
    refine ⟨splitInv (dampedPhi cf μ w n) ζ n,
      splitInv_leftInverse _ _ ζ (fun i x => dampedPhi_dampedPsi cf hμ.1 w n i x) n,
      splitInv_rightInverse _ _ ζ (fun i x => dampedPsi_dampedPhi cf hμ.1 w n i x) n,
      fun x => ⟨?_, ?_⟩⟩
    · have hf : ∀ i, NearId a δ 1 (fun y => dampedPsi cf μ w n i (y + ζ i)) := by
        intro i
        have habs := (abs_step_le (i := i) hn).1
        obtain ⟨hc, hb⟩ := hC0 _ hV _ _ (habs.trans (one_div_le_one hn))
        refine ⟨hc.comp (contDiff_id.add contDiff_const), fun y => ?_, fun y r hr2 hra => ?_⟩
        · rw [fderiv_comp_add_right (f := dampedPsi cf μ w n i)]
          refine ((hb _).1).trans ?_
          rw [← hstep]; gcongr
        · rw [iteratedFDeriv_comp_add_right]
          refine ((hb _).2 r hr2 hra).trans ?_
          rw [mul_one, ← hstep]; gcongr
      rw [splitMap_eq_compR]
      exact (hCR δ n hδ hnδ _ hf n le_rfl x a ha le_rfl).trans (le_max_left _ _)
    · have hf : ∀ i, NearId a δ 1 (fun z => dampedPhi cf μ w n i z - ζ i) := by
        intro i
        have habs := (abs_step_le (i := i) hn).2
        obtain ⟨hc, hb⟩ := hC0 _ hV _ _ (habs.trans (one_div_le_one hn))
        refine ⟨hc.sub contDiff_const, fun y => ?_, fun y r hr2 hra => ?_⟩
        · rw [fderiv_sub_const]
          refine ((hb _).1).trans ?_
          rw [← hstep]; gcongr
        · rw [iteratedFDeriv_sub_const_eq _ (by omega)]
          refine ((hb _).2 r hr2 hra).trans ?_
          rw [mul_one, ← hstep]; gcongr
      rw [splitInv_eq_compL]
      exact (hCL δ n hδ hnδ _ hf n le_rfl x a ha le_rfl).trans (le_max_right _ _)

end AnomDiss
