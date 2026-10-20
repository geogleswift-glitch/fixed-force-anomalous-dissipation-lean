module

public import RequestProject.FlowAug

/-!
# `C^∞` regularity of flows of smooth fields, with quantitative bounds

For a smooth field `V` on a finite-dimensional space, the flow map `Φ_{t₀ → t}` is `C^∞`; for
`|t - t₀| ≤ 1`, `‖DΦ - I‖ ≤ C |t - t₀|` and `‖D^j Φ‖ ≤ C |t - t₀|` for `2 ≤ j ≤ k`, where `C`
depends only on `k` and the bounds of `V`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff NNReal

noncomputable section

namespace AnomDiss

section Ident

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The flow of the augmented field from `(x, I)` is `(Φ(x), DΦ(x))`. -/
lemma gflow_aug_eq {V : ℝ → E → E} {B : ℕ → ℝ} (hV : SmoothField V B)
    {χ : (E →L[ℝ] E) → (E →L[ℝ] E)} (hχ : ContDiff ℝ ∞ χ) {Bχ : ℕ → ℝ}
    (hBχ : ∀ j J, ‖iteratedFDeriv ℝ j χ J‖ ≤ Bχ j) {R : ℝ} (hχR : ∀ J, ‖J‖ ≤ R → χ J = J)
    {t₀ t : ℝ} (h01 : t₀ ≤ t) (hR : Real.exp (B 1 * (t - t₀)) ≤ R) {x : E}
    {J : ℝ → E →L[ℝ] E} (hJ : IsVarSol V t₀ t x J) :
    ∀ s ∈ Icc t₀ t, gflow (augField V χ) t₀ s (x, ContinuousLinearMap.id ℝ E) =
      (gflow V t₀ s x, J s) := by
  have hW := (hV.aug hχ hBχ).toGood
  have hG := hV.toGood
  intro s hs
  have key := hW.eqOn_Icc (a := t₀) (b := t) (t₀ := t₀) ⟨le_rfl, h01⟩
    (α := fun s => gflow (augField V χ) t₀ s (x, ContinuousLinearMap.id ℝ E))
    (β := fun s => (gflow V t₀ s x, J s))
    (fun r _ => (hW.hasDerivAt_gflow _ r _).hasDerivWithinAt)
    (fun r hr => by
      have h1 := hG.hasDerivAt_gflow t₀ r x
      have h2 := hJ.2 r hr
      have hJr : ‖J r‖ ≤ R := by
        refine (hJ.norm_le hG hr).trans (le_trans ?_ hR)
        change Real.exp (B 1 * (r - t₀)) ≤ Real.exp (B 1 * (t - t₀))
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (sub_le_sub_right hr.2 t₀) (hV.B_nonneg 1))
      have : augField V χ r (gflow V t₀ r x, J r) =
          (V r (gflow V t₀ r x), (fderiv ℝ (V r) (gflow V t₀ r x)).comp (J r)) := by
        simp [augField, hχR _ hJr]
      rw [this]
      exact (h1.prodMk h2).hasDerivWithinAt)
    (by simp [hW.gflow_self, hG.gflow_self, hJ.1])
  exact key hs

/-- Consequently the derivative of the flow is the second component of the augmented flow. -/
lemma hasFDerivAt_gflow_aug {V : ℝ → E → E} {B : ℕ → ℝ} (hV : SmoothField V B)
    {χ : (E →L[ℝ] E) → (E →L[ℝ] E)} (hχ : ContDiff ℝ ∞ χ) {Bχ : ℕ → ℝ}
    (hBχ : ∀ j J, ‖iteratedFDeriv ℝ j χ J‖ ≤ Bχ j) {R : ℝ} (hχR : ∀ J, ‖J‖ ≤ R → χ J = J)
    {t₀ t : ℝ} (h01 : t₀ ≤ t) (hR : Real.exp (B 1 * (t - t₀)) ≤ R) (x : E) :
    HasFDerivAt (gflow V t₀ t)
      (gflow (augField V χ) t₀ t (x, ContinuousLinearMap.id ℝ E)).2 x := by
  obtain ⟨J, hJ⟩ := exists_varSol hV.toGood hV.toC2 h01 x
  rw [gflow_aug_eq hV hχ hBχ hχR h01 hR hJ t ⟨h01, le_rfl⟩]
  exact hJ.hasFDerivAt hV.toGood hV.toC2 ⟨h01, le_rfl⟩

/-- The first-derivative estimate `‖DΦ - I‖ ≤ B₁ e^{B₁} (t - t₀)` for `t₀ ≤ t ≤ t₀ + 1`. -/
lemma norm_fderiv_gflow_sub_id_le {V : ℝ → E → E} {B : ℕ → ℝ} (hV : SmoothField V B)
    {t₀ t : ℝ} (h01 : t₀ ≤ t) (h1 : t ≤ t₀ + 1) (x : E) :
    ‖fderiv ℝ (gflow V t₀ t) x - ContinuousLinearMap.id ℝ E‖ ≤
      (B 1 * Real.exp (B 1)) * (t - t₀) := by
  have h := ((gflow_C2_fwd hV.toGood hV.toC2 h01).2 x).1
  refine h.trans ?_
  have hB := hV.B_nonneg 1
  have : Real.exp (B 1 * (t - t₀)) ≤ Real.exp (B 1) := by
    gcongr; nlinarith
  have h0 : 0 ≤ t - t₀ := by linarith
  calc B 1 * (t - t₀) * Real.exp (B 1 * (t - t₀)) ≤ B 1 * (t - t₀) * Real.exp (B 1) := by
        gcongr
    _ = _ := by ring

end Ident

/-- The statement proved by induction on `k`. -/
def FlowCk (k : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (B : ℕ → ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : ℝ → E → E, SmoothField V B → ∀ t₀ t : ℝ, t₀ ≤ t → t ≤ t₀ + 1 →
      ContDiff ℝ k (gflow V t₀ t) ∧ ∀ x,
        ‖fderiv ℝ (gflow V t₀ t) x - ContinuousLinearMap.id ℝ E‖ ≤ C * (t - t₀) ∧
        ∀ j, 2 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j (gflow V t₀ t) x‖ ≤ C * (t - t₀)

theorem flowCk_zero : FlowCk 0 := by
  intro E _ _ _ B
  refine ⟨max 0 (B 1 * Real.exp (B 1)), le_max_left _ _, fun V hV t₀ t h01 h1 => ⟨?_, fun x => ⟨?_, ?_⟩⟩⟩
  · exact contDiff_zero.2 (hV.toGood.continuous_gflow t₀ t)
  · exact (norm_fderiv_gflow_sub_id_le hV h01 h1 x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
  · intro j hj hjk; omega

theorem flowCk_succ {k : ℕ} (ih : FlowCk k) : FlowCk (k + 1) := by
  intro E _ _ _ B
  set R : ℝ := Real.exp (B 1) + 1 with hRdef
  have hR : 0 < R := by positivity
  set χ : (E →L[ℝ] E) → (E →L[ℝ] E) := truncMap R hR with hχdef
  have hχ : ContDiff ℝ ∞ χ := contDiff_truncMap R hR
  choose Bχ hBχ using fun j => truncMap_bounds (F := E →L[ℝ] E) R hR j
  obtain ⟨C', hC'0, hC'⟩ := ih (E × (E →L[ℝ] E)) (augBound B Bχ)
  refine ⟨max (max 0 (B 1 * Real.exp (B 1))) C', le_max_of_le_left (le_max_left _ _),
    fun V hV t₀ t h01 h1 => ?_⟩
  have hW := hV.aug hχ hBχ
  have hRb : Real.exp (B 1 * (t - t₀)) ≤ R := by
    have hB := hV.B_nonneg 1
    have : Real.exp (B 1 * (t - t₀)) ≤ Real.exp (B 1) := by gcongr; nlinarith
    linarith
  obtain ⟨hGc, hGb⟩ := hC' (augField V χ) hW t₀ t h01 h1
  set G := gflow (augField V χ) t₀ t with hGdef
  set ι : E → E × (E →L[ℝ] E) := fun x => (x, ContinuousLinearMap.id ℝ E) with hι
  set D' : E → E →L[ℝ] E := fun x => (G (ι x)).2 with hD'
  have hHas : ∀ x, HasFDerivAt (gflow V t₀ t) (D' x) x := fun x =>
    hasFDerivAt_gflow_aug hV hχ hBχ (fun J hJ => truncMap_eq R hR hJ) h01 hRb x
  have hDeq : fderiv ℝ (gflow V t₀ t) = D' := funext fun x => (hHas x).fderiv
  have hιc : ContDiff ℝ ∞ ι := contDiff_id.prodMk contDiff_const
  have hD'C : ContDiff ℝ k D' := contDiff_snd.comp (hGc.comp (hιc.of_le (natCast_le_inf k)))
  have hle : max 0 (B 1 * Real.exp (B 1)) ≤ max (max 0 (B 1 * Real.exp (B 1))) C' :=
    le_max_left _ _
  have hle' : C' ≤ max (max 0 (B 1 * Real.exp (B 1))) C' := le_max_right _ _
  have h0 : 0 ≤ t - t₀ := by linarith
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · have : ContDiff ℝ ((k : WithTop ℕ∞) + 1) (gflow V t₀ t) :=
      contDiff_succ_iff_hasFDerivAt.2 ⟨D', hD'C, hHas⟩
    exact_mod_cast this
  · exact (norm_fderiv_gflow_sub_id_le hV h01 h1 x).trans
      (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hle) h0)
  · intro j hj2 hjk
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hik : i ≤ k := by omega
    have hi1 : 1 ≤ i := by omega
    rw [← norm_iteratedFDeriv_fderiv, hDeq]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hle' h0)
    rcases Nat.lt_or_ge i 2 with hi | hi
    · -- first derivative of `D'`: use `snd ∘ I ∘ inl = 0`
      obtain rfl : i = 1 := by omega
      rw [norm_iteratedFDeriv_one]
      have hk1 : (1 : WithTop ℕ∞) ≤ k := by exact_mod_cast hik
      have hGd : DifferentiableAt ℝ G (ι x) :=
        (hGc.differentiable (by
          intro h; rw [h] at hk1; exact absurd hk1 (by simp))) _
      have hιd : HasFDerivAt ι (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)) x :=
        (hasFDerivAt_id x).prodMk (hasFDerivAt_const _ x)
      have hcomp : HasFDerivAt D' ((ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
          ((fderiv ℝ G (ι x)).comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)))) x :=
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp x
          (hGd.hasFDerivAt.comp x hιd)
      rw [hcomp.fderiv]
      have e : (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
          ((fderiv ℝ G (ι x)).comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))) =
          (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
          ((fderiv ℝ G (ι x) - ContinuousLinearMap.id ℝ _).comp
            (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))) := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
        simp
      rw [e]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine (mul_le_of_le_one_left (norm_nonneg _)
        (ContinuousLinearMap.norm_snd_le ℝ E (E →L[ℝ] E))).trans ?_
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine (mul_le_of_le_one_right (norm_nonneg _)
        (ContinuousLinearMap.norm_inl_le_one ℝ E (E →L[ℝ] E))).trans ?_
      exact (hGb (ι x)).1
    · -- higher derivatives
      have hik' : (i : WithTop ℕ∞) ≤ k := by exact_mod_cast hik
      set c : E × (E →L[ℝ] E) := (0, ContinuousLinearMap.id ℝ E)
      have hsplit : D' = (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)) ∘
          ((fun z => G (z + c)) ∘ (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))) := by
        funext y; simp [hD', hι, c]
      have hGs : ContDiff ℝ k (fun z => G (z + c)) := hGc.comp (contDiff_id.add contDiff_const)
      rw [hsplit]
      refine ((ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).norm_iteratedFDeriv_comp_left
        (hGs.comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)).contDiff).contDiffAt hik').trans ?_
      refine (mul_le_of_le_one_left (norm_nonneg _)
        (ContinuousLinearMap.norm_snd_le ℝ E (E →L[ℝ] E))).trans ?_
      refine (norm_iteratedFDeriv_comp_clm_le' hGs (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))
        (ContinuousLinearMap.norm_inl_le_one ℝ E (E →L[ℝ] E)) x hik').trans ?_
      rw [iteratedFDeriv_comp_add_right]
      exact (hGb _).2 i hi hik

theorem flowCk (k : ℕ) : FlowCk k := by
  induction k with
  | zero => exact flowCk_zero
  | succ k ih => exact flowCk_succ ih

/-- **`C^k` regularity of flows of smooth fields, with bounds** (forward and backward times):
for `|t - t₀| ≤ 1`, `Φ_{t₀ → t}` is `C^k`, `‖DΦ - I‖ ≤ C |t - t₀|` and
`‖D^j Φ‖ ≤ C |t - t₀|` for `2 ≤ j ≤ k`, with `C` depending only on `k` and the bounds `B`. -/
theorem gflow_smooth_bounds (k : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : ℝ → E → E, SmoothField V B → ∀ t₀ t : ℝ, |t - t₀| ≤ 1 →
      ContDiff ℝ k (gflow V t₀ t) ∧ ∀ x,
        ‖fderiv ℝ (gflow V t₀ t) x - ContinuousLinearMap.id ℝ E‖ ≤ C * |t - t₀| ∧
        ∀ j, 2 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j (gflow V t₀ t) x‖ ≤ C * |t - t₀| := by
  obtain ⟨C, hC0, hC⟩ := flowCk k E B
  refine ⟨C, hC0, fun V hV t₀ t ht => ?_⟩
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)] at ht ⊢
    exact hC V hV t₀ t h (by linarith)
  · have he : gflow V t₀ t = gflow (GoodField.revField V (2 * t₀)) t₀ (2 * t₀ - t) :=
      funext fun x => hV.toGood.gflow_rev t₀ t x
    have ha : |t - t₀| = 2 * t₀ - t - t₀ := by
      rw [abs_of_nonpos (sub_nonpos.2 h)]; ring
    rw [ha] at ht ⊢
    rw [he]
    exact hC _ (hV.rev (2 * t₀)) t₀ (2 * t₀ - t) (by linarith) (by linarith)

/-- Flow maps of smooth fields over times `|t - t₀| ≤ 1` are `C^∞`. -/
theorem contDiff_gflow_of_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {V : ℝ → E → E} {B : ℕ → ℝ} (hV : SmoothField V B) {t₀ t : ℝ}
    (ht : |t - t₀| ≤ 1) : ContDiff ℝ ∞ (gflow V t₀ t) :=
  contDiff_infty.2 fun k => by
    obtain ⟨C, -, hC⟩ := gflow_smooth_bounds (E := E) k B
    exact (hC V hV t₀ t ht).1

end AnomDiss
