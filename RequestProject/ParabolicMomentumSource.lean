module

public import RequestProject.ParabolicFirstOrderOperations
public import RequestProject.PhaseForceHolderBounds

/-!
# Analytic data for the genuine momentum source

The original first-order parabolic regularity of velocity and pressure
implies the required Hölder regularity of their actual convective term
and pressure gradient. Time clamping extends these bounds and continuity
globally. The actual constructed force is also fixed by unit time
clamping, because its support is strictly inside the unit interval.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

theorem BddOn.mul {d : ℕ} {T : ℝ} {f g : ℝ → Pt d → ℝ}
    (hf : BddOn T f) (hg : BddOn T g) :
    BddOn T (fun t x => f t x * g t x) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨max A 0 * max B 0, fun t ht x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hA t ht x).trans (le_max_left _ _))
    ((hB t ht x).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

theorem BddOn.sub {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {f g : ℝ → Pt d → E} (hf : BddOn T f) (hg : BddOn T g) :
    BddOn T (fun t x => f t x - g t x) := by
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    sub_eq_add_neg] using hf.add (hg.clm (-ContinuousLinearMap.id ℝ E))

/-- A bound on the unit slab becomes a global bound for a genuinely
time-clamped function. -/
theorem BddOn.uniform_of_unit_clamped {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → Pt d → E} (hg : BddOn 1 g)
    (hc : ∀ t : ℝ, g (projIcc 0 1 (by norm_num) t) = g t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖g t x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨max C 0, le_max_right _ _, fun t x => ?_⟩
  have hb := hC (projIcc 0 1 (by norm_num) t) (Subtype.mem _) x
  rw [hc t] at hb
  exact hb.trans (le_max_left _ _)

/-- A parabolic Hölder modulus supplies one spatial Hölder constant for
all real times when the function is genuinely clamped in time. -/
theorem ParHolder.uniform_spatial_of_unit_clamped {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ} (hβ : 0 < β)
    {g : ℝ → Pt d → E} (hg : ParHolder 1 β g)
    (hc : ∀ t : ℝ, g (projIcc 0 1 (by norm_num) t) = g t) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t x y, ‖g t x - g t y‖ ≤ H * ‖x - y‖ ^ β := by
  obtain ⟨H, hH⟩ := hg
  refine ⟨max H 0, le_max_right _ _, fun t x y => ?_⟩
  have hh := hH (projIcc 0 1 (by norm_num) t) (Subtype.mem _)
    (projIcc 0 1 (by norm_num) t) (Subtype.mem _) x y
  rw [hc t] at hh
  simp only [sub_self, abs_zero, Real.zero_rpow (by linarith : β / 2 ≠ 0), add_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (norm_nonneg _) _))

/-- An admissible force vanishes outside a compact subinterval of `(0,1)`,
so its actual values are fixed by unit time clamping. -/
theorem IsAdmissibleForce.unit_clamped {f : ℝ → Pt 2 → Pt 2}
    (hf : IsAdmissibleForce f) (t : ℝ) :
    f (projIcc 0 1 (by norm_num) t) = f t := by
  obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hf.compact_support
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [projIcc_of_mem (by norm_num) ht]
  · have ht' : t < 0 ∨ 1 < t := by
      simpa only [mem_Icc, not_and_or, not_le] using ht
    rcases ht' with ht | ht
    · rw [projIcc_of_le_left (by norm_num) ht.le]
      change f 0 = f t
      rw [hsupp 0 (by intro h; linarith [h.1]), hsupp t (by intro h; linarith [h.1])]
    · rw [projIcc_of_right_le (by norm_num) ht.le]
      change f 1 = f t
      rw [hsupp 1 (by intro h; linarith [h.2]), hsupp t (by intro h; linarith [h.2])]

def momentumSourceComponent (phase : Phase) (v : ℝ → Pt 2 → Pt 2)
    (p : ℝ → Pt 2 → ℝ) (i : Fin 2) (t : ℝ) (x : Pt 2) : ℂ :=
  ((gForce phase t x i - conv (v t) (v t) x i - pd i (p t) x : ℝ) : ℂ)

theorem momentumConvComponent_parHolder {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    {v : ℝ → Pt 2 → Pt 2} (hv : IsParabolicC01 1 β v) (i : Fin 2) :
    ParHolder 1 β (fun t x => conv (v t) (v t) x i) := by
  have hV (j : Fin 2) : ParHolder 1 β (fun t x => v t x j) :=
    (hv.parHolder hβ₀ hβ₁).clm (ContinuousLinearMap.proj j)
  have hD (j : Fin 2) : ParHolder 1 β (fun t x => pd j (v t) x i) :=
    (hv.holder_d1 j).clm (ContinuousLinearMap.proj i)
  have hbV (j : Fin 2) : BddOn 1 (fun t x => v t x j) :=
    hv.bdd.clm (ContinuousLinearMap.proj j)
  have hbD (j : Fin 2) : BddOn 1 (fun t x => pd j (v t) x i) :=
    (hv.bdd_d1 j).clm (ContinuousLinearMap.proj i)
  simpa only [conv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two] using
    ((hV 0).mul (hD 0) (hbV 0) (hbD 0)).add
      ((hV 1).mul (hD 1) (hbV 1) (hbD 1))

theorem momentumConvComponent_bddOn {β : ℝ} {v : ℝ → Pt 2 → Pt 2}
    (hv : IsParabolicC01 1 β v) (i : Fin 2) :
    BddOn 1 (fun t x => conv (v t) (v t) x i) := by
  have hbV (j : Fin 2) : BddOn 1 (fun t x => v t x j) :=
    hv.bdd.clm (ContinuousLinearMap.proj j)
  have hbD (j : Fin 2) : BddOn 1 (fun t x => pd j (v t) x i) :=
    (hv.bdd_d1 j).clm (ContinuousLinearMap.proj i)
  simpa only [conv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two] using
    ((hbV 0).mul (hbD 0)).add ((hbV 1).mul (hbD 1))

theorem momentumSourceComponent_parHolder {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    {v : ℝ → Pt 2 → Pt 2} {p : ℝ → Pt 2 → ℝ}
    (hv : IsParabolicC01 1 β v) (hp : IsParabolicC01 1 β p)
    (phase : Phase) (i : Fin 2) : ParHolder 1 β (momentumSourceComponent phase v p i) := by
  have hG : ParHolder 1 β (fun t x => gForce phase t x i) :=
    (gForce_parHolder phase 1 hβ₀.le hβ₁).clm (ContinuousLinearMap.proj i)
  exact ((hG.sub (momentumConvComponent_parHolder hβ₀.le hβ₁.le hv i)).sub
    (hp.holder_d1 i)).clm Complex.ofRealCLM

theorem momentumSourceComponent_bddOn {β : ℝ}
    {v : ℝ → Pt 2 → Pt 2} {p : ℝ → Pt 2 → ℝ}
    (hv : IsParabolicC01 1 β v) (hp : IsParabolicC01 1 β p)
    (phase : Phase) (i : Fin 2) : BddOn 1 (momentumSourceComponent phase v p i) := by
  obtain ⟨K, _, hK⟩ := forceD_uniform_holderBd (α := 0) (by norm_num) (by norm_num) 0
  have hG : BddOn 1 (gForce phase) := by
    refine ⟨K, fun t ht x => ?_⟩
    simpa only [forceD_zero_eq] using (hK phase t).1 x
  have hGi := hG.clm (ContinuousLinearMap.proj (R := ℝ) i)
  exact ((hGi.sub (momentumConvComponent_bddOn hv i)).sub (hp.bdd_d1 i)).clm Complex.ofRealCLM

theorem momentumSourceComponent_unit_clamped
    (phase : Phase) {v : ℝ → Pt 2 → Pt 2} {p : ℝ → Pt 2 → ℝ}
    (hvc : ∀ t : ℝ, v (projIcc 0 1 (by norm_num) t) = v t)
    (hpc : ∀ t : ℝ, p (projIcc 0 1 (by norm_num) t) = p t) (i : Fin 2) (t : ℝ) :
    momentumSourceComponent phase v p i (projIcc 0 1 (by norm_num) t) =
      momentumSourceComponent phase v p i t := by
  funext x
  unfold momentumSourceComponent
  rw [hvc t, hpc t, (force_regularity.1 phase).1.unit_clamped t]

theorem momentumSourceComponent_periodic (phase : Phase)
    {v : ℝ → Pt 2 → Pt 2} {p : ℝ → Pt 2 → ℝ}
    (hvp : ∀ t, IsPeriodic (v t)) (hpp : ∀ t, IsPeriodic (p t)) (i : Fin 2) (t : ℝ) :
    IsPeriodic (momentumSourceComponent phase v p i t) := by
  have hconv : IsPeriodic (conv (v t) (v t)) := by
    intro x n
    unfold conv
    apply Finset.sum_congr rfl
    intro j _
    rw [hvp t x n, isPeriodic_pd (v t) (hvp t) j x n]
  intro x n
  unfold momentumSourceComponent
  rw [(gForce_slice_props phase t).1 x n, hconv x n, isPeriodic_pd (p t) (hpp t) i x n]

/-- All analytic hypotheses needed by the genuine heat Duhamel Schauder
theorem hold for the momentum source of a first-order parabolic velocity
and pressure, with the original time-clamp identities. -/
theorem momentumSourceComponent_analytic_data {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    {v : ℝ → Pt 2 → Pt 2} {p : ℝ → Pt 2 → ℝ}
    (hv : IsParabolicC01 1 β v) (hp : IsParabolicC01 1 β p)
    (hvc : ∀ t : ℝ, v (projIcc 0 1 (by norm_num) t) = v t)
    (hpc : ∀ t : ℝ, p (projIcc 0 1 (by norm_num) t) = p t)
    (phase : Phase) (i : Fin 2) :
    Continuous (Function.uncurry (momentumSourceComponent phase v p i)) ∧
      ParHolder 1 β (momentumSourceComponent phase v p i) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖momentumSourceComponent phase v p i t x‖ ≤ C) ∧
      (∃ H : ℝ, 0 ≤ H ∧ ∀ t x y,
        ‖momentumSourceComponent phase v p i t x - momentumSourceComponent phase v p i t y‖ ≤
          H * ‖x - y‖ ^ β) := by
  have hpar := momentumSourceComponent_parHolder hβ₀ hβ₁ hv hp phase i
  have hclamp := momentumSourceComponent_unit_clamped phase hvc hpc i
  exact ⟨continuous_of_parHolder_unit_clamped hβ₀ hpar hclamp, hpar,
    (momentumSourceComponent_bddOn hv hp phase i).uniform_of_unit_clamped hclamp,
    hpar.uniform_spatial_of_unit_clamped hβ₀ hclamp⟩

end AnomDiss
