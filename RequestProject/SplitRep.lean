module

public import RequestProject.SplitConvergence

/-!
# The probabilistic representation of the split operator

`P_j h(x) = 𝔼_ζ h(Ψ_j(x))` where `Ψ_j = f_1 ∘ ⋯ ∘ f_j`, `f_i(y) = ψ_i(y + ζ_i)`, and the `ζ_i` are
independent Gaussian increments (the first part of Lemma 3.8).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

instance gaussSeq_isProb (v : ℝ≥0) : IsProbabilityMeasure (gaussSeq v) := by
  unfold gaussSeq; infer_instance

/-- Resampling one coordinate of the Gaussian sequence does not change its law. -/
lemma map_update_gaussSeq (v : ℝ≥0) (k : ℕ) :
    ((gaussSeq v).prod (gauss2 v)).map (fun p : (ℕ → Pt 2) × Pt 2 => Function.update p.1 k p.2) =
      gaussSeq v := by
  have hmeas : Measurable (fun p : (ℕ → Pt 2) × Pt 2 => Function.update p.1 k p.2) := by
    fun_prop
  unfold gaussSeq
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  classical
  have hpre : (fun p : (ℕ → Pt 2) × Pt 2 => Function.update p.1 k p.2) ⁻¹' (Set.pi s t) =
      (Set.pi (s.erase k : Set ℕ) t) ×ˢ (if k ∈ s then t k else univ) := by
    ext ⟨ζ, ζ'⟩
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · obtain ⟨hik, his⟩ := hi
        have := h i his
        rwa [Function.update_of_ne hik] at this
      · split_ifs with hk
        · have := h k hk
          rwa [Function.update_self] at this
        · trivial
    · rintro ⟨h1, h2⟩ i his
      by_cases hik : i = k
      · subst hik
        rw [Function.update_self]
        simp only [his, if_true] at h2
        exact h2
      · rw [Function.update_of_ne hik]
        exact h1 i ⟨hik, his⟩
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre,
    Measure.prod_prod]
  have hP : (Measure.infinitePi fun _ : ℕ => gauss2 v) (Set.pi (s.erase k : Set ℕ) t) =
      ∏ i ∈ s.erase k, gauss2 v (t i) := Measure.infinitePi_pi _ (fun i _ => ht i)
  rw [hP]
  split_ifs with hk
  · rw [Finset.prod_erase_mul _ _ hk]
  · rw [measure_univ, mul_one, Finset.erase_eq_of_notMem hk]

lemma splitMap_succ (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) (j : ℕ) (x : Pt 2) :
    splitMap ψ ζ (j + 1) x = splitMap ψ ζ j (ψ (j + 1) (x + ζ (j + 1))) := rfl

/-- `Ψ_j` only depends on `ζ_1, …, ζ_j`. -/
lemma splitMap_update (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) {j k : ℕ} (hjk : j < k) (z : Pt 2) :
    splitMap ψ (Function.update ζ k z) j = splitMap ψ ζ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    rw [splitMap_succ, splitMap_succ, ih (by omega), Function.update_of_ne (by omega)]

lemma continuous_splitMap {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, Continuous (ψ i)) (j : ℕ) :
    Continuous fun p : (ℕ → Pt 2) × Pt 2 => splitMap ψ p.1 j p.2 := by
  induction j with
  | zero => exact continuous_snd
  | succ j ih =>
    have h1 : Continuous fun p : (ℕ → Pt 2) × Pt 2 =>
        (p.1, ψ (j + 1) (p.2 + p.1 (j + 1))) :=
      continuous_fst.prodMk ((hψ _).comp (continuous_snd.add
        ((continuous_apply (j + 1)).comp continuous_fst)))
    exact ih.comp h1

/-- **Lemma 3.8, representation part**: `P_j h(x) = 𝔼_ζ h(Ψ_j(x))` for continuous bounded `h`. -/
theorem splitOp_eq_integral (μ : ℝ) (n : ℕ) {ψ : ℕ → Pt 2 → Pt 2} (hψ : ∀ i, Continuous (ψ i))
    {g : Pt 2 → ℂ} (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (j : ℕ) (x : Pt 2) :
    splitOp μ n ψ j g x = ∫ ζ, g (splitMap ψ ζ j x) ∂(gaussSeq (splitVar μ n)) := by
  set v := splitVar μ n
  induction j generalizing x with
  | zero => simp [splitOp_zero, splitMap]
  | succ j ih =>
    rw [splitOp_succ]
    unfold heatOp
    simp only [Function.comp_apply, ih]
    -- integrand on the product space
    set F : (ℕ → Pt 2) × Pt 2 → ℂ := fun p => g (splitMap ψ p.1 j (ψ (j + 1) (x + p.2)))
      with hF
    have hFc : Continuous F := by
      have := continuous_splitMap hψ j
      exact hg.comp (this.comp (continuous_fst.prodMk ((hψ _).comp
        (continuous_const.add continuous_snd))))
    have hFi : Integrable F ((gaussSeq v).prod (gauss2 v)) :=
      Integrable.of_bound hFc.aestronglyMeasurable B (Eventually.of_forall fun p => hB _)
    have h1 : ∫ ζ', ∫ ζ, F (ζ, ζ') ∂(gaussSeq v) ∂(gauss2 v) =
        ∫ p, F p ∂((gaussSeq v).prod (gauss2 v)) := (integral_prod_symm F hFi).symm
    simp only [hF] at h1
    rw [h1]
    -- change of variables by resampling coordinate `j + 1`
    have hmeas : Measurable (fun p : (ℕ → Pt 2) × Pt 2 => Function.update p.1 (j + 1) p.2) := by
      fun_prop
    have hG : Continuous fun ζ : ℕ → Pt 2 => g (splitMap ψ ζ (j + 1) x) :=
      hg.comp ((continuous_splitMap hψ (j + 1)).comp (continuous_id.prodMk continuous_const))
    conv_rhs => rw [← map_update_gaussSeq v (j + 1)]
    rw [integral_map hmeas.aemeasurable hG.aestronglyMeasurable]
    congr 1; funext p
    rw [splitMap_succ, splitMap_update ψ p.1 (by omega), Function.update_self, add_comm x]

end AnomDiss
