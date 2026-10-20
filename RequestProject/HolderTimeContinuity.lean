module

public import RequestProject.ForceRegularity
public import RequestProject.TimeSmoothForceContinuity

/-!
# Continuity of every Hölder-valued time derivative

The difference-quotient definition in `IsSmoothHolderValued` already forces
continuity of every derivative in the full Hölder norm. This uses the norm
triangle inequality and homogeneity, without any PDE existence input.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holderNorm_smul (α c : ℝ) (f : Pt d → E) :
    holderNorm α (c • f) = ‖c‖ₑ * holderNorm α f := by
  simp only [holderNorm, Pi.smul_apply, ← smul_sub, enorm_smul,
    mul_div_assoc, ← ENNReal.mul_iSup, mul_add]

/-- A derivative in the full Hölder norm implies continuity in that same norm. -/
theorem holderNorm_increment_tendsto_zero {α : ℝ} {f : ℝ → Pt d → E}
    {f' : Pt d → E} {t : ℝ} (hfin : holderNorm α f' < ⊤)
    (hd : Tendsto (fun h : ℝ => holderNorm α
      (h⁻¹ • (f (t + h) - f t) - f')) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => holderNorm α (f (t + h) - f t)) (𝓝 0) (𝓝 0) := by
  let C : ℝ≥0∞ := 1 + holderNorm α f'
  have hC : C ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨by simp, hfin.ne⟩
  have herr : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      holderNorm α (h⁻¹ • (f (t + h) - f t) - f') < 1 :=
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      holderNorm α (f (t + h) - f t) ≤ ‖h‖ₑ * C := by
    filter_upwards [herr, self_mem_nhdsWithin] with h he hh
    have hn : h ≠ 0 := by simpa using hh
    have heq : h⁻¹ • (f (t + h) - f t) =
        (h⁻¹ • (f (t + h) - f t) - f') + f' := by abel
    have hquot : holderNorm α (h⁻¹ • (f (t + h) - f t)) ≤ C := by
      rw [heq]
      exact (holderNorm_add_le _ _ _).trans (add_le_add he.le le_rfl)
    calc
      holderNorm α (f (t + h) - f t) =
          holderNorm α (h • (h⁻¹ • (f (t + h) - f t))) := by
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = ‖h‖ₑ * holderNorm α (h⁻¹ • (f (t + h) - f t)) := holderNorm_smul _ _ _
      _ ≤ ‖h‖ₑ * C := mul_le_mul_right hquot _
  have hb' : ∀ᶠ h : ℝ in 𝓝 0,
      holderNorm α (f (t + h) - f t) ≤ ‖h‖ₑ * C := by
    filter_upwards [eventually_nhdsWithin_iff.mp hb] with h hh
    by_cases hn : h = 0
    · simp [hn, holderNorm_zero']
    · exact hh (by simpa using hn)
  have hnorm : Tendsto (fun h : ℝ => ‖h‖ₑ) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_norm_eq_enorm, norm_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (continuous_norm.tendsto (0 : ℝ))
  have hbound := ENNReal.Tendsto.mul_const hnorm (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_mul] using hbound) (Eventually.of_forall fun _ => zero_le) hb'

/-- The derivative witnesses in `IsSmoothHolderValued` are all continuous
in the full Hölder norm, including derivatives of arbitrarily high order. -/
theorem IsSmoothHolderValued.exists_continuous_derivatives {α : ℝ}
    {f : ℝ → Pt d → E} (hf : IsSmoothHolderValued α f) :
    ∃ D : ℕ → ℝ → Pt d → E, D 0 = f ∧
      (∀ r t, holderNorm α (D r t) < ⊤) ∧
      (∀ r t, Tendsto (fun h : ℝ => holderNorm α
        (h⁻¹ • (D r (t + h) - D r t) - D (r + 1) t)) (𝓝[≠] 0) (𝓝 0)) ∧
      ∀ r t, Tendsto (fun h : ℝ => holderNorm α (D r (t + h) - D r t))
        (𝓝 0) (𝓝 0) := by
  obtain ⟨D, h0, hfin, hd⟩ := hf
  exact ⟨D, h0, hfin, hd, fun r t => holderNorm_increment_tendsto_zero
    (hfin (r + 1) t) (hd r t)⟩

end AnomDiss
