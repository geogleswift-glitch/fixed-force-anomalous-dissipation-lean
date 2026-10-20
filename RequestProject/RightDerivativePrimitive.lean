module

public import Mathlib

/-! A continuous right derivative on the positive half-line determines a
classical primitive, including the one-sided derivatives of closed intervals. -/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace AnomDiss

theorem hasDerivWithinAt_Icc_of_continuous_right_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} (hf : ContinuousOn f (Ici 0)) (hf' : ContinuousOn f' (Ici 0))
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Ici t) t)
    {T t : ℝ} (ht : t ∈ Icc 0 T) : HasDerivWithinAt f (f' t) (Icc 0 T) t := by
  let g : ℝ → E := fun s => f' (max s 0)
  have hgc : Continuous g := hf'.comp_continuous
    (continuous_id.max continuous_const) (fun s => le_max_right s 0)
  let P : ℝ → E := fun s => f 0 + ∫ r in (0 : ℝ)..s, g r
  have hPd (s : ℝ) : HasDerivAt P (g s) s := by
    simpa only [P, Pi.add_apply, zero_add] using
      (hasDerivAt_const s (f 0)).fun_add (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun s => (hPd s).continuousAt
  have hPw (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt P (f' s) (Ici s) s := by
    simpa only [g, max_eq_left hs] using (hPd s).hasDerivWithinAt
  have he (s : ℝ) (hs : 0 ≤ s) : f s = P s := by
    exact eq_of_has_deriv_right_eq
      (fun y hy => hd y hy.1) (fun y hy => hPw y hy.1)
      (hf.mono Icc_subset_Ici_self) hPc.continuousOn (by simp [P]) s ⟨hs, le_rfl⟩
  have hdt : HasDerivWithinAt P (f' t) (Icc 0 T) t := by
    simpa only [g, max_eq_left ht.1] using (hPd t).hasDerivWithinAt
  apply hdt.congr_of_eventuallyEq ?_ (he t ht.1)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact he s hs.1

/-- The local closed-interval version also supplies the derivative at the terminal endpoint. -/
theorem hasDerivWithinAt_Icc_of_continuous_right_derivative_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f f' : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hf' : ContinuousOn f' (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) : HasDerivWithinAt f (f' t) (Icc 0 T) t := by
  let g : ℝ → E := fun s => f' (projIcc 0 T hT s)
  have hgc : Continuous g := hf'.comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc : Continuous (projIcc 0 T hT)))
    (fun s => (projIcc 0 T hT s).property)
  let P : ℝ → E := fun s => f 0 + ∫ r in (0 : ℝ)..s, g r
  have hPd (s : ℝ) : HasDerivAt P (g s) s := by
    simpa only [P, Pi.add_apply, zero_add] using
      (hasDerivAt_const s (f 0)).fun_add (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun s => (hPd s).continuousAt
  have hPw (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivWithinAt P (f' s) (Ici s) s := by
    simpa only [g, projIcc_of_mem hT hs] using (hPd s).hasDerivWithinAt
  have he (s : ℝ) (hs : s ∈ Icc 0 T) : f s = P s := by
    exact eq_of_has_deriv_right_eq
      (fun y hy => hd y ⟨hy.1, hy.2.trans_le hs.2⟩)
      (fun y hy => hPw y ⟨hy.1, hy.2.le.trans hs.2⟩)
      (hf.mono (Icc_subset_Icc le_rfl hs.2)) hPc.continuousOn
      (by simp [P]) s ⟨hs.1, le_rfl⟩
  have hdt : HasDerivWithinAt P (f' t) (Icc 0 T) t := by
    simpa only [g, projIcc_of_mem hT ht] using (hPd t).hasDerivWithinAt
  apply hdt.congr_of_eventuallyEq ?_ (he t ht)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact he s hs

end AnomDiss
