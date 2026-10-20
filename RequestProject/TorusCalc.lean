module

public import RequestProject.Basic

/-!
# Calculus on the torus `𝕋²`

Helper results for Lemma 1.7: Fubini on the unit cell, vanishing of the mean of a partial
derivative of a periodic function, periodic integration by parts, and the one-variable facts
(first and second derivative at a maximum) used in the maximum principle.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- Every point of `ℝ²` is an integer translate of a point of the unit cell. -/
lemma exists_cell_rep {d : ℕ} (x : Pt d) : ∃ y ∈ cell d, ∃ n : Fin d → ℤ, x = y + intVec n := by
  refine ⟨fun i => Int.fract (x i), ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩,
    fun i => ⌊x i⌋, ?_⟩
  funext i; simp only [intVec, Pi.add_apply, Int.fract]; ring

lemma continuous_vec2 : Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Pt 2) :=
  continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop

/-- Fubini on the unit cell of `ℝ²`. -/
lemma integral_cell_two (G : Pt 2 → ℝ) (hG : ContinuousOn G (cell 2)) :
    ∫ x in cell 2, G x = ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, G ![a, b] := by
  let e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hmp : MeasurePreserving e volume volume := volume_preserving_finTwoArrow ℝ
  have hset : cell 2 = e ⁻¹' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    ext x
    simp only [cell, mem_preimage, mem_prod, mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply, e,
      MeasurableEquiv.finTwoArrow_apply, Fin.forall_fin_two]
    tauto
  have hsymm : ∀ p : ℝ × ℝ, e.symm p = ![p.1, p.2] := fun p => by
    funext i; fin_cases i <;> rfl
  have hc : ContinuousOn (fun p : ℝ × ℝ => G (e.symm p)) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    simp only [hsymm]
    refine hG.comp continuous_vec2.continuousOn ?_
    rintro p ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    simp only [cell, mem_Icc, Pi.le_def, Fin.forall_fin_two]
    simp [h1, h2, h3, h4]
  have key := hmp.setIntegral_preimage_emb e.measurableEmbedding (fun p => G (e.symm p))
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)
  simp only [MeasurableEquiv.symm_apply_apply] at key
  rw [hset, key]
  rw [Measure.volume_eq_prod,
    setIntegral_prod _ (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  simp only [hsymm]

/-- Fubini on the unit cell of `ℝ²`, other order. -/
lemma integral_cell_two' (G : Pt 2 → ℝ) (hG : ContinuousOn G (cell 2)) :
    ∫ x in cell 2, G x = ∫ b in (0:ℝ)..1, ∫ a in (0:ℝ)..1, G ![a, b] := by
  rw [integral_cell_two G hG]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  refine integral_integral_swap ?_
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hc : ContinuousOn (fun p : ℝ × ℝ => G ![p.1, p.2]) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    refine hG.comp continuous_vec2.continuousOn ?_
    rintro p ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    simp only [cell, mem_Icc, Pi.le_def, Fin.forall_fin_two]
    simp [h1, h2, h3, h4]
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

section line
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `i`-th standard basis vector. -/
def eb (i : Fin d) : Pt d := Pi.single i 1

lemma hasDerivAt_line (h : Pt d → E) (x : Pt d) (i : Fin d) (r : ℝ)
    (hd : DifferentiableAt ℝ h (x + r • eb i)) :
    HasDerivAt (fun r => h (x + r • eb i)) (pd i h (x + r • eb i)) r := by
  have hl : HasDerivAt (fun r : ℝ => x + r • eb i) (eb i) r := by
    simpa using ((hasDerivAt_id r).smul_const (eb i)).const_add x
  exact hd.hasFDerivAt.comp_hasDerivAt r hl

lemma continuous_pd_of_C1 (h : Pt d → E) (hh : ContDiff ℝ 1 h) (i : Fin d) : Continuous (pd i h) :=
  (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma integral_pd_line (h : Pt d → ℝ) (hh : ContDiff ℝ 1 h) (hp : IsPeriodic h) (i : Fin d)
    (x : Pt d) : ∫ r in (0:ℝ)..1, pd i h (x + r • eb i) = 0 := by
  have hc : Continuous fun r : ℝ => pd i h (x + r • eb i) :=
    (continuous_pd_of_C1 h hh i).comp (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_line h x i r (hh.differentiable one_ne_zero _))
    (hc.intervalIntegrable _ _)]
  have : x + eb i = x + intVec (Pi.single i 1) := by
    congr 1; funext j; simp [intVec, eb, Pi.single_apply]
  simp only [one_smul, zero_smul, add_zero]
  rw [this, hp, sub_self]

end line

/-- The mean of a partial derivative of a periodic `C¹` function vanishes. -/
lemma integral_pd_periodic (h : Pt 2 → ℝ) (hh : ContDiff ℝ 1 h) (hp : IsPeriodic h) (i : Fin 2) :
    ∫ x in cell 2, pd i h x = 0 := by
  have hc := (continuous_pd_of_C1 h hh i).continuousOn (s := cell 2)
  fin_cases i
  · rw [integral_cell_two' _ hc]
    have : ∀ b : ℝ, ∫ a in (0:ℝ)..1, pd 0 h ![a, b] = 0 := by
      intro b
      have e : ∀ a : ℝ, (![a, b] : Pt 2) = ![0, b] + a • eb 0 := by
        intro a; funext j; fin_cases j <;> simp [eb]
      rw [show (fun a : ℝ => pd 0 h ![a, b]) = fun a => pd 0 h (![0, b] + a • eb 0) from
        funext fun a => by rw [← e]]
      exact integral_pd_line h hh hp 0 _
    simp [this]
  · rw [integral_cell_two _ hc]
    have : ∀ a : ℝ, ∫ b in (0:ℝ)..1, pd 1 h ![a, b] = 0 := by
      intro a
      have e : ∀ b : ℝ, (![a, b] : Pt 2) = ![a, 0] + b • eb 1 := by
        intro b; funext j; fin_cases j <;> simp [eb]
      rw [show (fun b : ℝ => pd 1 h ![a, b]) = fun b => pd 1 h (![a, 0] + b • eb 1) from
        funext fun b => by rw [← e]]
      exact integral_pd_line h hh hp 1 _
    simp [this]

section ibp
variable {d : ℕ}

lemma pd_mul' (f g : Pt d → ℝ) (x : Pt d) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  unfold pd
  rw [fderiv_fun_mul hf hg]
  simp; ring

lemma isPeriodic_pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Pt d → E)
    (hp : IsPeriodic h) (i : Fin d) : IsPeriodic (pd i h) := by
  intro x n
  unfold pd
  have : h = fun y => h (y + intVec n) := funext fun y => (hp y n).symm
  conv_rhs => rw [this]
  rw [fderiv_comp_add_right]

lemma contDiff_pd_of_C2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Pt d → E)
    (hh : ContDiff ℝ 2 h) (i : Fin d) : ContDiff ℝ 1 (pd i h) :=
  (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma isPeriodic_mul (f g : Pt d → ℝ) (hf : IsPeriodic f) (hg : IsPeriodic g) :
    IsPeriodic (fun y => f y * g y) := fun x n => by simp [hf x n, hg x n]

lemma integral_mul_pd (f g : Pt 2 → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : IsPeriodic f) (hgp : IsPeriodic g) (i : Fin 2) :
    ∫ x in cell 2, f x * pd i g x = -∫ x in cell 2, pd i f x * g x := by
  have h0 := integral_pd_periodic _ (hf.mul hg) (isPeriodic_mul f g hfp hgp) i
  have e : ∀ x, pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x :=
    fun x => pd_mul' f g x (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x) i
  simp only [e] at h0
  have hc : ∀ (F : Pt 2 → ℝ), Continuous F → IntegrableOn F (cell 2) := fun F hF =>
    hF.continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_add (f := fun x => pd i f x * g x) (g := fun x => f x * pd i g x)
    (hc _ ((continuous_pd_of_C1 f hf i).mul hg.continuous))
    (hc _ (hf.continuous.mul (continuous_pd_of_C1 g hg i)))] at h0
  linarith

lemma integrableOn_cell_of_continuous {F : Pt 2 → ℝ} (hF : Continuous F) : IntegrableOn F (cell 2) :=
  hF.continuousOn.integrableOn_compact isCompact_Icc

lemma integral_mul_lap (θ : Pt 2 → ℝ) (hθ : ContDiff ℝ 2 θ) (hp : IsPeriodic θ) :
    ∫ x in cell 2, θ x * lap θ x = -∫ x in cell 2, gradSq θ x := by
  have h1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  unfold lap gradSq
  simp only [Finset.mul_sum]
  rw [integral_finset_sum (f := fun i x => θ x * pd i (pd i θ) x) _
      (fun i _ => integrableOn_cell_of_continuous
      (h1.continuous.mul (continuous_pd_of_C1 _ (contDiff_pd_of_C2 θ hθ i) i))),
    integral_finset_sum (f := fun i x => pd i θ x ^ 2) _ (fun i _ => integrableOn_cell_of_continuous
      ((continuous_pd_of_C1 _ h1 i).pow 2)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_pd θ (pd i θ) h1 (contDiff_pd_of_C2 θ hθ i) hp (isPeriodic_pd θ hp i)]
  simp [sq]

lemma pd_component (u : Pt d → Pt d) (x : Pt d) (hu : DifferentiableAt ℝ u x) (j k : Fin d) :
    pd j (fun y => u y k) x = pd j u x k := by
  unfold pd
  have : (fun y => u y k) = (ContinuousLinearMap.proj k : Pt d →L[ℝ] ℝ) ∘ u := rfl
  rw [this, fderiv_comp x (ContinuousLinearMap.proj k).differentiableAt hu]
  simp

lemma integral_mul_conv (u : Pt 2 → Pt 2) (hu : ContDiff ℝ 1 u) (hup : IsPeriodic u)
    (hdiv : ∀ x, divergence u x = 0) (θ : Pt 2 → ℝ) (hθ : ContDiff ℝ 1 θ) (hp : IsPeriodic θ) :
    ∫ x in cell 2, θ x * conv u θ x = 0 := by
  have huj : ∀ j : Fin 2, ContDiff ℝ 1 (fun y => u y j) := fun j =>
    (contDiff_apply ℝ ℝ j).comp hu
  have hujp : ∀ j : Fin 2, IsPeriodic (fun y => u y j) := fun j x n => by simp [hup x n]
  have hcu : ∀ j : Fin 2, Continuous (pd j (fun y => u y j)) := fun j => continuous_pd_of_C1 _ (huj j) j
  -- the identity for each direction
  have key : ∀ j : Fin 2, 2 * ∫ x in cell 2, θ x * (u x j * pd j θ x) =
      -∫ x in cell 2, pd j (fun y => u y j) x * θ x ^ 2 := by
    intro j
    have hI := integral_mul_pd (fun y => u y j * θ y) θ ((huj j).mul hθ) hθ
      (isPeriodic_mul _ _ (hujp j) hp) hp j
    have e : ∀ x, pd j (fun y => u y j * θ y) x * θ x =
        pd j (fun y => u y j) x * θ x ^ 2 + θ x * (u x j * pd j θ x) := fun x => by
      rw [pd_mul' _ _ x ((huj j).differentiable one_ne_zero x) (hθ.differentiable one_ne_zero x)]
      ring
    simp only [e] at hI
    rw [integral_add (f := fun x => pd j (fun y => u y j) x * θ x ^ 2)
      (g := fun x => θ x * (u x j * pd j θ x))
      (integrableOn_cell_of_continuous ((hcu j).mul (hθ.continuous.pow 2)))
      (integrableOn_cell_of_continuous (hθ.continuous.mul (((continuous_apply j).comp
        hu.continuous).mul (continuous_pd_of_C1 θ hθ j))))] at hI
    have e2 : ∀ x, u x j * θ x * pd j θ x = θ x * (u x j * pd j θ x) := fun x => by ring
    simp only [e2] at hI
    linarith
  have hsum : ∫ x in cell 2, θ x * conv u θ x =
      ∑ j : Fin 2, ∫ x in cell 2, θ x * (u x j * pd j θ x) := by
    unfold conv
    simp only [smul_eq_mul, Finset.mul_sum]
    exact integral_finset_sum _ (fun j _ => integrableOn_cell_of_continuous
      (hθ.continuous.mul (((continuous_apply j).comp hu.continuous).mul (continuous_pd_of_C1 θ hθ j))))
  have hdiv' : ∫ x in cell 2, ∑ j : Fin 2, pd j (fun y => u y j) x * θ x ^ 2 = 0 := by
    have : ∀ x, ∑ j : Fin 2, pd j (fun y => u y j) x * θ x ^ 2 = 0 := fun x => by
      rw [← Finset.sum_mul]
      have := hdiv x
      unfold divergence at this
      simp only [← pd_component u x (hu.differentiable one_ne_zero x)] at this
      rw [this, zero_mul]
    simp [this]
  rw [integral_finset_sum (f := fun j x => pd j (fun y => u y j) x * θ x ^ 2) _
    (fun j _ => integrableOn_cell_of_continuous
    ((hcu j).mul (hθ.continuous.pow 2)))] at hdiv'
  rw [hsum]
  have : 2 * ∑ j : Fin 2, ∫ x in cell 2, θ x * (u x j * pd j θ x) = 0 := by
    rw [Finset.mul_sum]; simp only [key]; rw [Finset.sum_neg_distrib, hdiv', neg_zero]
  linarith
end ibp

end AnomDiss
