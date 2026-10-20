module

public import RequestProject.H2Dens

/-!
# The `H²` density under near-identity changes of variables

If `‖Dψ - I‖ ≤ a` and `‖D²ψ‖ ≤ a` with `0 ≤ a`, then
`h2Dens (f ∘ ψ) ≤ (1 + C a (1 + a)³) h2Dens f ∘ ψ` pointwise, with an absolute constant `C`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

noncomputable section

namespace AnomDiss

lemma clm_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Pt 2 →L[ℝ] E)
    (w : Pt 2) : L w = ∑ k, w k • L (Pi.single k 1) := by
  have hw : w = ∑ k, w k • (Pi.single k 1 : Pt 2) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul]

lemma norm_single_le (k : Fin 2) : ‖(Pi.single k 1 : Pt 2)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = k
  · subst h; simp
  · simp [h]

/-- First derivative applied to a vector, in terms of partial derivatives. -/
lemma norm_fderiv_apply_le_pd (f : Pt 2 → ℂ) (p v : Pt 2) :
    ‖fderiv ℝ f p v‖ ≤ ‖v‖ * ∑ k, ‖pd k f p‖ := by
  rw [fderiv_apply_eq_sum_pd, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v k)
    (norm_nonneg _)

/-- Second derivative applied to two vectors, in terms of second partial derivatives. -/
lemma norm_fderiv2_apply_le_pd {f : Pt 2 → ℂ} (hf : ContDiff ℝ 2 f) (p u w : Pt 2) :
    ‖fderiv ℝ (fderiv ℝ f) p u w‖ ≤ ‖u‖ * ‖w‖ * ∑ l, ∑ k, ‖pd l (pd k f) p‖ := by
  rw [clm_apply_eq_sum (fderiv ℝ (fderiv ℝ f) p) u]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [clm_apply_eq_sum (fderiv ℝ (fderiv ℝ f) p (Pi.single l 1)) w, Finset.smul_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [fderiv_fderiv_apply_eq_pd hf, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hu : |u l| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u l
  have hw : |w k| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w k
  have := norm_nonneg (pd l (pd k f) p)
  calc |u l| * (|w k| * ‖pd l (pd k f) p‖) = |u l| * |w k| * ‖pd l (pd k f) p‖ := by ring
    _ ≤ ‖u‖ * ‖w‖ * ‖pd l (pd k f) p‖ := by gcongr

/-- Chain rule for second derivatives. -/
lemma fderiv2_comp_apply {f : Pt 2 → ℂ} {ψ : Pt 2 → Pt 2} (hf : ContDiff ℝ 2 f)
    (hψ : ContDiff ℝ 2 ψ) (y u w : Pt 2) :
    fderiv ℝ (fderiv ℝ (f ∘ ψ)) y u w =
      fderiv ℝ (fderiv ℝ f) (ψ y) (fderiv ℝ ψ y u) (fderiv ℝ ψ y w) +
        fderiv ℝ f (ψ y) (fderiv ℝ (fderiv ℝ ψ) y u w) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hψ1 : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hf2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  have hψ2 : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  have hfd : fderiv ℝ (f ∘ ψ) = fun z => (fderiv ℝ f (ψ z)).comp (fderiv ℝ ψ z) := by
    funext z; exact fderiv_comp z (hf1 _) (hψ1 _)
  have hA : HasFDerivAt (fun z => fderiv ℝ f (ψ z))
      ((fderiv ℝ (fderiv ℝ f) (ψ y)).comp (fderiv ℝ ψ y)) y :=
    (hf2 (ψ y)).hasFDerivAt.comp y (hψ1 y).hasFDerivAt
  have h := hA.clm_comp (hψ2 y).hasFDerivAt
  rw [hfd, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  abel

lemma pd_pd_eq_fderiv2_C {g : Pt 2 → ℂ} (hg : ContDiff ℝ 2 g) (i j : Fin 2) (y : Pt 2) :
    pd i (pd j g) y = fderiv ℝ (fderiv ℝ g) y (Pi.single i 1) (Pi.single j 1) :=
  (fderiv_fderiv_apply_eq_pd hg j i y).symm

/-- `‖x + e‖² ≤ ‖x‖² + c a (‖x‖² + W²) + (c a W)²` when `‖e‖ ≤ c a W`. -/
lemma sq_norm_add_le_aux {x e : ℂ} {c a W : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (he : ‖e‖ ≤ c * a * W) :
    ‖x + e‖ ^ 2 ≤ ‖x‖ ^ 2 + c * a * (‖x‖ ^ 2 + W ^ 2) + (c * a * W) ^ 2 := by
  have h1 := norm_add_le x e
  have h2 := norm_nonneg e
  have h3 := norm_nonneg x
  have hca : 0 ≤ c * a := mul_nonneg hc ha
  have h4 : ‖x + e‖ ^ 2 ≤ (‖x‖ + ‖e‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h5 : 2 * ‖x‖ * ‖e‖ ≤ c * a * (‖x‖ ^ 2 + W ^ 2) := by
    have : 2 * ‖x‖ * ‖e‖ ≤ 2 * ‖x‖ * (c * a * W) := by gcongr
    nlinarith [sq_nonneg (‖x‖ - W)]
  have h6 : ‖e‖ ^ 2 ≤ (c * a * W) ^ 2 := pow_le_pow_left₀ h2 he 2
  nlinarith

lemma sq_sum6_le (x₁ x₂ x₃ x₄ x₅ x₆ : ℝ) :
    (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) ^ 2 ≤ 6 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2 + x₆ ^ 2) := by
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₁ - x₄), sq_nonneg (x₁ - x₅),
    sq_nonneg (x₁ - x₆), sq_nonneg (x₂ - x₃), sq_nonneg (x₂ - x₄), sq_nonneg (x₂ - x₅),
    sq_nonneg (x₂ - x₆), sq_nonneg (x₃ - x₄), sq_nonneg (x₃ - x₅), sq_nonneg (x₃ - x₆),
    sq_nonneg (x₄ - x₅), sq_nonneg (x₄ - x₆), sq_nonneg (x₅ - x₆)]

lemma h2_final_arith {a D W f0 P2 Q2 F2 S2 : ℝ} (ha : 0 ≤ a) (hD : D = f0 + F2 + S2)
    (hf0 : 0 ≤ f0) (hF2 : 0 ≤ F2) (hS2 : 0 ≤ S2) (hW2 : W ^ 2 ≤ 6 * D)
    (hP : P2 ≤ F2 + a * (D + 2 * W ^ 2) + 2 * (a * W) ^ 2)
    (hQ : Q2 ≤ S2 + (2 + a) * a * (D + 4 * W ^ 2) + 4 * ((2 + a) * a * W) ^ 2) :
    f0 + P2 + Q2 ≤ (1 + 400 * a * (1 + a) ^ 3) * D := by
  have hD0 : 0 ≤ D := by linarith
  have k1 : a * (D + 2 * W ^ 2) ≤ 13 * a * D := by nlinarith
  have k2 : 2 * (a * W) ^ 2 ≤ 12 * a ^ 2 * D := by
    have : (a * W) ^ 2 = a ^ 2 * W ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg a]
  have hb : 0 ≤ (2 + a) * a := by positivity
  have k3 : (2 + a) * a * (D + 4 * W ^ 2) ≤ 25 * ((2 + a) * a) * D := by nlinarith
  have k4 : 4 * ((2 + a) * a * W) ^ 2 ≤ 24 * ((2 + a) * a) ^ 2 * D := by
    have : ((2 + a) * a * W) ^ 2 = ((2 + a) * a) ^ 2 * W ^ 2 := by ring
    rw [this]
    have : 0 ≤ ((2 + a) * a) ^ 2 := by positivity
    nlinarith
  have h1 : 1 ≤ (1 + a) ^ 3 := one_le_pow₀ (by linarith)
  have hc : (1 + a) ^ 3 = (1 + a) * (1 + a) ^ 2 := by ring
  have h2 : a ≤ a * (1 + a) ^ 3 := by nlinarith
  have h3 : a ^ 2 ≤ a * (1 + a) ^ 3 := by
    have : a ^ 2 ≤ a * (1 + a) := by nlinarith
    have : a * (1 + a) ≤ a * (1 + a) ^ 3 := by
      have : (1 + a) ≤ (1 + a) ^ 3 := by nlinarith [sq_nonneg (1 + a)]
      exact mul_le_mul_of_nonneg_left this ha
    linarith
  have h4 : (2 + a) * a ≤ 2 * (a * (1 + a) ^ 3) := by nlinarith
  have h5 : ((2 + a) * a) ^ 2 ≤ 4 * (a * (1 + a) ^ 3) := by
    have e : ((2 + a) * a) ^ 2 = (2 + a) ^ 2 * a ^ 2 := by ring
    have s1 : (2 + a) ^ 2 ≤ 4 * (1 + a) ^ 2 := by nlinarith
    have s2 : a ^ 2 * (1 + a) ^ 2 ≤ a * (1 + a) ^ 3 := by
      have : a ^ 2 ≤ a * (1 + a) := by nlinarith
      have : 0 ≤ (1 + a) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right this (sq_nonneg (1 + a))
      nlinarith
    rw [e]
    have : (2 + a) ^ 2 * a ^ 2 ≤ 4 * (1 + a) ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_right s1 (sq_nonneg a)
    nlinarith
  have k5 : 13 * a + 12 * a ^ 2 + 25 * ((2 + a) * a) + 24 * ((2 + a) * a) ^ 2 ≤
      400 * a * (1 + a) ^ 3 := by nlinarith
  have := mul_le_mul_of_nonneg_right k5 hD0
  nlinarith

theorem h2Dens_comp_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Pt 2 → ℂ) (ψ : Pt 2 → Pt 2) (a : ℝ),
    ContDiff ℝ 2 f → ContDiff ℝ 2 ψ → 0 ≤ a →
    (∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ (Pt 2)‖ ≤ a) →
    (∀ x, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ a) →
    ∀ y, h2Dens (f ∘ ψ) y ≤ (1 + C * a * (1 + a) ^ 3) * h2Dens f (ψ y) := by
  refine ⟨400, by norm_num, fun f ψ a hf hψ ha hD1 hD2 y => ?_⟩
  set p := ψ y with hp
  set A := fderiv ℝ ψ y with hA
  have hψ1 : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg : ContDiff ℝ 2 (f ∘ ψ) := hf.comp hψ
  -- basic vector bounds
  have hAe : ∀ k : Fin 2, ‖A (Pi.single k 1) - Pi.single k 1‖ ≤ a := fun k => by
    have : A (Pi.single k 1) - Pi.single k 1 =
        (A - ContinuousLinearMap.id ℝ (Pt 2)) (Pi.single k 1) := by simp
    rw [this]
    refine ((A - ContinuousLinearMap.id ℝ (Pt 2)).le_opNorm _).trans ?_
    calc _ ≤ a * 1 := mul_le_mul (hD1 y) (norm_single_le k) (norm_nonneg _) ha
      _ = a := mul_one a
  have hAn : ∀ k : Fin 2, ‖A (Pi.single k 1)‖ ≤ 1 + a := fun k => by
    have := norm_add_le (A (Pi.single k 1) - Pi.single k 1) (Pi.single k 1)
    rw [sub_add_cancel] at this
    linarith [hAe k, norm_single_le k]
  have hHn : ∀ i j : Fin 2,
      ‖fderiv ℝ (fderiv ℝ ψ) y (Pi.single i 1) (Pi.single j 1)‖ ≤ a := fun i j => by
    refine ((fderiv ℝ (fderiv ℝ ψ) y (Pi.single i 1)).le_opNorm _).trans ?_
    refine (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ ψ) y).le_opNorm _)
      (norm_nonneg _)).trans ?_
    have := norm_single_le i; have := norm_single_le j
    have := hD2 y
    have h0 := norm_nonneg (fderiv ℝ (fderiv ℝ ψ) y)
    calc _ ≤ a * 1 * 1 := by gcongr
      _ = a := by ring
  -- the quantities at `p`
  set SF := ∑ k, ‖pd k f p‖ with hSF
  set SS := ∑ l, ∑ k, ‖pd l (pd k f) p‖ with hSS
  set W := SF + SS with hW
  have hSF0 : 0 ≤ SF := by positivity
  have hSS0 : 0 ≤ SS := by positivity
  have hW0 : 0 ≤ W := by positivity
  -- first derivatives
  have hP : ∀ j : Fin 2, ‖pd j (f ∘ ψ) y‖ ^ 2 ≤
      ‖pd j f p‖ ^ 2 + 1 * a * (‖pd j f p‖ ^ 2 + W ^ 2) + (1 * a * W) ^ 2 := by
    intro j
    have e : pd j (f ∘ ψ) y = pd j f p + fderiv ℝ f p (A (Pi.single j 1) - Pi.single j 1) := by
      unfold pd
      rw [fderiv_comp y (hf1 _) (hψ1 _), ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [e]
    refine sq_norm_add_le_aux zero_le_one ha ?_
    refine (norm_fderiv_apply_le_pd f p _).trans ?_
    calc _ ≤ a * SF := mul_le_mul (hAe j) le_rfl hSF0 ha
      _ ≤ 1 * a * W := by nlinarith
  -- second derivatives
  have hQ : ∀ i j : Fin 2, ‖pd i (pd j (f ∘ ψ)) y‖ ^ 2 ≤
      ‖pd i (pd j f) p‖ ^ 2 + (2 + a) * a * (‖pd i (pd j f) p‖ ^ 2 + W ^ 2) +
        ((2 + a) * a * W) ^ 2 := by
    intro i j
    set ei : Pt 2 := Pi.single i 1
    set ej : Pt 2 := Pi.single j 1
    have e : pd i (pd j (f ∘ ψ)) y = pd i (pd j f) p +
        (fderiv ℝ (fderiv ℝ f) p (A ei - ei) (A ej) + fderiv ℝ (fderiv ℝ f) p ei (A ej - ej) +
          fderiv ℝ f p (fderiv ℝ (fderiv ℝ ψ) y ei ej)) := by
      rw [pd_pd_eq_fderiv2_C hg, fderiv2_comp_apply hf hψ, pd_pd_eq_fderiv2_C hf]
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    rw [e]
    refine sq_norm_add_le_aux (by linarith) ha ?_
    have b1 := norm_fderiv2_apply_le_pd hf p (A ei - ei) (A ej)
    have b2 := norm_fderiv2_apply_le_pd hf p ei (A ej - ej)
    have b3 := norm_fderiv_apply_le_pd f p (fderiv ℝ (fderiv ℝ ψ) y ei ej)
    have n1 := hAe i; have n2 := hAn j; have n3 := hAe j; have n4 := norm_single_le i
    have n5 := hHn i j
    have c1 : ‖A ei - ei‖ * ‖A ej‖ * SS ≤ a * (1 + a) * SS := by gcongr
    have c2 : ‖ei‖ * ‖A ej - ej‖ * SS ≤ 1 * a * SS := by gcongr
    have c3 : ‖fderiv ℝ (fderiv ℝ ψ) y ei ej‖ * SF ≤ a * SF := by gcongr
    have d : 0 ≤ (1 + a) * a * SF := by positivity
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have e1 := b1.trans c1
    have e2 := b2.trans c2
    have e3 := b3.trans c3
    have : a * (1 + a) * SS + 1 * a * SS + a * SF ≤ (2 + a) * a * W := by
      rw [hW]; nlinarith
    linarith
  -- assemble
  set D := h2Dens f p with hD
  have hDdef : D = ‖f p‖ ^ 2 + ∑ k, ‖pd k f p‖ ^ 2 + ∑ l, ∑ k, ‖pd l (pd k f) p‖ ^ 2 := rfl
  have hF2 : 0 ≤ ∑ k, ‖pd k f p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ l, ∑ k, ‖pd l (pd k f) p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hf0 : 0 ≤ ‖f p‖ ^ 2 := sq_nonneg _
  have hW2 : W ^ 2 ≤ 6 * D := by
    have h6 := sq_sum6_le ‖pd 0 f p‖ ‖pd 1 f p‖ ‖pd 0 (pd 0 f) p‖ ‖pd 0 (pd 1 f) p‖
      ‖pd 1 (pd 0 f) p‖ ‖pd 1 (pd 1 f) p‖
    have eW : W = ‖pd 0 f p‖ + ‖pd 1 f p‖ + ‖pd 0 (pd 0 f) p‖ + ‖pd 0 (pd 1 f) p‖ +
        ‖pd 1 (pd 0 f) p‖ + ‖pd 1 (pd 1 f) p‖ := by
      simp only [hW, hSF, hSS, Fin.sum_univ_two]; ring
    have eD : D = ‖f p‖ ^ 2 + (‖pd 0 f p‖ ^ 2 + ‖pd 1 f p‖ ^ 2) + (‖pd 0 (pd 0 f) p‖ ^ 2 +
        ‖pd 0 (pd 1 f) p‖ ^ 2 + (‖pd 1 (pd 0 f) p‖ ^ 2 + ‖pd 1 (pd 1 f) p‖ ^ 2)) := by
      rw [hDdef]; simp only [Fin.sum_univ_two]
    rw [eW, eD]
    linarith
  have hPsum : ∑ j, ‖pd j (f ∘ ψ) y‖ ^ 2 ≤
      ∑ k, ‖pd k f p‖ ^ 2 + a * (D + 2 * W ^ 2) + 2 * (a * W) ^ 2 := by
    have hFD : ∑ k, ‖pd k f p‖ ^ 2 ≤ D := by linarith
    have m := mul_le_mul_of_nonneg_left hFD ha
    have := hP 0; have := hP 1
    simp only [Fin.sum_univ_two] at m ⊢
    linarith
  have hQsum : ∑ i, ∑ j, ‖pd i (pd j (f ∘ ψ)) y‖ ^ 2 ≤
      ∑ l, ∑ k, ‖pd l (pd k f) p‖ ^ 2 + (2 + a) * a * (D + 4 * W ^ 2) +
        4 * ((2 + a) * a * W) ^ 2 := by
    have hSD : ∑ l, ∑ k, ‖pd l (pd k f) p‖ ^ 2 ≤ D := by linarith
    have m := mul_le_mul_of_nonneg_left hSD (show 0 ≤ (2 + a) * a by positivity)
    have := hQ 0 0; have := hQ 0 1; have := hQ 1 0; have := hQ 1 1
    simp only [Fin.sum_univ_two] at m ⊢
    linarith
  have h0 : ‖(f ∘ ψ) y‖ ^ 2 = ‖f p‖ ^ 2 := rfl
  show ‖(f ∘ ψ) y‖ ^ 2 + ∑ j, ‖pd j (f ∘ ψ) y‖ ^ 2 + ∑ i, ∑ j, ‖pd i (pd j (f ∘ ψ)) y‖ ^ 2 ≤ _
  rw [h0]
  exact h2_final_arith ha hDdef hf0 hF2 hS2 hW2 hPsum hQsum

end AnomDiss
