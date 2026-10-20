module

public import RequestProject.NSGalerkinTests

/-!
# Bounds for fixed spatial test modes

Only the spatial `L²` energy and `H¹` seminorm of the velocity are used.
Derivatives in the viscous term are transferred to the fixed smooth test
function. This is the spatial ingredient of low-frequency time compactness.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

private lemma ns_abs_mul_le_squares (a b : ℝ) : |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b,
    sq_nonneg a, sq_nonneg b]

private lemma ns_abs_le_sq_add_one (a : ℝ) : |a| ≤ a ^ 2 + 1 := by
  nlinarith [sq_nonneg (|a| - 1), sq_abs a]

private lemma ns_abs_triple_le {A : ℝ} (hA : 0 ≤ A) {c : ℝ} (hc : |c| ≤ A)
    (a b : ℝ) : |c * (a * b)| ≤ A * (a ^ 2 + b ^ 2) := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (ns_abs_mul_le_squares a b) hA)

/-- A fixed bounded test field controls the convective pairing by the velocity
energy and enstrophy density. -/
theorem ns_convective_test_pointwise {A : ℝ} (hA : 0 ≤ A)
    (φ v : Pt 2 → Pt 2) (x : Pt 2) (hφ : ∀ i, |φ x i| ≤ A) :
    |dot (φ x) (conv v v x)| ≤ A * (2 * (∑ i, v x i ^ 2) + gradSqV v x) := by
  have heq : dot (φ x) (conv v v x) =
      ∑ i : Fin 2, ∑ j : Fin 2, φ x i * (v x j * pd j v x i) := by
    simp only [dot, conv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [heq]
  calc
    |∑ i : Fin 2, ∑ j : Fin 2, φ x i * (v x j * pd j v x i)| ≤
        ∑ i : Fin 2, ∑ j : Fin 2, |φ x i * (v x j * pd j v x i)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, A * ((v x j) ^ 2 + (pd j v x i) ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        ns_abs_triple_le hA (hφ i) (v x j) (pd j v x i)
    _ = A * (2 * (∑ i, v x i ^ 2) + gradSqV v x) := by
      simp only [gradSqV, Fin.sum_univ_two]
      ring

/-- A fixed bounded test field controls the force pairing by its squared
`L²` density, without differentiating the force. -/
theorem ns_force_test_pointwise {A : ℝ} (hA : 0 ≤ A)
    (φ g : Pt 2 → Pt 2) (x : Pt 2) (hφ : ∀ i, |φ x i| ≤ A) :
    |dot (φ x) (g x)| ≤ A * ((∑ i, g x i ^ 2) + 2) := by
  unfold dot
  calc
    |∑ i : Fin 2, φ x i * g x i| ≤ ∑ i : Fin 2, |φ x i * g x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, A * (g x i ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hφ i) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (ns_abs_le_sq_add_one (g x i)) hA)
    _ = A * ((∑ i, g x i ^ 2) + 2) := by simp only [Fin.sum_univ_two]; ring

/-- The fixed test function's first derivatives control the cross-gradient
pairing by the velocity's gradient density. -/
theorem ns_gradient_test_pointwise {D : ℝ} (hD : 0 ≤ D)
    (φ v : Pt 2 → Pt 2) (x : Pt 2) (hφ : ∀ i j, |pd j φ x i| ≤ D) :
    |∑ i : Fin 2, ∑ j : Fin 2, pd j φ x i * pd j v x i| ≤
      D * (gradSqV v x + 4) := by
  calc
    |∑ i : Fin 2, ∑ j : Fin 2, pd j φ x i * pd j v x i| ≤
        ∑ i : Fin 2, ∑ j : Fin 2, |pd j φ x i * pd j v x i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, D * ((pd j v x i) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hφ i j) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (ns_abs_le_sq_add_one (pd j v x i)) hD)
    _ = D * (gradSqV v x + 4) := by simp only [gradSqV, Fin.sum_univ_two]; ring

/-- A scalar Laplacian tested against a different periodic function. -/
theorem ns_scalar_laplacian_test (φ v : Pt 2 → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hv : ContDiff ℝ 2 v)
    (hφp : IsPeriodic φ) (hvp : IsPeriodic v) :
    (∫ x in cell 2, φ x * lap v x) =
      -(∫ x in cell 2, ∑ j : Fin 2, pd j φ x * pd j v x) := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  unfold lap
  simp only [Finset.mul_sum]
  rw [integral_finset_sum (f := fun j x => φ x * pd j (pd j v) x) _
    (fun j _ => integrableOn_cell_of_continuous
      (hφ.continuous.mul (continuous_pd_of_C1 _ (contDiff_pd_of_C2 v hv j) j)))]
  simp only [fun j => integral_mul_pd φ (pd j v) hφ (contDiff_pd_of_C2 v hv j)
    hφp (isPeriodic_pd v hvp j) j]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum
    (f := fun j x => pd j φ x * pd j v x) _ (fun j _ =>
    integrableOn_cell_of_continuous
      ((continuous_pd_of_C1 φ hφ j).mul (continuous_pd_of_C1 v hv1 j)))]

/-- All Laplacian derivatives can be transferred to first derivatives of a
fixed test vector field on the torus. -/
theorem ns_vector_laplacian_test (φ v : Pt 2 → Pt 2)
    (hφ : ContDiff ℝ 1 φ) (hv : ContDiff ℝ 2 v)
    (hφp : IsPeriodic φ) (hvp : IsPeriodic v) :
    (∫ x in cell 2, dot (φ x) (lap v x)) =
      -(∫ x in cell 2, ∑ i : Fin 2, ∑ j : Fin 2, pd j φ x i * pd j v x i) := by
  have hφk : ∀ i : Fin 2, ContDiff ℝ 1 (cmp φ i) := contDiff_cmp hφ
  have hvk : ∀ i : Fin 2, ContDiff ℝ 2 (cmp v i) := contDiff_cmp hv
  have hφkp : ∀ i : Fin 2, IsPeriodic (cmp φ i) := fun i x n => by simp [cmp, hφp x n]
  have hvkp : ∀ i : Fin 2, IsPeriodic (cmp v i) := fun i x n => by simp [cmp, hvp x n]
  have heq : (fun x => dot (φ x) (lap v x)) =
      fun x => ∑ i : Fin 2, cmp φ i x * lap (cmp v i) x := by
    funext x
    simp only [dot, cmp, lap_component v hv]
  rw [heq, integral_finset_sum (f := fun i x => cmp φ i x * lap (cmp v i) x) _
    (fun i _ => integrableOn_cell_of_continuous
    ((hφk i).continuous.mul (continuous_lap_of_C2 _ (hvk i))))]
  simp only [fun i => ns_scalar_laplacian_test (cmp φ i) (cmp v i)
    (hφk i) (hvk i) (hφkp i) (hvkp i)]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum
    (f := fun i x => ∑ j : Fin 2, pd j (cmp φ i) x * pd j (cmp v i) x) _ (fun i _ =>
    integrableOn_cell_of_continuous (continuous_finset_sum _ (fun j _ =>
      (continuous_pd_of_C1 _ (hφk i) j).mul
        (continuous_pd_of_C1 _ ((hvk i).of_le (by norm_num)) j))))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  simp only [pd_component φ x (hφ.differentiable one_ne_zero x),
    pd_component v x (hv.differentiable (by norm_num) x)]

private lemma ns_integral_abs_bound (F H : Pt 2 → ℝ) (hF : Continuous F)
    (hH : Continuous H) (hb : ∀ x, |F x| ≤ H x) :
    |∫ x in cell 2, F x| ≤ ∫ x in cell 2, H x :=
  abs_integral_le_integral_abs.trans (setIntegral_mono_on
    (integrableOn_cell_of_continuous hF.abs) (integrableOn_cell_of_continuous hH)
    measurableSet_Icc (fun x _ => hb x))

private lemma ns_continuous_energy_density {v : Pt 2 → Pt 2} (hv : Continuous v) :
    Continuous (fun x => ∑ i, v x i ^ 2) :=
  continuous_finset_sum _ fun i _ => ((continuous_apply i).comp hv).pow 2

private lemma ns_continuous_gradient_density {v : Pt 2 → Pt 2} (hv : ContDiff ℝ 1 v) :
    Continuous (fun x => gradSqV v x) :=
  continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp (continuous_pd_of_C1 v hv j)).pow 2

private lemma ns_continuous_vector_conv {v : Pt 2 → Pt 2} (hv : ContDiff ℝ 1 v) :
    Continuous (conv v v) :=
  continuous_finset_sum _ fun j _ => ((continuous_apply j).comp hv.continuous).smul
    (continuous_pd_of_C1 v hv j)

/-- The fixed test's nonlinear pairing is controlled solely by velocity
energy and the gradient squared integral. -/
theorem ns_convective_test_integral {A : ℝ} (hA : 0 ≤ A)
    (φ v : Pt 2 → Pt 2) (hφ : Continuous φ) (hv : ContDiff ℝ 1 v)
    (hb : ∀ x i, |φ x i| ≤ A) :
    |∫ x in cell 2, dot (φ x) (conv v v x)| ≤
      A * (2 * l2sqV v + ∫ x in cell 2, gradSqV v x) := by
  have he := ns_continuous_energy_density hv.continuous
  have hd := ns_continuous_gradient_density hv
  have ht := ns_integral_abs_bound (fun x => dot (φ x) (conv v v x))
    (fun x => A * (2 * (∑ i, v x i ^ 2) + gradSqV v x))
    (continuous_finset_sum _ fun i _ => ((continuous_apply i).comp hφ).mul
      ((continuous_apply i).comp (ns_continuous_vector_conv hv)))
    (continuous_const.mul ((continuous_const.mul he).add hd))
    (fun x => ns_convective_test_pointwise hA φ v x (hb x))
  rw [integral_const_mul, integral_add
    ((integrableOn_cell_of_continuous he).const_mul 2)
    (integrableOn_cell_of_continuous hd), integral_const_mul] at ht
  exact ht

/-- Force work against a fixed test mode requires only the original force's
squared `L²` norm. -/
theorem ns_force_test_integral {A : ℝ} (hA : 0 ≤ A)
    (φ g : Pt 2 → Pt 2) (hφ : Continuous φ) (hg : Continuous g)
    (hb : ∀ x i, |φ x i| ≤ A) :
    |∫ x in cell 2, dot (φ x) (g x)| ≤ A * (l2sqV g + 2) := by
  have he := ns_continuous_energy_density hg
  have ht := ns_integral_abs_bound (fun x => dot (φ x) (g x))
    (fun x => A * ((∑ i, g x i ^ 2) + 2))
    (continuous_finset_sum _ fun i _ => ((continuous_apply i).comp hφ).mul
      ((continuous_apply i).comp hg))
    (continuous_const.mul (he.add continuous_const))
    (fun x => ns_force_test_pointwise hA φ g x (hb x))
  rw [integral_const_mul, integral_add (integrableOn_cell_of_continuous he)
    (integrableOn_cell_of_continuous continuous_const)] at ht
  have hc : (∫ _x in cell 2, (2 : ℝ)) = 2 := by
    simp [Measure.real, cell, Real.volume_Icc_pi]
  rw [hc] at ht
  exact ht

/-- The viscosity pairing with a fixed test requires only a gradient bound
for that test and the velocity's `H¹` seminorm. -/
theorem ns_laplacian_test_integral {D : ℝ} (hD : 0 ≤ D)
    (φ v : Pt 2 → Pt 2) (hφ : ContDiff ℝ 1 φ) (hv : ContDiff ℝ 2 v)
    (hφp : IsPeriodic φ) (hvp : IsPeriodic v)
    (hb : ∀ x i j, |pd j φ x i| ≤ D) :
    |∫ x in cell 2, dot (φ x) (lap v x)| ≤
      D * ((∫ x in cell 2, gradSqV v x) + 4) := by
  rw [ns_vector_laplacian_test φ v hφ hv hφp hvp, abs_neg]
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hd := ns_continuous_gradient_density hv1
  have ht := ns_integral_abs_bound
    (fun x => ∑ i : Fin 2, ∑ j : Fin 2, pd j φ x i * pd j v x i)
    (fun x => D * (gradSqV v x + 4))
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((continuous_apply i).comp (continuous_pd_of_C1 φ hφ j)).mul
        ((continuous_apply i).comp (continuous_pd_of_C1 v hv1 j)))
    (continuous_const.mul (hd.add continuous_const))
    (fun x => ns_gradient_test_pointwise hD φ v x (hb x))
  rw [integral_const_mul, integral_add (integrableOn_cell_of_continuous hd)
    (integrableOn_cell_of_continuous continuous_const)] at ht
  have hc : (∫ _x in cell 2, (4 : ℝ)) = 4 := by
    simp [Measure.real, cell, Real.volume_Icc_pi]
  rw [hc] at ht
  exact ht

end AnomDiss
