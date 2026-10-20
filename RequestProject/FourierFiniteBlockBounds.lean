module

public import RequestProject.FourierFrequencyBox
public import RequestProject.NSFiniteGalerkinCore

/-!
# Actual L² distances from finitely many Fourier coordinates

Finite coefficient convergence controls the spatial `L²` distance of the
reconstructed block. Two true spatial tails then control the full distance.
These statements provide the quantitative bridge from diagonal coefficient
compactness to compactness of the actual velocity fields.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

theorem realFourierTruncation_component_distance_le
    (S : Finset (Fin 2 → ℤ)) (v w : Pt 2 → Pt 2) {δ : ℝ}
    (hcoeff : ∀ k ∈ S, ∀ i, ‖vectorFourierCoeff v k i - vectorFourierCoeff w k i‖ ≤ δ)
    (x : Pt 2) (i : Fin 2) :
    |realFourierTruncation S v x i - realFourierTruncation S w x i| ≤ (S.card : ℝ) * δ := by
  have heq : realFourierTruncation S v x i - realFourierTruncation S w x i =
      (∑ k ∈ S, (vectorFourierCoeff v k i - vectorFourierCoeff w k i) * expChar (intVec k) x).re := by
    simp only [realFourierTruncation, vectorFourierCoeff_apply, ← Complex.sub_re,
      ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  calc
    |(∑ k ∈ S, (vectorFourierCoeff v k i - vectorFourierCoeff w k i) *
        expChar (intVec k) x).re| ≤
        ‖∑ k ∈ S, (vectorFourierCoeff v k i - vectorFourierCoeff w k i) *
          expChar (intVec k) x‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ k ∈ S, ‖(vectorFourierCoeff v k i - vectorFourierCoeff w k i) *
        expChar (intVec k) x‖ := norm_sum_le _ _
    _ = ∑ k ∈ S, ‖vectorFourierCoeff v k i - vectorFourierCoeff w k i‖ := by
      simp only [norm_mul, norm_expChar, mul_one]
    _ ≤ ∑ k ∈ S, δ := Finset.sum_le_sum fun k hk => hcoeff k hk i
    _ = (S.card : ℝ) * δ := by simp

theorem realFourierTruncation_l2_distance_le
    (S : Finset (Fin 2 → ℤ)) (v w : Pt 2 → Pt 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ k ∈ S, ∀ i, ‖vectorFourierCoeff v k i - vectorFourierCoeff w k i‖ ≤ δ) :
    l2sqV (realFourierTruncation S v - realFourierTruncation S w) ≤
      2 * ((S.card : ℝ) * δ) ^ 2 := by
  let C : ℝ := (S.card : ℝ) * δ
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) hδ
  have hc := (continuous_realFourierTruncation S v).sub (continuous_realFourierTruncation S w)
  have hi : IntegrableOn (fun x => ∑ i : Fin 2,
      (realFourierTruncation S v x i - realFourierTruncation S w x i) ^ 2) (cell 2) :=
    integrableOn_cell_of_continuous (continuous_finset_sum _ fun i _ =>
      (((continuous_apply i).comp hc).pow 2))
  have hb : ∀ x, ∑ i : Fin 2,
      (realFourierTruncation S v x i - realFourierTruncation S w x i) ^ 2 ≤ 2 * C ^ 2 := by
    intro x
    have hsq (i : Fin 2) :
        (realFourierTruncation S v x i - realFourierTruncation S w x i) ^ 2 ≤ C ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg _) hC).2
        (realFourierTruncation_component_distance_le S v w hcoeff x i)
      simpa only [sq_abs] using h
    simp only [Fin.sum_univ_two]
    linarith [hsq 0, hsq 1]
  calc
    l2sqV (realFourierTruncation S v - realFourierTruncation S w) ≤
        ∫ x in cell 2, 2 * C ^ 2 :=
      setIntegral_mono_on hi (integrableOn_cell_of_continuous continuous_const)
        measurableSet_Icc (fun x _ => hb x)
    _ = 2 * ((S.card : ℝ) * δ) ^ 2 := by simp [C, Measure.real, volume_cell]

lemma l2sqV_sub_comm (v w : Pt 2 → Pt 2) : l2sqV (v - w) = l2sqV (w - v) := by
  unfold l2sqV
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.sub_apply]
  ring

theorem l2sqV_add_three_le (a b c : Pt 2 → Pt 2)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    l2sqV (a + b + c) ≤ 3 * (l2sqV a + l2sqV b + l2sqV c) := by
  have hd (f : Pt 2 → Pt 2) (hf : Continuous f) :
      IntegrableOn (fun x => ∑ i : Fin 2, f x i ^ 2) (cell 2) :=
    integrableOn_cell_of_continuous (continuous_finset_sum _ fun i _ =>
      (((continuous_apply i).comp hf).pow 2))
  have hpoint (x : Pt 2) :
      (∑ i : Fin 2, (a x i + b x i + c x i) ^ 2) ≤
        3 * ((∑ i : Fin 2, a x i ^ 2) + (∑ i : Fin 2, b x i ^ 2) +
          (∑ i : Fin 2, c x i ^ 2)) := by
    have hsq (i : Fin 2) : (a x i + b x i + c x i) ^ 2 ≤
        3 * (a x i ^ 2 + b x i ^ 2 + c x i ^ 2) := by
      nlinarith [sq_nonneg (a x i - b x i), sq_nonneg (a x i - c x i),
        sq_nonneg (b x i - c x i)]
    simp only [Fin.sum_univ_two]
    nlinarith [hsq 0, hsq 1]
  calc
    l2sqV (a + b + c) ≤ ∫ x in cell 2,
        3 * ((∑ i : Fin 2, a x i ^ 2) + (∑ i : Fin 2, b x i ^ 2) +
          (∑ i : Fin 2, c x i ^ 2)) :=
      setIntegral_mono_on (hd (a + b + c) ((ha.add hb).add hc))
        (((hd a ha).add (hd b hb)).add (hd c hc) |>.const_mul 3)
        measurableSet_Icc (fun x _ => hpoint x)
    _ = 3 * (l2sqV a + l2sqV b + l2sqV c) := by
      rw [integral_const_mul,
        integral_add (f := fun x => (∑ i : Fin 2, a x i ^ 2) + (∑ i : Fin 2, b x i ^ 2))
          (g := fun x => ∑ i : Fin 2, c x i ^ 2) ((hd a ha).add (hd b hb)) (hd c hc),
        integral_add (f := fun x => ∑ i : Fin 2, a x i ^ 2)
          (g := fun x => ∑ i : Fin 2, b x i ^ 2) (hd a ha) (hd b hb)]
      rfl

theorem l2sqV_difference_le_fourier_tails
    (S : Finset (Fin 2 → ℤ)) (v w : Pt 2 → Pt 2) (hv : Continuous v) (hw : Continuous w) :
    l2sqV (v - w) ≤ 3 * (l2sqV (v - realFourierTruncation S v) +
      l2sqV (realFourierTruncation S v - realFourierTruncation S w) +
      l2sqV (w - realFourierTruncation S w)) := by
  have hdecomp : v - w = (v - realFourierTruncation S v) +
      (realFourierTruncation S v - realFourierTruncation S w) +
      (realFourierTruncation S w - w) := by
    ext x i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have h := l2sqV_add_three_le (v - realFourierTruncation S v)
    (realFourierTruncation S v - realFourierTruncation S w) (realFourierTruncation S w - w)
    (hv.sub (continuous_realFourierTruncation S v))
    ((continuous_realFourierTruncation S v).sub (continuous_realFourierTruncation S w))
    ((continuous_realFourierTruncation S w).sub hw)
  rw [← hdecomp, l2sqV_sub_comm (realFourierTruncation S w) w] at h
  exact h

theorem l2sqV_difference_le_fourier_tail_coefficients
    (S : Finset (Fin 2 → ℤ)) (v w : Pt 2 → Pt 2) (hv : Continuous v) (hw : Continuous w)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ k ∈ S, ∀ i, ‖vectorFourierCoeff v k i - vectorFourierCoeff w k i‖ ≤ δ) :
    l2sqV (v - w) ≤ 3 * (l2sqV (v - realFourierTruncation S v) +
      2 * ((S.card : ℝ) * δ) ^ 2 + l2sqV (w - realFourierTruncation S w)) := by
  exact (l2sqV_difference_le_fourier_tails S v w hv hw).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add le_rfl (realFourierTruncation_l2_distance_le S v w hδ hcoeff)) le_rfl)
      (by norm_num : (0 : ℝ) ≤ 3))

end AnomDiss
