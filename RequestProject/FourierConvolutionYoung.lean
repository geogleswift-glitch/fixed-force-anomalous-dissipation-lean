module

public import Mathlib

/-!
# Discrete Young inequality for actual infinite Fourier convolutions

The ℓ² × ℓ¹ → ℓ² estimate holds on any additive commutative group.
Absolute convergence is proved before the infinite convolution is used.
Finite weighted Cauchy--Schwarz and a shear of the nonnegative double
series give the squared norm bound, with constant one.
-/

@[expose] public section

open Set Filter Topology Real

noncomputable section

namespace AnomDiss

set_option maxHeartbeats 800000

private def youngSubEquiv {G : Type*} [AddCommGroup G] (k : G) : G ≃ G where
  toFun l := k - l
  invFun l := k - l
  left_inv l := by dsimp; abel
  right_inv l := by dsimp; abel

private def youngShearEquiv {G : Type*} [AddCommGroup G] : (G × G) ≃ (G × G) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext <;> dsimp <;> abel
  right_inv p := by ext <;> dsimp <;> abel

/-- Nonnegative discrete Young inequality, including actual summability of
each infinite convolution and its squared coefficient family. -/
theorem discrete_young_l2_l1_nonneg {G : Type*} [AddCommGroup G]
    (A B : G → ℝ) (hA0 : ∀ l, 0 ≤ A l) (hB0 : ∀ l, 0 ≤ B l)
    (hA : Summable (fun l => A l ^ 2)) (hB : Summable B) :
    (∀ k, Summable (fun l => A l * B (k - l))) ∧
    Summable (fun k => (∑' l, A l * B (k - l)) ^ 2) ∧
    (∑' k, (∑' l, A l * B (k - l)) ^ 2) ≤
      (∑' l, B l) ^ 2 * ∑' l, A l ^ 2 := by
  classical
  let W : G × G → ℝ := fun p => A p.2 ^ 2 * B (p.1 - p.2)
  have hprod : Summable (fun p : G × G => A p.1 ^ 2 * B p.2) :=
    hA.mul_of_nonneg hB (fun l => sq_nonneg _) hB0
  have hW : Summable W := by
    exact youngShearEquiv.summable_iff.mpr hprod
  have hW0 : ∀ p, 0 ≤ W p := fun p => mul_nonneg (sq_nonneg _) (hB0 _)
  have hBshift (k : G) : Summable (fun l => B (k - l)) :=
    (youngSubEquiv k).summable_iff.mpr hB
  have hBsum (k : G) : (∑' l, B (k - l)) = ∑' l, B l :=
    (youngSubEquiv k).tsum_eq B
  have hBtotal : 0 ≤ ∑' l, B l := tsum_nonneg hB0
  have hpartial (k : G) (S : Finset G) :
      (∑ l ∈ S, A l * B (k - l)) ^ 2 ≤
        (∑' l, B l) * ∑' l, A l ^ 2 * B (k - l) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul S
      (r := fun l => A l * B (k - l))
      (f := fun l => A l ^ 2 * B (k - l)) (g := fun l => B (k - l))
      (fun l _ => mul_nonneg (sq_nonneg _) (hB0 _))
      (fun l _ => hB0 _) (fun l _ => by ring)
    have hleft : (∑ l ∈ S, A l ^ 2 * B (k - l)) ≤
        ∑' l, A l ^ 2 * B (k - l) :=
      (hW.prod_factor k).sum_le_tsum S (fun l _ => hW0 (k, l))
    have hright : (∑ l ∈ S, B (k - l)) ≤ ∑' l, B l := by
      rw [← hBsum k]
      exact (hBshift k).sum_le_tsum S (fun l _ => hB0 _)
    exact hcs.trans ((mul_le_mul hleft hright
      (Finset.sum_nonneg fun l _ => hB0 _)
      (tsum_nonneg fun l => hW0 (k, l))).trans_eq (mul_comm _ _))
  have hconv (k : G) : Summable (fun l => A l * B (k - l)) := by
    apply summable_of_sum_le (fun l => mul_nonneg (hA0 l) (hB0 _))
      (c := Real.sqrt ((∑' l, B l) * ∑' l, A l ^ 2 * B (k - l)))
    intro S
    exact Real.le_sqrt_of_sq_le (hpartial k S)
  have hpoint (k : G) :
      (∑' l, A l * B (k - l)) ^ 2 ≤
        (∑' l, B l) * ∑' l, A l ^ 2 * B (k - l) := by
    apply le_of_tendsto ((hconv k).hasSum.pow 2)
    exact Eventually.of_forall (hpartial k)
  have hsquare : Summable (fun k => (∑' l, A l * B (k - l)) ^ 2) :=
    (hW.prod.mul_left (∑' l, B l)).of_nonneg_of_le (fun k => sq_nonneg _) hpoint
  refine ⟨hconv, hsquare, ?_⟩
  have hdouble : (∑' k, ∑' l, A l ^ 2 * B (k - l)) =
      (∑' l, A l ^ 2) * ∑' l, B l := by
    calc
      _ = ∑' p : G × G, W p := hW.tsum_prod.symm
      _ = ∑' p : G × G, A p.1 ^ 2 * B p.2 :=
        (youngShearEquiv (G := G)).tsum_eq (fun p : G × G => A p.1 ^ 2 * B p.2)
      _ = _ := (hA.tsum_mul_tsum hB hprod).symm
  calc
    _ ≤ ∑' k, (∑' l, B l) * ∑' l, A l ^ 2 * B (k - l) :=
      Summable.tsum_le_tsum hpoint hsquare (hW.prod.mul_left _)
    _ = (∑' l, B l) * ∑' k, ∑' l, A l ^ 2 * B (k - l) := tsum_mul_left
    _ = _ := by rw [hdouble]; ring

/-- Discrete Young ℓ² × ℓ¹ → ℓ² for complex Fourier coefficient families
on an arbitrary additive commutative group. The convolution is absolutely
convergent at every frequency and the squared norm estimate has constant one. -/
theorem discrete_young_l2_l1_complex {G : Type*} [AddCommGroup G]
    (a b : G → ℂ) (ha : Summable (fun l => ‖a l‖ ^ 2))
    (hb : Summable (fun l => ‖b l‖)) :
    (∀ k, Summable (fun l => ‖a l * b (k - l)‖)) ∧
    Summable (fun k => ‖∑' l, a l * b (k - l)‖ ^ 2) ∧
    (∑' k, ‖∑' l, a l * b (k - l)‖ ^ 2) ≤
      (∑' l, ‖b l‖) ^ 2 * ∑' l, ‖a l‖ ^ 2 := by
  obtain ⟨hconv, hsquare, hbound⟩ := discrete_young_l2_l1_nonneg
    (fun l => ‖a l‖) (fun l => ‖b l‖) (fun l => norm_nonneg _) (fun l => norm_nonneg _) ha hb
  have habs (k : G) : Summable (fun l => ‖a l * b (k - l)‖) := by
    simpa only [norm_mul] using hconv k
  have hpoint (k : G) :
      ‖∑' l, a l * b (k - l)‖ ^ 2 ≤ (∑' l, ‖a l‖ * ‖b (k - l)‖) ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (tsum_nonneg fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    simpa only [norm_mul] using norm_tsum_le_tsum_norm (habs k)
  have hresult : Summable (fun k => ‖∑' l, a l * b (k - l)‖ ^ 2) :=
    hsquare.of_nonneg_of_le (fun k => sq_nonneg _) hpoint
  exact ⟨habs, hresult, (Summable.tsum_le_tsum hpoint hresult hsquare).trans hbound⟩

end AnomDiss
