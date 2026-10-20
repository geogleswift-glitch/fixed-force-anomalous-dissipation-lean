module

public import RequestProject.FourierFiniteBlockBounds

/-!
# From uniform coefficient convergence to actual velocity L² compactness

The spatial tail hypothesis is a genuine `l2sqV` estimate. Uniform convergence
at finitely many Fourier coordinates gives one common index threshold, and
the finite-block estimate then proves uniform-in-time `L²` Cauchyness of the
actual spatial fields. No existence of a velocity limit is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss

/-- Finitely many uniformly convergent coefficient curves share a uniform
Cauchy threshold over the whole compact time interval. -/
theorem finite_fourier_coefficients_uniform_cauchy
    (v : ℕ → ℝ → Pt 2 → Pt 2)
    (a : (Fin 2 → ℤ) → Fin 2 → Icc (0 : ℝ) 1 → ℂ)
    (hconv : ∀ k i, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t : Icc (0 : ℝ) 1,
      ‖vectorFourierCoeff (v n t) k i - a k i t‖ < ε)
    (S : Finset (Fin 2 → ℤ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ m, N ≤ m → ∀ t ∈ Icc 0 1,
      ∀ k ∈ S, ∀ i, ‖vectorFourierCoeff (v n t) k i - vectorFourierCoeff (v m t) k i‖ ≤ δ := by
  have hb : ∀ᶠ n : ℕ in atTop, ∀ k ∈ S, ∀ i, ∀ t : Icc (0 : ℝ) 1,
      ‖vectorFourierCoeff (v n t) k i - a k i t‖ < δ / 2 := by
    apply S.eventually_all.mpr
    intro k hk
    apply Filter.eventually_all.mpr
    intro i
    exact hconv k i (δ / 2) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  refine ⟨N, fun n hn m hm t ht k hk i => ?_⟩
  have hnt := hN n hn k hk i ⟨t, ht⟩
  have hmt := hN m hm k hk i ⟨t, ht⟩
  have htri : ‖vectorFourierCoeff (v n t) k i - vectorFourierCoeff (v m t) k i‖ ≤
      ‖vectorFourierCoeff (v n t) k i - a k i ⟨t, ht⟩‖ +
        ‖a k i ⟨t, ht⟩ - vectorFourierCoeff (v m t) k i‖ := by
    calc
      ‖vectorFourierCoeff (v n t) k i - vectorFourierCoeff (v m t) k i‖ =
          ‖(vectorFourierCoeff (v n t) k i - a k i ⟨t, ht⟩) +
            (a k i ⟨t, ht⟩ - vectorFourierCoeff (v m t) k i)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev (a k i ⟨t, ht⟩) (vectorFourierCoeff (v m t) k i)] at htri
  linarith

/-- Uniformly small real spatial Fourier tails and uniform convergence of
every actual Fourier coefficient imply uniform-in-time `L²` Cauchyness. -/
theorem uniform_l2_cauchy_of_fourier_tails_and_coefficients
    (v : ℕ → ℝ → Pt 2 → Pt 2)
    (hv : ∀ n t, Continuous (v n t))
    (htail : ∀ ε > 0, ∃ S : Finset (Fin 2 → ℤ),
      ∀ n t, t ∈ Icc 0 1 → l2sqV (v n t - realFourierTruncation S (v n t)) < ε)
    (a : (Fin 2 → ℤ) → Fin 2 → Icc (0 : ℝ) 1 → ℂ)
    (hconv : ∀ k i, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t : Icc (0 : ℝ) 1,
      ‖vectorFourierCoeff (v n t) k i - a k i t‖ < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → ∀ m, N ≤ m → ∀ t ∈ Icc 0 1,
      l2sqV (v n t - v m t) < ε := by
  intro ε hε
  obtain ⟨S, hS⟩ := htail (ε / 12) (by linarith)
  let M : ℝ := S.card
  let δ : ℝ := sqrt ε / (4 * (M + 1))
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (sqrt_pos.2 hε) (by positivity)
  have hδid : 4 * (M + 1) * δ = sqrt ε := by
    dsimp [δ]
    field_simp
  have hsmall : 2 * (M * δ) ^ 2 ≤ ε / 8 := by
    have hsqrt : (sqrt ε) ^ 2 = ε := sq_sqrt hε.le
    have hle : M * δ ≤ sqrt ε / 4 := by nlinarith [hδ.le]
    have hsq := (sq_le_sq₀ (mul_nonneg hM hδ.le)
      (by positivity : 0 ≤ sqrt ε / 4)).2 hle
    nlinarith
  obtain ⟨N, hN⟩ := finite_fourier_coefficients_uniform_cauchy v a hconv S hδ
  refine ⟨N, fun n hn m hm t ht => ?_⟩
  have hdist := l2sqV_difference_le_fourier_tail_coefficients S (v n t) (v m t)
    (hv n t) (hv m t) hδ.le (hN n hn m hm t ht)
  have hleft := hS n t ht
  have hright := hS m t ht
  change 2 * ((S.card : ℝ) * δ) ^ 2 ≤ ε / 8 at hsmall
  nlinarith

end AnomDiss
