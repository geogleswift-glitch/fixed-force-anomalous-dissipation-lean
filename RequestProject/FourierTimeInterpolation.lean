module

public import RequestProject.FourierTimeEnergy

/-!
# Absolute coefficient time moduli from two energy levels

A Lipschitz estimate at a weaker Sobolev level and a uniform stronger
bound imply a genuine Hölder modulus for the weighted absolute Fourier
series. This also controls spatial derivatives of the reconstructed
series when the absolute moment is at least one.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Real
noncomputable section
namespace AnomDiss

theorem sqrt_interpolated_square_factor {A B d γ θ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) :
    Real.sqrt ((A * d^2)^γ * B^θ) =
      Real.sqrt (A^γ * B^θ) * d^γ := by
  have he : (d^2)^γ = (d^γ)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hd, ← Real.rpow_mul hd]
    congr 1
    ring
  rw [Real.mul_rpow hA (sq_nonneg _), he]
  have hre : A^γ * (d^γ)^2 * B^θ = (A^γ * B^θ) * (d^γ)^2 := by ring
  rw [hre, Real.sqrt_mul (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.rpow_nonneg hd _)]

theorem fourier_covering_increment_l1_bound
    (a : (Fin 2 → ℤ) → ℂ) {p q m D B d γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hm : 0 ≤ m)
    (hgap : 1 < γ*p + (1-γ)*q - m)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hp : Summable (fun k => (1 + fourierEigenvalue k)^p * ‖a k‖^2))
    (hq : Summable (fun k => (1 + fourierEigenvalue k)^q * ‖a k‖^2))
    (hpbound : (∑' k, (1 + fourierEigenvalue k)^p * ‖a k‖^2) ≤ D*d^2)
    (hqbound : (∑' k, (1 + fourierEigenvalue k)^q * ‖a k‖^2) ≤ B) :
    Summable (fun k => (1+‖intVec k‖)^m * ‖a k‖) ∧
      (∑' k, (1+‖intVec k‖)^m * ‖a k‖) ≤
        (2^m * (Real.sqrt (D^γ * B^(1-γ)) *
          Real.sqrt (∑' k : Fin 2 → ℤ,
            (1+fourierEigenvalue k)^(-(γ*p+(1-γ)*q-m))))) * d^γ := by
  have he : (1-(1-γ))*p + (1-γ)*q = γ*p + (1-γ)*q := by ring
  have hi := fourier_energy_interpolation_bound a
    (θ := 1-γ) (by linarith) (by linarith) hp hq hpbound hqbound
  simp only [he, show 1-(1-γ) = γ by ring] at hi
  obtain ⟨hs, hb⟩ := fourier_covering_weighted_l1_of_sobolev hm hgap hi.1
  refine ⟨hs, hb.trans ?_⟩
  have hroot := Real.sqrt_le_sqrt hi.2
  rw [sqrt_interpolated_square_factor hD hB hd] at hroot
  have hK : 0 ≤ Real.sqrt (∑' k : Fin 2 → ℤ,
      (1+fourierEigenvalue k)^(-(γ*p+(1-γ)*q-m))) := Real.sqrt_nonneg _
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hroot hK)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)
  exact h.trans_eq (by ring)

end AnomDiss
