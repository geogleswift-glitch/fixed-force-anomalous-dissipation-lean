module

public import RequestProject.TorusFourier

/-!
# The genuine Leray multiplier on each two-dimensional Fourier mode

These are unconditional ingredients for a Fourier Galerkin construction.  The
coefficient space carries its Euclidean Hilbert norm.  The multiplier is the
orthogonal projection onto the kernel of the actual Fourier divergence symbol,
so its contraction and pressure-annihilation properties do not assume a PDE
solution or either of the external existence interfaces.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace AnomDiss

abbrev FourierVelocity := EuclideanSpace ℂ (Fin 2)

/-- The real integer wavevector viewed in the complex coefficient Hilbert space. -/
def fourierWave (k : Fin 2 → ℤ) : FourierVelocity :=
  WithLp.toLp 2 (fun i => (k i : ℂ))

@[simp] lemma fourierWave_apply (k : Fin 2 → ℤ) (i : Fin 2) :
    fourierWave k i = (k i : ℂ) := rfl

/-- The Fourier symbol of divergence, with the common factor `2πi` omitted. -/
def fourierDivSymbol (k : Fin 2 → ℤ) (a : FourierVelocity) : ℂ :=
  ∑ i, (k i : ℂ) * a i

lemma fourierDivSymbol_eq_inner (k : Fin 2 → ℤ) (a : FourierVelocity) :
    fourierDivSymbol k a = inner ℂ (fourierWave k) a := by
  simp [fourierDivSymbol, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Solenoidal coefficients at wavevector `k`; at `k = 0` this is the whole space. -/
def solenoidalMode (k : Fin 2 → ℤ) : Submodule ℂ FourierVelocity :=
  (ℂ ∙ fourierWave k)ᗮ

lemma mem_solenoidalMode_iff (k : Fin 2 → ℤ) (a : FourierVelocity) :
    a ∈ solenoidalMode k ↔ fourierDivSymbol k a = 0 := by
  rw [fourierDivSymbol_eq_inner]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

/-- The Leray Fourier multiplier, defined by the genuine orthogonal projection. -/
def fourierLeray (k : Fin 2 → ℤ) : FourierVelocity →L[ℂ] FourierVelocity :=
  (solenoidalMode k).starProjection

theorem fourierLeray_div_free (k : Fin 2 → ℤ) (a : FourierVelocity) :
    fourierDivSymbol k (fourierLeray k a) = 0 := by
  exact (mem_solenoidalMode_iff k _).mp ((solenoidalMode k).starProjection_apply_mem a)

theorem fourierLeray_fixes_solenoidal (k : Fin 2 → ℤ) (a : FourierVelocity)
    (ha : fourierDivSymbol k a = 0) : fourierLeray k a = a := by
  exact Submodule.starProjection_eq_self_iff.mpr ((mem_solenoidalMode_iff k a).mpr ha)

theorem fourierLeray_idempotent (k : Fin 2 → ℤ) (a : FourierVelocity) :
    fourierLeray k (fourierLeray k a) = fourierLeray k a :=
  fourierLeray_fixes_solenoidal k _ (fourierLeray_div_free k a)

theorem norm_fourierLeray_le (k : Fin 2 → ℤ) : ‖fourierLeray k‖ ≤ 1 :=
  (solenoidalMode k).starProjection_norm_le

theorem norm_fourierLeray_apply_le (k : Fin 2 → ℤ) (a : FourierVelocity) :
    ‖fourierLeray k a‖ ≤ ‖a‖ :=
  (solenoidalMode k).norm_starProjection_apply_le a

theorem fourierLeray_self_adjoint (k : Fin 2 → ℤ) (a b : FourierVelocity) :
    inner ℂ (fourierLeray k a) b = inner ℂ a (fourierLeray k b) :=
  (solenoidalMode k).inner_starProjection_left_eq_right a b

theorem fourierLeray_zero_mode (a : FourierVelocity) : fourierLeray 0 a = a := by
  apply fourierLeray_fixes_solenoidal
  simp [fourierDivSymbol]

/-- Explicit multiplier formula, including the zero mode through total division. -/
theorem fourierLeray_formula (k : Fin 2 → ℤ) (a : FourierVelocity) :
    fourierLeray k a = a -
      (fourierDivSymbol k a / ((‖fourierWave k‖ ^ 2 : ℝ) : ℂ)) • fourierWave k := by
  unfold fourierLeray solenoidalMode
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
  rw [fourierDivSymbol_eq_inner]
  rfl

/-- Every Fourier pressure gradient is killed by the velocity projection. -/
theorem fourierLeray_annihilates_gradient (k : Fin 2 → ℤ) (z : ℂ) :
    fourierLeray k (z • fourierWave k) = 0 := by
  unfold fourierLeray
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.zero_mem _
  · intro a ha
    have hz : inner ℂ (fourierWave k) a = 0 := by
      rw [← fourierDivSymbol_eq_inner]
      exact (mem_solenoidalMode_iff k a).mp ha
    simp [inner_smul_left, hz]

lemma solenoidalMode_neg (k : Fin 2 → ℤ) : solenoidalMode (-k) = solenoidalMode k := by
  ext a
  simp only [mem_solenoidalMode_iff, fourierDivSymbol, Pi.neg_apply, Int.cast_neg,
    neg_mul, Finset.sum_neg_distrib, neg_eq_zero]

/-- The multiplier is even in frequency, as required for real Fourier fields. -/
theorem fourierLeray_neg (k : Fin 2 → ℤ) : fourierLeray (-k) = fourierLeray k := by
  simp [fourierLeray, solenoidalMode_neg]

/-- The squared norm of the wavevector has precisely the usual Fourier value. -/
theorem norm_fourierWave_sq (k : Fin 2 → ℤ) :
    ‖fourierWave k‖ ^ 2 = ∑ i, (k i : ℝ) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Complex.norm_intCast, sq_abs]

/-- Coefficientwise complex conjugation used by the reality condition. -/
def fourierConj (a : FourierVelocity) : FourierVelocity :=
  WithLp.toLp 2 (fun i => (starRingEnd ℂ) (a i))

@[simp] lemma fourierConj_apply (a : FourierVelocity) (i : Fin 2) :
    fourierConj a i = (starRingEnd ℂ) (a i) := rfl

lemma fourierDivSymbol_conj (k : Fin 2 → ℤ) (a : FourierVelocity) :
    fourierDivSymbol k (fourierConj a) = (starRingEnd ℂ) (fourierDivSymbol k a) := by
  simp [fourierDivSymbol, map_mul]

/-- Coordinate form of the usual `I - k⊗k/|k|²` multiplier. -/
theorem fourierLeray_apply_formula (k : Fin 2 → ℤ) (a : FourierVelocity) (i : Fin 2) :
    fourierLeray k a i = a i -
      (fourierDivSymbol k a / ((‖fourierWave k‖ ^ 2 : ℝ) : ℂ)) * (k i : ℂ) := by
  have h := congrArg (fun b : FourierVelocity => b i) (fourierLeray_formula k a)
  simpa using h

/-- The Leray multiplier preserves the reality symmetry of Fourier coefficients. -/
theorem fourierLeray_conj (k : Fin 2 → ℤ) (a : FourierVelocity) :
    fourierLeray k (fourierConj a) = fourierConj (fourierLeray k a) := by
  ext i
  rw [fourierConj_apply, fourierLeray_apply_formula, fourierLeray_apply_formula,
    fourierDivSymbol_conj, fourierConj_apply]
  simp

end AnomDiss
