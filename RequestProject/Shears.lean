module

public import RequestProject.External
public import RequestProject.TorusFourier

/-!
# Section 2.1: an elementary stretching estimate

The shears `H`, `V`, the commutator `F = V⁻¹ ∘ H⁻¹ ∘ V ∘ H`, its rotated and translated copies
`G_{ι,z}`, the random matrix law `Q`, and the negative moment estimate (Lemma 2.5).

Maps of the torus isotopic to the identity are represented by their lifts `Φ : ℝ² → ℝ²`
satisfying `Φ (x + n) = Φ x + n` for `n ∈ ℤ²`.  The uniform distribution on `𝕋²` is Lebesgue
measure on the unit cell, and the uniform distribution on `{0,1}` is the uniform distribution on
`Bool`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix

noncomputable section

namespace AnomDiss

/-- The horizontal shear `H(x,y) = (x + (2π)⁻¹ sin(2πy), y)`. -/
def shearH (p : Pt 2) : Pt 2 := ![p 0 + (2 * π)⁻¹ * Real.sin (2 * π * p 1), p 1]

/-- The vertical shear `V(x,y) = (x, y + (2π)⁻¹ sin(2πx))`. -/
def shearV (p : Pt 2) : Pt 2 := ![p 0, p 1 + (2 * π)⁻¹ * Real.sin (2 * π * p 0)]

/-- `H⁻¹`. -/
def shearHinv (p : Pt 2) : Pt 2 := ![p 0 - (2 * π)⁻¹ * Real.sin (2 * π * p 1), p 1]

/-- `V⁻¹`. -/
def shearVinv (p : Pt 2) : Pt 2 := ![p 0, p 1 - (2 * π)⁻¹ * Real.sin (2 * π * p 0)]

/-- `F = V⁻¹ ∘ H⁻¹ ∘ V ∘ H`. -/
def mapF : Pt 2 → Pt 2 := shearVinv ∘ shearHinv ∘ shearV ∘ shearH

/-- `F⁻¹ = H⁻¹ ∘ V⁻¹ ∘ H ∘ V`. -/
def mapFinv : Pt 2 → Pt 2 := shearHinv ∘ shearVinv ∘ shearH ∘ shearV

/-- The quarter turn `𝒥(x,y) = (-y,x)`. -/
def rotJ (p : Pt 2) : Pt 2 := ![-p 1, p 0]

/-- `𝒥⁻¹(x,y) = (y,-x)`. -/
def rotJinv (p : Pt 2) : Pt 2 := ![p 1, -p 0]

/-- `𝒥^ι Φ 𝒥^{-ι}` for `ι ∈ {0,1}` (`false = 0`, `true = 1`). -/
def conjJ (ι : Bool) (Φ : Pt 2 → Pt 2) : Pt 2 → Pt 2 :=
  if ι then rotJ ∘ Φ ∘ rotJinv else Φ

/-- `G_{ι,z} = τ_z ∘ 𝒥^ι F 𝒥^{-ι} ∘ τ_{-z}`. -/
def mapG (ι : Bool) (z : Pt 2) (x : Pt 2) : Pt 2 := z + conjJ ι mapF (x - z)

/-- `G_{ι,z}⁻¹ = τ_z ∘ 𝒥^ι F⁻¹ 𝒥^{-ι} ∘ τ_{-z}`. -/
def mapGinv (ι : Bool) (z : Pt 2) (x : Pt 2) : Pt 2 := z + conjJ ι mapFinv (x - z)

/-- The Jacobian matrix `DΦ(x)`. -/
def jac (Φ : Pt 2 → Pt 2) (x : Pt 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => fderiv ℝ Φ x (Pi.single j 1) i

/-- A map `ℝ² → ℝ²` is a lift of a torus map isotopic to the identity
(`Φ (x + n) = Φ x + n` for every `n ∈ ℤ²`, i.e. `Φ - id` is periodic). -/
def IsLift (Φ : Pt 2 → Pt 2) : Prop := ∀ x (n : Fin 2 → ℤ), Φ (x + intVec n) = Φ x + intVec n

/-- `C₀ = DF(0,0)`. -/
def matC0 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 3]

/-- `C₁ = DF(1/2,0)`. -/
def matC1 : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]


/-- The continuous linear map attached to a `2 × 2` matrix. -/
noncomputable def matCLM (A : Matrix (Fin 2) (Fin 2) ℝ) : Pt 2 →L[ℝ] Pt 2 :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

lemma matCLM_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Pt 2) : matCLM A v = A *ᵥ v := rfl

lemma matCLM_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) : (matCLM A).comp (matCLM B) = matCLM (A * B) := by
  apply ContinuousLinearMap.ext
  intro v
  change A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v
  exact Matrix.mulVec_mulVec v A B

lemma jac_eq_of_hasFDerivAt {Φ : Pt 2 → Pt 2} {x : Pt 2} {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : HasFDerivAt Φ (matCLM A) x) : jac Φ x = A := by
  ext i j
  simp [jac, h.fderiv, matCLM_apply, Matrix.mulVec_single]

lemma hasFDerivAt_shearX (f : ℝ → ℝ) (f' : ℝ) (p : Pt 2) (hf : HasDerivAt f f' (p 1)) :
    HasFDerivAt (fun p : Pt 2 => ![p 0 + f (p 1), p 1]) (matCLM !![1, f'; 0, 1]) p := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · change HasFDerivAt (fun q : Pt 2 => q 0 + f (q 1))
      ((ContinuousLinearMap.proj (0 : Fin 2)).comp (matCLM !![1, f'; 0, 1])) p
    have h := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p).fun_add
      (hf.comp_hasFDerivAt p (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p))
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp [matCLM_apply, dotProduct, Fin.sum_univ_two]
  · change HasFDerivAt (fun q : Pt 2 => q 1)
      ((ContinuousLinearMap.proj (1 : Fin 2)).comp (matCLM !![1, f'; 0, 1])) p
    convert hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [matCLM_apply, dotProduct, Fin.sum_univ_two]

lemma hasFDerivAt_shearY (g : ℝ → ℝ) (g' : ℝ) (p : Pt 2) (hg : HasDerivAt g g' (p 0)) :
    HasFDerivAt (fun p : Pt 2 => ![p 0, p 1 + g (p 0)]) (matCLM !![1, 0; g', 1]) p := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · change HasFDerivAt (fun q : Pt 2 => q 0)
      ((ContinuousLinearMap.proj (0 : Fin 2)).comp (matCLM !![1, 0; g', 1])) p
    convert hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [matCLM_apply, dotProduct, Fin.sum_univ_two]
  · change HasFDerivAt (fun q : Pt 2 => q 1 + g (q 0))
      ((ContinuousLinearMap.proj (1 : Fin 2)).comp (matCLM !![1, 0; g', 1])) p
    have h := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p).fun_add
      (hg.comp_hasFDerivAt p (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p))
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp [matCLM_apply, dotProduct, Fin.sum_univ_two]
      ring


lemma hasDerivAt_sinShear (y : ℝ) :
    HasDerivAt (fun y => (2 * π)⁻¹ * Real.sin (2 * π * y)) (Real.cos (2 * π * y)) y := by
  have h := ((Real.hasDerivAt_sin (2 * π * y)).comp y
    ((hasDerivAt_id y).const_mul (2 * π))).const_mul (2 * π)⁻¹
  convert h using 1
  · rfl
  · field_simp [Real.pi_ne_zero]

lemma hasDerivAt_negSinShear (y : ℝ) :
    HasDerivAt (fun y => -((2 * π)⁻¹ * Real.sin (2 * π * y))) (-Real.cos (2 * π * y)) y :=
  (hasDerivAt_sinShear y).neg

lemma hasFDerivAt_shearH (p : Pt 2) :
    HasFDerivAt shearH (matCLM !![1, Real.cos (2 * π * p 1); 0, 1]) p :=
  hasFDerivAt_shearX _ _ p (hasDerivAt_sinShear (p 1))

lemma hasFDerivAt_shearV (p : Pt 2) :
    HasFDerivAt shearV (matCLM !![1, 0; Real.cos (2 * π * p 0), 1]) p :=
  hasFDerivAt_shearY _ _ p (hasDerivAt_sinShear (p 0))

lemma hasFDerivAt_shearHinv (p : Pt 2) :
    HasFDerivAt shearHinv (matCLM !![1, -Real.cos (2 * π * p 1); 0, 1]) p := by
  have e : shearHinv = fun p : Pt 2 => ![p 0 + -((2 * π)⁻¹ * Real.sin (2 * π * p 1)), p 1] := by
    funext q; simp [shearHinv, sub_eq_add_neg]
  rw [e]; exact hasFDerivAt_shearX _ _ p (hasDerivAt_negSinShear (p 1))

lemma hasFDerivAt_shearVinv (p : Pt 2) :
    HasFDerivAt shearVinv (matCLM !![1, 0; -Real.cos (2 * π * p 0), 1]) p := by
  have e : shearVinv = fun p : Pt 2 => ![p 0, p 1 + -((2 * π)⁻¹ * Real.sin (2 * π * p 0))] := by
    funext q; simp [shearVinv, sub_eq_add_neg]
  rw [e]; exact hasFDerivAt_shearY _ _ p (hasDerivAt_negSinShear (p 0))

lemma hasFDerivAt_mapF (x : Pt 2) :
    HasFDerivAt mapF
      (matCLM (!![1, 0; -Real.cos (2 * π * shearHinv (shearV (shearH x)) 0), 1] *
        (!![1, -Real.cos (2 * π * shearV (shearH x) 1); 0, 1] *
        (!![1, 0; Real.cos (2 * π * shearH x 0), 1] *
        !![1, Real.cos (2 * π * x 1); 0, 1])))) x := by
  have h := (hasFDerivAt_shearVinv _).comp x ((hasFDerivAt_shearHinv _).comp x
    ((hasFDerivAt_shearV _).comp x (hasFDerivAt_shearH x)))
  simp only [matCLM_mul] at h
  exact h

lemma contDiff_vec2 {f g : Pt 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p => ![f p, g p]) := by
  rw [contDiff_pi]
  intro i; fin_cases i
  · simpa using hf
  · simpa using hg

lemma contDiff_shearH : ContDiff ℝ ∞ shearH :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_shearV : ContDiff ℝ ∞ shearV :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_shearHinv : ContDiff ℝ ∞ shearHinv :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_shearVinv : ContDiff ℝ ∞ shearVinv :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_rotJ : ContDiff ℝ ∞ rotJ := contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_rotJinv : ContDiff ℝ ∞ rotJinv := contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_mapF : ContDiff ℝ ∞ mapF :=
  contDiff_shearVinv.comp (contDiff_shearHinv.comp (contDiff_shearV.comp contDiff_shearH))

lemma contDiff_mapFinv : ContDiff ℝ ∞ mapFinv :=
  contDiff_shearHinv.comp (contDiff_shearVinv.comp (contDiff_shearH.comp contDiff_shearV))

lemma contDiff_conjJ (ι : Bool) {Φ : Pt 2 → Pt 2} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (conjJ ι Φ) := by
  cases ι
  · exact hΦ
  · exact contDiff_rotJ.comp (hΦ.comp contDiff_rotJinv)

lemma contDiff_mapG (ι : Bool) (z : Pt 2) : ContDiff ℝ ∞ (mapG ι z) :=
  contDiff_const.add ((contDiff_conjJ ι contDiff_mapF).comp (contDiff_id.sub contDiff_const))

lemma contDiff_mapGinv (ι : Bool) (z : Pt 2) : ContDiff ℝ ∞ (mapGinv ι z) :=
  contDiff_const.add ((contDiff_conjJ ι contDiff_mapFinv).comp (contDiff_id.sub contDiff_const))

/-! inverses -/

lemma vec2_ext {p q : Pt 2} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  funext i; fin_cases i <;> assumption

lemma shearHinv_shearH (p : Pt 2) : shearHinv (shearH p) = p :=
  vec2_ext (by simp [shearH, shearHinv]) (by simp [shearH, shearHinv])

lemma shearH_shearHinv (p : Pt 2) : shearH (shearHinv p) = p :=
  vec2_ext (by simp [shearH, shearHinv]) (by simp [shearH, shearHinv])

lemma shearVinv_shearV (p : Pt 2) : shearVinv (shearV p) = p :=
  vec2_ext (by simp [shearV, shearVinv]) (by simp [shearV, shearVinv])

lemma shearV_shearVinv (p : Pt 2) : shearV (shearVinv p) = p :=
  vec2_ext (by simp [shearV, shearVinv]) (by simp [shearV, shearVinv])

lemma rotJinv_rotJ (p : Pt 2) : rotJinv (rotJ p) = p :=
  vec2_ext (by simp [rotJ, rotJinv]) (by simp [rotJ, rotJinv])

lemma rotJ_rotJinv (p : Pt 2) : rotJ (rotJinv p) = p :=
  vec2_ext (by simp [rotJ, rotJinv]) (by simp [rotJ, rotJinv])

lemma mapFinv_mapF (p : Pt 2) : mapFinv (mapF p) = p := by
  simp [mapF, mapFinv, shearVinv_shearV, shearV_shearVinv, shearHinv_shearH, shearH_shearHinv]

lemma mapF_mapFinv (p : Pt 2) : mapF (mapFinv p) = p := by
  simp [mapF, mapFinv, shearVinv_shearV, shearV_shearVinv, shearHinv_shearH, shearH_shearHinv]

lemma conjJ_inv (ι : Bool) {Φ Ψ : Pt 2 → Pt 2} (h : ∀ p, Ψ (Φ p) = p) (p : Pt 2) :
    conjJ ι Ψ (conjJ ι Φ p) = p := by
  cases ι
  · exact h p
  · simp [conjJ, rotJinv_rotJ, h, rotJ_rotJinv]

lemma mapGinv_mapG (ι : Bool) (z p : Pt 2) : mapGinv ι z (mapG ι z p) = p := by
  simp [mapG, mapGinv, conjJ_inv ι mapFinv_mapF]

lemma mapG_mapGinv (ι : Bool) (z p : Pt 2) : mapG ι z (mapGinv ι z p) = p := by
  simp [mapG, mapGinv, conjJ_inv ι mapF_mapFinv]


/-! lifts -/

lemma sin_two_pi_add_int (y : ℝ) (n : ℤ) : Real.sin (2 * π * (y + n)) = Real.sin (2 * π * y) := by
  rw [show 2 * π * (y + n) = 2 * π * y + n * (2 * π) by ring, Real.sin_add_int_mul_two_pi]

lemma isLift_shearH : IsLift shearH := fun x n =>
  vec2_ext (by simp [shearH, intVec, sin_two_pi_add_int]; ring) (by simp [shearH, intVec])

lemma isLift_shearV : IsLift shearV := fun x n =>
  vec2_ext (by simp [shearV, intVec]) (by simp [shearV, intVec, sin_two_pi_add_int]; ring)

lemma isLift_shearHinv : IsLift shearHinv := fun x n =>
  vec2_ext (by simp [shearHinv, intVec, sin_two_pi_add_int]; ring) (by simp [shearHinv, intVec])

lemma isLift_shearVinv : IsLift shearVinv := fun x n =>
  vec2_ext (by simp [shearVinv, intVec]) (by simp [shearVinv, intVec, sin_two_pi_add_int]; ring)

lemma IsLift.comp {Φ Ψ : Pt 2 → Pt 2} (hΦ : IsLift Φ) (hΨ : IsLift Ψ) : IsLift (Φ ∘ Ψ) :=
  fun x n => by simp only [Function.comp, hΨ x n, hΦ _ n]

lemma isLift_mapF : IsLift mapF :=
  isLift_shearVinv.comp (isLift_shearHinv.comp (isLift_shearV.comp isLift_shearH))

lemma isLift_mapFinv : IsLift mapFinv :=
  isLift_shearHinv.comp (isLift_shearVinv.comp (isLift_shearH.comp isLift_shearV))

lemma rotJinv_add_intVec (x : Pt 2) (n : Fin 2 → ℤ) :
    rotJinv (x + intVec n) = rotJinv x + intVec ![n 1, -n 0] :=
  vec2_ext (by simp [rotJinv, intVec]) (by simp [rotJinv, intVec]; ring)

lemma rotJ_add_intVec (x : Pt 2) (n : Fin 2 → ℤ) :
    rotJ (x + intVec n) = rotJ x + intVec ![-n 1, n 0] :=
  vec2_ext (by simp [rotJ, intVec]; ring) (by simp [rotJ, intVec])

lemma isLift_conjJ (ι : Bool) {Φ : Pt 2 → Pt 2} (hΦ : IsLift Φ) : IsLift (conjJ ι Φ) := by
  cases ι
  · exact hΦ
  · intro x n
    simp only [conjJ, if_true, Function.comp, rotJinv_add_intVec, hΦ _, rotJ_add_intVec]
    congr 2
    funext i; fin_cases i <;> simp

lemma isLift_mapG (ι : Bool) (z : Pt 2) : IsLift (mapG ι z) := fun x n => by
  simp only [mapG, show x + intVec n - z = (x - z) + intVec n by abel, isLift_conjJ ι isLift_mapF _ n]
  abel


/-! Jacobian determinants -/

lemma rotJ_eq_matCLM : rotJ = ⇑(matCLM !![0, -1; 1, 0]) := by
  funext p; exact vec2_ext (by simp [rotJ, matCLM_apply, Matrix.vecHead, Matrix.vecTail])
    (by simp [rotJ, matCLM_apply, Matrix.vecHead, Matrix.vecTail])

lemma rotJinv_eq_matCLM : rotJinv = ⇑(matCLM !![0, 1; -1, 0]) := by
  funext p; exact vec2_ext (by simp [rotJinv, matCLM_apply, Matrix.vecHead, Matrix.vecTail])
    (by simp [rotJinv, matCLM_apply, Matrix.vecHead, Matrix.vecTail])

lemma hasFDerivAt_conjJ (ι : Bool) {Φ : Pt 2 → Pt 2} {A : Pt 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (matCLM (A y)) y) (y : Pt 2) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℝ, B.det = (A (if ι then rotJinv y else y)).det ∧
      HasFDerivAt (conjJ ι Φ) (matCLM B) y := by
  cases ι
  · exact ⟨A y, rfl, hΦ y⟩
  · refine ⟨!![0, -1; 1, 0] * (A (rotJinv y) * !![0, 1; -1, 0]), ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul]; simp [Matrix.det_fin_two_of]
    · have h1 : HasFDerivAt rotJinv (matCLM !![0, 1; -1, 0]) y := by
        rw [rotJinv_eq_matCLM]; exact (matCLM _).hasFDerivAt
      have h2 : HasFDerivAt rotJ (matCLM !![0, -1; 1, 0]) (Φ (rotJinv y)) := by
        rw [rotJ_eq_matCLM]; exact (matCLM _).hasFDerivAt
      have h := h2.comp y ((hΦ (rotJinv y)).comp y h1)
      simp only [matCLM_mul] at h
      exact h

lemma hasFDerivAt_translate {Φ : Pt 2 → Pt 2} {B : Matrix (Fin 2) (Fin 2) ℝ} {z x : Pt 2}
    (h : HasFDerivAt Φ (matCLM B) (x - z)) :
    HasFDerivAt (fun x => z + Φ (x - z)) (matCLM B) x := by
  have h' := (h.comp x ((hasFDerivAt_id x).sub_const z)).const_add z
  simpa using h'

lemma det_jac_mapF (x : Pt 2) : (jac mapF x).det = 1 := by
  rw [jac_eq_of_hasFDerivAt (hasFDerivAt_mapF x), Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fin_two_of]

lemma det_jac_mapG (ι : Bool) (z x : Pt 2) : (jac (mapG ι z) x).det = 1 := by
  obtain ⟨B, hB, hd⟩ := hasFDerivAt_conjJ ι (fun y => hasFDerivAt_mapF y) (x - z)
  have h := hasFDerivAt_translate (z := z) (x := x) hd
  have e : mapG ι z = fun x => z + conjJ ι mapF (x - z) := rfl
  rw [e, jac_eq_of_hasFDerivAt h, hB]
  have := det_jac_mapF (if ι then rotJinv (x - z) else x - z)
  rwa [jac_eq_of_hasFDerivAt (hasFDerivAt_mapF _)] at this

/-- **Lemma 2.2**, smoothness, invertibility, lift property and area preservation of the basic
maps. -/
theorem basic_shear_properties :
    (ContDiff ℝ ∞ shearH ∧ ContDiff ℝ ∞ shearV ∧ ContDiff ℝ ∞ mapF ∧
      ∀ ι z, ContDiff ℝ ∞ (mapG ι z)) ∧
    (Function.LeftInverse shearHinv shearH ∧ Function.RightInverse shearHinv shearH ∧
      Function.LeftInverse shearVinv shearV ∧ Function.RightInverse shearVinv shearV ∧
      Function.LeftInverse mapFinv mapF ∧ Function.RightInverse mapFinv mapF ∧
      ∀ ι z, Function.LeftInverse (mapGinv ι z) (mapG ι z) ∧
        Function.RightInverse (mapGinv ι z) (mapG ι z)) ∧
    (IsLift shearH ∧ IsLift shearV ∧ IsLift mapF ∧ ∀ ι z, IsLift (mapG ι z)) ∧
    (∀ x, (jac shearH x).det = 1 ∧ (jac shearV x).det = 1 ∧ (jac mapF x).det = 1 ∧
      ∀ ι z, (jac (mapG ι z) x).det = 1) := by
  refine ⟨⟨contDiff_shearH, contDiff_shearV, contDiff_mapF, contDiff_mapG⟩,
    ⟨shearHinv_shearH, shearH_shearHinv, shearVinv_shearV, shearV_shearVinv, mapFinv_mapF,
      mapF_mapFinv, fun ι z => ⟨mapGinv_mapG ι z, mapG_mapGinv ι z⟩⟩,
    ⟨isLift_shearH, isLift_shearV, isLift_mapF, isLift_mapG⟩,
    fun x => ⟨?_, ?_, det_jac_mapF x, fun ι z => det_jac_mapG ι z x⟩⟩
  · rw [jac_eq_of_hasFDerivAt (hasFDerivAt_shearH x)]; simp [Matrix.det_fin_two_of]
  · rw [jac_eq_of_hasFDerivAt (hasFDerivAt_shearV x)]; simp [Matrix.det_fin_two_of]

/-- **Lemma 2.2**, fixed points and derivative matrices:
`F(0,0) = (0,0)`, `F(1/2,0) = (1/2,0)`, `DF(0,0) = C₀`, `DF(1/2,0) = C₁`. -/
theorem mapF_fixed_points :
    mapF ![0, 0] = ![0, 0] ∧ mapF ![1 / 2, 0] = ![1 / 2, 0] ∧
    jac mapF ![0, 0] = matC0 ∧ jac mapF ![1 / 2, 0] = matC1 := by
  have hπ1 : 2 * π * (1 / 2) = π := by ring
  have hπ2 : 2 * π * 2⁻¹ = π := by ring
  have hc : Real.cos (2 * π * (1 / 2)) = -1 := by rw [hπ1, Real.cos_pi]
  have hH0 : shearH ![0, 0] = ![0, 0] := by simp [shearH]
  have hV0 : shearV ![0, 0] = ![0, 0] := by simp [shearV]
  have hHi0 : shearHinv ![0, 0] = ![0, 0] := by simp [shearHinv]
  have hVi0 : shearVinv ![0, 0] = ![0, 0] := by simp [shearVinv]
  have hH1 : shearH ![1 / 2, 0] = ![1 / 2, 0] := by simp [shearH]
  have hV1 : shearV ![1 / 2, 0] = ![1 / 2, 0] := by simp [shearV, hπ2]
  have hHi1 : shearHinv ![1 / 2, 0] = ![1 / 2, 0] := by simp [shearHinv]
  have hVi1 : shearVinv ![1 / 2, 0] = ![1 / 2, 0] := by simp [shearVinv, hπ2]
  have e : ∀ x, mapF x = shearVinv (shearHinv (shearV (shearH x))) := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, hH0, hV0, hHi0, hVi0]
  · rw [e, hH1, hV1, hHi1, hVi1]
  · rw [jac_eq_of_hasFDerivAt (hasFDerivAt_mapF _), hH0, hV0, hHi0]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [matC0, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [jac_eq_of_hasFDerivAt (hasFDerivAt_mapF _), hH1, hV1, hHi1]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [matC1, Matrix.mul_apply, Fin.sum_univ_two, hc]

/-! ### The matrix law (Definition 2.3) -/

/-- Uniform probability measure on `{0,1} = Bool`. -/
def uniformBool : Measure Bool := Measure.uniformOfFinset Finset.univ

/-- The finite-set API gives each Boolean exactly the original probability `1/2`. -/
lemma uniformBool_apply_singleton (b : Bool) : uniformBool {b} = (2 : ℝ≥0∞)⁻¹ := by
  simp [uniformBool, Measure.uniformOfFinset_apply_singleton]

/-- Uniform probability measure on `𝕋²` (Lebesgue measure on the unit cell). -/
def uniformTorus : Measure (Pt 2) := volume.restrict (cell 2)

/-- Law of one pair `(ι, z)`: independent uniform variables on `{0,1}` and `𝕋²`. -/
def stepMeasure : Measure (Bool × Pt 2) := uniformBool.prod uniformTorus

instance : IsProbabilityMeasure uniformTorus :=
  ⟨by simp [uniformTorus, cell, Real.volume_Icc_pi]⟩

instance : IsProbabilityMeasure uniformBool := by
  constructor
  norm_num [uniformBool, Measure.uniformOfFinset, Fintype.sum_bool]
  simpa only [one_div] using ENNReal.add_halves 1

instance : IsProbabilityMeasure stepMeasure := by unfold stepMeasure; infer_instance

/-- The matrix `𝒥` acting on `ℝ²`. -/
def matJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The matrix `𝒥⁻¹`. -/
def matJinv : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- `A(Z) = DF⁻¹(Z)ᵀ`. -/
def matA (Z : Pt 2) : Matrix (Fin 2) (Fin 2) ℝ := (jac mapFinv Z)ᵀ

/-- `Q = 𝒥^ι A 𝒥^{-ι}` (Definition 2.3). -/
def matQ (w : Bool × Pt 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  if w.1 then matJ * matA w.2 * matJinv else matA w.2

/-- The entries of a `2 × 2` matrix, as a point of `Fin 2 → Fin 2 → ℝ` (used to speak about
laws of random matrices). -/
def matEntries (A : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => A i j


lemma fderiv_eq_matCLM_jac (Φ : Pt 2 → Pt 2) (y : Pt 2) :
    fderiv ℝ Φ y = matCLM (jac Φ y) := by
  ext v i
  simp only [matCLM_apply, jac, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hv : v = ∑ j, v j • (Pi.single j 1 : Pt 2) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, mul_comm]

lemma hasFDerivAt_mapFinv_jac (y : Pt 2) : HasFDerivAt mapFinv (matCLM (jac mapFinv y)) y := by
  rw [← fderiv_eq_matCLM_jac]
  exact (contDiff_mapFinv.differentiable (by simp) y).hasFDerivAt

lemma jac_mapGinv_false (z x : Pt 2) : jac (mapGinv false z) x = jac mapFinv (x - z) := by
  have h := hasFDerivAt_translate (z := z) (x := x) (hasFDerivAt_mapFinv_jac (x - z))
  have e : mapGinv false z = fun x => z + mapFinv (x - z) := by
    funext x; simp [mapGinv, conjJ]
  rw [e, jac_eq_of_hasFDerivAt h]

lemma jac_mapGinv_true (z x : Pt 2) : jac (mapGinv true z) x =
    !![0, -1; 1, 0] * (jac mapFinv (rotJinv (x - z)) * !![0, 1; -1, 0]) := by
  set y := x - z
  have h1 : HasFDerivAt rotJinv (matCLM !![0, 1; -1, 0]) y := by
    rw [rotJinv_eq_matCLM]; exact (matCLM _).hasFDerivAt
  have h2 : HasFDerivAt rotJ (matCLM !![0, -1; 1, 0]) (mapFinv (rotJinv y)) := by
    rw [rotJ_eq_matCLM]; exact (matCLM _).hasFDerivAt
  have h := h2.comp y ((hasFDerivAt_mapFinv_jac (rotJinv y)).comp y h1)
  simp only [matCLM_mul] at h
  have h' := hasFDerivAt_translate (z := z) (x := x) (Φ := conjJ true mapFinv) h
  have e : mapGinv true z = fun x => z + conjJ true mapFinv (x - z) := rfl
  rw [e, jac_eq_of_hasFDerivAt h']

lemma jac_mapFinv_periodic (y : Pt 2) (n : Fin 2 → ℤ) :
    jac mapFinv (y + intVec n) = jac mapFinv y := by
  have : fderiv ℝ mapFinv (y + intVec n) = fderiv ℝ mapFinv y := by
    rw [← fderiv_comp_add_right]
    have e : (fun x => mapFinv (x + intVec n)) = fun x => mapFinv x + intVec n := by
      funext x; exact isLift_mapFinv x n
    rw [e, fderiv_add_const]
  simp [jac, this]

lemma continuous_jac_mapFinv : Continuous (jac mapFinv) := by
  have hc : Continuous (fderiv ℝ mapFinv) := contDiff_mapFinv.continuous_fderiv (by simp)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [jac, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((ContinuousLinearMap.apply ℝ (Pt 2) (Pi.single j 1 : Pt 2)).continuous.comp hc)

lemma continuous_matQ (ι : Bool) : Continuous fun Z => matEntries (matQ (ι, Z)) := by
  have hA : Continuous matA := by
    unfold matA
    exact continuous_jac_mapFinv.matrix_transpose
  have hentries : Continuous (matEntries : Matrix (Fin 2) (Fin 2) ℝ → Fin 2 → Fin 2 → ℝ) :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  cases ι
  · simpa only [matQ, Bool.false_eq_true, if_false, Function.comp_def] using hentries.comp hA
  · simpa only [matQ, if_true, Function.comp_def] using
      hentries.comp ((continuous_const.matrix_mul hA).matrix_mul continuous_const)

lemma matQ_periodic (ι : Bool) : IsPeriodic fun Z => matEntries (matQ (ι, Z)) := by
  intro Z n
  simp [matQ, matA, jac_mapFinv_periodic]

lemma jac_mapGinv_transpose (ι : Bool) (z x : Pt 2) :
    (jac (mapGinv ι z) x)ᵀ = matQ (ι, if ι then rotJinv (x - z) else x - z) := by
  cases ι
  · simp [jac_mapGinv_false, matQ, matA]
  · rw [jac_mapGinv_true]
    simp only [matQ, matA, if_true, Matrix.transpose_mul]
    have e1 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = matJ := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    have e2 : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = matJinv := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [e1, e2, Matrix.mul_assoc]

lemma stepMeasure_map_congr {β : Type*} [MeasurableSpace β] (F G : Bool × Pt 2 → β)
    (hF : ∀ ι, Measurable fun z => F (ι, z)) (hG : ∀ ι, Measurable fun z => G (ι, z))
    (h : ∀ ι, uniformTorus.map (fun z => F (ι, z)) = uniformTorus.map (fun z => G (ι, z))) :
    stepMeasure.map F = stepMeasure.map G := by
  have hF' : Measurable F := measurable_from_prod_countable_right hF
  have hG' : Measurable G := measurable_from_prod_countable_right hG
  ext s hs
  rw [Measure.map_apply hF' hs, Measure.map_apply hG' hs, stepMeasure,
    Measure.prod_apply (hF' hs), Measure.prod_apply (hG' hs)]
  refine lintegral_congr fun ι => ?_
  have := congrArg (fun μ : Measure β => μ s) (h ι)
  simp only [Measure.map_apply (hF ι) hs, Measure.map_apply (hG ι) hs] at this
  exact this

/-- **Lemma 2.4.**  For fixed `x`, `DG_{ι,z}⁻¹(x)ᵀ` has the law of `Q`. -/
theorem single_derivative_law (x : Pt 2) :
    stepMeasure.map (fun w : Bool × Pt 2 => matEntries (jac (mapGinv w.1 w.2) x)ᵀ) =
      stepMeasure.map (fun w => matEntries (matQ w)) := by
  have hrot : ∀ z : Pt 2, rotJinv (x - z) = ![x 1 - z 1, z 0 - x 0] := by
    intro z; exact vec2_ext (by simp [rotJinv]) (by simp [rotJinv])
  have hform : ∀ ι z, matEntries (jac (mapGinv ι z) x)ᵀ =
      matEntries (matQ (ι, if ι then ![x 1 - z 1, z 0 - x 0] else x - z)) := by
    intro ι z; rw [jac_mapGinv_transpose]; cases ι <;> simp [hrot]
  refine stepMeasure_map_congr _ _ (fun ι => ?_) (fun ι => (continuous_matQ ι).measurable)
    (fun ι => ?_)
  · simp only [hform]
    cases ι
    · exact ((continuous_matQ false).comp (continuous_const.sub continuous_id)).measurable
    · refine ((continuous_matQ true).comp ?_).measurable
      exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
  · simp only [hform]
    cases ι
    · exact map_cell_sub_left _ (continuous_matQ false) (matQ_periodic false) x
    · exact map_cell_rot_sub _ (continuous_matQ true) (matQ_periodic true) x


/-- The product `Q_L ⋯ Q_1` of the matrices attached to `L` parameter pairs. -/
def prodQ {L : ℕ} (w : Fin L → Bool × Pt 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (List.ofFn fun i => matQ (w i)).reverse.prod

/-- The negative moment bound `sup_{|e|=1} 𝔼|Q_L ⋯ Q_1 e|^{-σ} ≤ 1/(128 q^σ)`. -/
def NegMomentBound (q σ : ℝ) (L : ℕ) : Prop :=
  ∀ e : Pt 2, euclNorm e = 1 →
    ∫ w, euclNorm ((prodQ w) *ᵥ e) ^ (-σ) ∂(Measure.pi fun _ : Fin L => stepMeasure)
      ≤ 1 / (128 * q ^ σ)


/-! ### The random block map (Definition 2.6) -/

/-- The block map `𝓕 = G_{ι_L,z_L} ∘ ⋯ ∘ G_{ι_1,z_1}`. -/
def blockMap {L : ℕ} (w : Fin L → Bool × Pt 2) (x : Pt 2) : Pt 2 :=
  (List.ofFn w).foldl (fun y p => mapG p.1 p.2 y) x

/-- The inverse block map `𝓕⁻¹ = G_{ι_1,z_1}⁻¹ ∘ ⋯ ∘ G_{ι_L,z_L}⁻¹`. -/
def blockMapInv {L : ℕ} (w : Fin L → Bool × Pt 2) (x : Pt 2) : Pt 2 :=
  (List.ofFn w).foldr (fun p y => mapGinv p.1 p.2 y) x

/-! ### Auxiliary results for Lemma 2.7 -/

lemma foldr_mapGinv_foldl_mapG (l : List (Bool × Pt 2)) (x : Pt 2) :
    l.foldr (fun p y => mapGinv p.1 p.2 y) (l.foldl (fun y p => mapG p.1 p.2 y) x) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, List.foldr_cons, ih, mapGinv_mapG]

lemma foldl_mapG_foldr_mapGinv (l : List (Bool × Pt 2)) (x : Pt 2) :
    l.foldl (fun y p => mapG p.1 p.2 y) (l.foldr (fun p y => mapGinv p.1 p.2 y) x) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, List.foldr_cons, mapG_mapGinv, ih]

lemma blockMap_inverse {L : ℕ} (w : Fin L → Bool × Pt 2) :
    Function.LeftInverse (blockMapInv w) (blockMap w) ∧
      Function.RightInverse (blockMapInv w) (blockMap w) :=
  ⟨fun x => foldr_mapGinv_foldl_mapG _ x, fun x => foldl_mapG_foldr_mapGinv _ x⟩


lemma periodic_bdd {d : ℕ} {F : Type*} [NormedAddCommGroup F] (h : Pt d → F) (hc : Continuous h)
    (hp : IsPeriodic h) : ∃ C, ∀ y, ‖h y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Pt d)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun y => ?_⟩
  set n : Fin d → ℤ := fun i => ⌊y i⌋
  have hz : y - intVec n ∈ Icc (0 : Pt d) 1 := by
    constructor <;> intro i <;> simp only [Pi.sub_apply, intVec, Pi.zero_apply, Pi.one_apply, n]
    · exact sub_nonneg.2 (Int.floor_le _)
    · linarith [Int.lt_floor_add_one (y i)]
  have := hp (y - intVec n) n
  rw [sub_add_cancel] at this
  rw [this]; exact hC _ hz

lemma iteratedFDeriv_add_const_of_ne {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) {n : ℕ}
    (hn : n ≠ 0) (c : F) (x : E) :
    iteratedFDeriv ℝ n (fun y => f y + c) x = iteratedFDeriv ℝ n f x := by
  have : (fun y => f y + c) = f + fun _ => c := rfl
  rw [this, iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    contDiffAt_const, iteratedFDeriv_const_of_ne hn, Pi.zero_apply, add_zero]

/-- A family of smooth self-maps of `ℝ²` all of whose positive-order derivatives are bounded
uniformly over the family (for each finite range of orders). -/
def UnifDerivBdd (S : Set (Pt 2 → Pt 2)) : Prop :=
  (∀ Φ ∈ S, ContDiff ℝ ∞ Φ) ∧
    ∀ n : ℕ, ∃ C, ∀ Φ ∈ S, ∀ x, ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Φ x‖ ≤ C

lemma UnifDerivBdd.comp {S T : Set (Pt 2 → Pt 2)} (hS : UnifDerivBdd S) (hT : UnifDerivBdd T) :
    UnifDerivBdd {Φ | ∃ g ∈ S, ∃ f ∈ T, Φ = g ∘ f} := by
  refine ⟨?_, fun n => ?_⟩
  · rintro _ ⟨g, hg, f, hf, rfl⟩; exact (hS.1 g hg).comp (hT.1 f hf)
  obtain ⟨Cg, hCg⟩ := hS.2 n
  obtain ⟨Cf, hCf⟩ := hT.2 n
  set D := max 1 Cf
  set C := max 0 Cg
  refine ⟨n.factorial * C * D ^ n, ?_⟩
  rintro _ ⟨g, hg, f, hf, rfl⟩ x i hi1 hin
  have hgs := hS.1 g hg
  have hfs := hT.1 f hf
  set g' : Pt 2 → Pt 2 := fun y => g y + (-g (f x))
  have hg's : ContDiff ℝ ∞ g' := hgs.add contDiff_const
  have hcomp : iteratedFDeriv ℝ i (g ∘ f) x = iteratedFDeriv ℝ i (g' ∘ f) x := by
    have : g' ∘ f = fun y => (g ∘ f) y + (-g (f x)) := rfl
    rw [this, iteratedFDeriv_add_const_of_ne (hgs.comp hfs) (by omega)]
  have key := norm_iteratedFDeriv_comp_le (n := i) (N := ∞) (C := C) (D := D) hg's hfs
    (by exact_mod_cast le_top) x ?_ ?_
  · rw [hcomp]
    refine key.trans ?_
    have hD : 1 ≤ D := le_max_left _ _
    have hC : 0 ≤ C := le_max_left _ _
    gcongr
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDeriv_zero]
      simp only [g', add_neg_cancel, norm_zero]
      exact le_max_left _ _
    · rw [iteratedFDeriv_add_const_of_ne hgs (by omega)]
      exact (hCg g hg (f x) j hj0 (hj.trans hin)).trans (le_max_right _ _)
  · intro j hj1 hj
    calc _ ≤ Cf := hCf f hf x j hj1 (hj.trans hin)
      _ ≤ D := le_max_right _ _
      _ ≤ D ^ j := le_self_pow₀ (le_max_left _ _) (by omega)

lemma iteratedFDeriv_bdd_of_isLift {Φ : Pt 2 → Pt 2} (hΦ : ContDiff ℝ ∞ Φ) (hl : IsLift Φ)
    {i : ℕ} (hi : i ≠ 0) : ∃ C, ∀ x, ‖iteratedFDeriv ℝ i Φ x‖ ≤ C := by
  refine periodic_bdd _ (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top)) ?_
  intro x n
  rw [← iteratedFDeriv_comp_add_right]
  have : (fun z => Φ (z + intVec n)) = fun z => Φ z + intVec n := funext fun z => hl z n
  rw [this, iteratedFDeriv_add_const_of_ne hΦ hi]


lemma UnifDerivBdd.mono {S T : Set (Pt 2 → Pt 2)} (hT : UnifDerivBdd T) (h : S ⊆ T) :
    UnifDerivBdd S :=
  ⟨fun Φ hΦ => hT.1 Φ (h hΦ), fun n => (hT.2 n).imp fun _ hC Φ hΦ => hC Φ (h hΦ)⟩

lemma cumBound_of_isLift {Φ : Pt 2 → Pt 2} (hΦ : ContDiff ℝ ∞ Φ) (hl : IsLift Φ) (n : ℕ) :
    ∃ C, ∀ x i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Φ x‖ ≤ C := by
  induction n with
  | zero => exact ⟨0, fun x i h1 h2 => by omega⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := iteratedFDeriv_bdd_of_isLift hΦ hl (i := n + 1) (by omega)
    refine ⟨max C C', fun x i h1 h2 => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (hC x i h1 (by omega)).trans (le_max_left _ _)
    · obtain rfl : i = n + 1 := by omega
      exact (hC' x).trans (le_max_right _ _)

lemma iteratedFDeriv_translate_conj {Ψ : Pt 2 → Pt 2} (hΨ : ContDiff ℝ ∞ Ψ) (z x : Pt 2) {i : ℕ}
    (hi : i ≠ 0) :
    iteratedFDeriv ℝ i (fun y => z + Ψ (y - z)) x = iteratedFDeriv ℝ i Ψ (x - z) := by
  have : (fun y => z + Ψ (y - z)) = fun y => Ψ (y - z) + z := funext fun y => add_comm _ _
  have hc : ContDiff ℝ ∞ (fun y => Ψ (y - z)) := hΨ.comp (contDiff_id.sub contDiff_const)
  rw [this, iteratedFDeriv_add_const_of_ne hc hi, iteratedFDeriv_comp_sub]

lemma unifDerivBdd_translates {Ψ : Bool → Pt 2 → Pt 2} (hΨ : ∀ ι, ContDiff ℝ ∞ (Ψ ι))
    (hl : ∀ ι, IsLift (Ψ ι)) :
    UnifDerivBdd {Φ | ∃ ι z, Φ = fun y => z + Ψ ι (y - z)} := by
  refine ⟨?_, fun n => ?_⟩
  · rintro _ ⟨ι, z, rfl⟩
    exact contDiff_const.add ((hΨ ι).comp (contDiff_id.sub contDiff_const))
  obtain ⟨C0, h0⟩ := cumBound_of_isLift (hΨ false) (hl false) n
  obtain ⟨C1, h1⟩ := cumBound_of_isLift (hΨ true) (hl true) n
  refine ⟨max C0 C1, ?_⟩
  rintro _ ⟨ι, z, rfl⟩ x i hi1 hin
  rw [iteratedFDeriv_translate_conj (hΨ ι) z x (by omega)]
  cases ι
  · exact (h0 _ i hi1 hin).trans (le_max_left _ _)
  · exact (h1 _ i hi1 hin).trans (le_max_right _ _)

lemma unifDerivBdd_mapG : UnifDerivBdd {Φ | ∃ p : Bool × Pt 2, Φ = mapG p.1 p.2} :=
  (unifDerivBdd_translates (Ψ := fun ι => conjJ ι mapF) (fun ι => contDiff_conjJ ι contDiff_mapF)
    (fun ι => isLift_conjJ ι isLift_mapF)).mono (by
      rintro _ ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩)

lemma unifDerivBdd_mapGinv : UnifDerivBdd {Φ | ∃ p : Bool × Pt 2, Φ = mapGinv p.1 p.2} :=
  (unifDerivBdd_translates (Ψ := fun ι => conjJ ι mapFinv)
    (fun ι => contDiff_conjJ ι contDiff_mapFinv)
    (fun ι => isLift_conjJ ι isLift_mapFinv)).mono (by
      rintro _ ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩)

lemma unifDerivBdd_id : UnifDerivBdd {(id : Pt 2 → Pt 2)} := by
  refine ⟨fun Φ hΦ => by rw [hΦ]; exact contDiff_id, fun n => ?_⟩
  obtain ⟨C, hC⟩ := cumBound_of_isLift (Φ := id) contDiff_id (fun x n => rfl) n
  exact ⟨C, fun Φ hΦ => by rw [hΦ]; exact hC⟩

lemma unifDerivBdd_foldl (k : ℕ) :
    UnifDerivBdd {Φ | ∃ l : List (Bool × Pt 2), l.length = k ∧
      Φ = fun x => l.foldl (fun y p => mapG p.1 p.2 y) x} := by
  induction k with
  | zero =>
    refine unifDerivBdd_id.mono ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [List.length_eq_zero_iff.1 hl]; rfl
  | succ k ih =>
    refine (ih.comp unifDerivBdd_mapG).mono ?_
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    exact ⟨_, ⟨l, by simpa using hl, rfl⟩, _, ⟨a, rfl⟩, rfl⟩

lemma unifDerivBdd_foldr (k : ℕ) :
    UnifDerivBdd {Φ | ∃ l : List (Bool × Pt 2), l.length = k ∧
      Φ = fun x => l.foldr (fun p y => mapGinv p.1 p.2 y) x} := by
  induction k with
  | zero =>
    refine unifDerivBdd_id.mono ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [List.length_eq_zero_iff.1 hl]; rfl
  | succ k ih =>
    refine (unifDerivBdd_mapGinv.comp ih).mono ?_
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    exact ⟨_, ⟨a, rfl⟩, _, ⟨l, by simpa using hl, rfl⟩, rfl⟩

lemma blockMap_deriv_bounds (L : ℕ) (a : ℕ) (ha : 1 ≤ a) :
    ∃ C, ∀ (w : Fin L → Bool × Pt 2) x, ‖iteratedFDeriv ℝ a (blockMap w) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ a (blockMapInv w) x‖ ≤ C := by
  obtain ⟨C1, h1⟩ := (unifDerivBdd_foldl L).2 a
  obtain ⟨C2, h2⟩ := (unifDerivBdd_foldr L).2 a
  refine ⟨max C1 C2, fun w x => ⟨?_, ?_⟩⟩
  · exact (h1 (blockMap w) ⟨List.ofFn w, List.length_ofFn, rfl⟩ x a ha le_rfl).trans
      (le_max_left _ _)
  · exact (h2 (blockMapInv w) ⟨List.ofFn w, List.length_ofFn, rfl⟩ x a ha le_rfl).trans
      (le_max_right _ _)


lemma continuous_matQ_joint : Continuous matQ := by
  rw [continuous_prod_of_discrete_left]
  intro ι
  exact continuous_matQ ι

lemma continuous_prodQ (L : ℕ) : Continuous fun w : Fin L → Bool × Pt 2 => prodQ w := by
  unfold prodQ
  simp only [List.ofFn_eq_map, ← List.map_reverse]
  exact continuous_list_prod _ fun i _ => continuous_matQ_joint.comp (continuous_apply i)

lemma measurable_prodQ_entries (L : ℕ) :
    Measurable fun w : Fin L → Bool × Pt 2 => matEntries (prodQ w) :=
  (show Continuous fun w : Fin L → Bool × Pt 2 => matEntries (prodQ w) from
    continuous_prodQ L).measurable


lemma neg_moment_of_law (q σ : ℝ) (L : ℕ) (h : NegMomentBound q σ L)
    (F : (Fin L → Bool × Pt 2) → Matrix (Fin 2) (Fin 2) ℝ)
    (hFm : AEMeasurable (fun w => matEntries (F w))
      (Measure.pi fun _ : Fin L => stepMeasure))
    (hF : (Measure.pi fun _ : Fin L => stepMeasure).map (fun w => matEntries (F w)) =
      (Measure.pi fun _ : Fin L => stepMeasure).map (fun w => matEntries (prodQ w)))
    (e : Pt 2) (he : euclNorm e = 1) :
    ∫ w, euclNorm (F w *ᵥ e) ^ (-σ) ∂(Measure.pi fun _ : Fin L => stepMeasure)
      ≤ 1 / (128 * q ^ σ) := by
  set μ := Measure.pi fun _ : Fin L => stepMeasure
  set φ : (Fin 2 → Fin 2 → ℝ) → ℝ := fun m => euclNorm (Matrix.of m *ᵥ e) ^ (-σ)
  have hφ : Measurable φ := by
    refine Measurable.pow_const ?_ _
    unfold euclNorm
    refine Continuous.measurable ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hQ := measurable_prodQ_entries L
  have e1 : ∫ w, euclNorm (F w *ᵥ e) ^ (-σ) ∂μ = ∫ m, φ m ∂(μ.map fun w => matEntries (F w)) := by
    rw [integral_map hFm hφ.aestronglyMeasurable]; rfl
  have e2 : ∫ w, euclNorm (prodQ w *ᵥ e) ^ (-σ) ∂μ =
      ∫ m, φ m ∂(μ.map fun w => matEntries (prodQ w)) := by
    rw [integral_map hQ.aemeasurable hφ.aestronglyMeasurable]; rfl
  rw [e1, hF, ← e2]
  exact h e he


lemma continuous_of_bool_param {γ : Type*} [TopologicalSpace γ] (f : Bool → Pt 2 → Pt 2 → γ)
    (hf : ∀ ι, Continuous fun p : Pt 2 × Pt 2 => f ι p.1 p.2) :
    Continuous fun q : (Bool × Pt 2) × Pt 2 => f q.1.1 q.1.2 q.2 := by
  have h : Continuous fun r : Bool × (Pt 2 × Pt 2) => f r.1 r.2.1 r.2.2 :=
    continuous_prod_of_discrete_left.2 fun ι => hf ι
  exact h.comp ((continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

lemma continuous_mapGinv_joint :
    Continuous fun q : (Bool × Pt 2) × Pt 2 => mapGinv q.1.1 q.1.2 q.2 :=
  continuous_of_bool_param (fun ι z x => mapGinv ι z x) fun ι => by
    unfold mapGinv
    have := (contDiff_conjJ ι contDiff_mapFinv).continuous
    fun_prop

lemma continuous_jac_mapGinv_joint :
    Continuous fun q : (Bool × Pt 2) × Pt 2 => jac (mapGinv q.1.1 q.1.2) q.2 := by
  have e : (fun q : (Bool × Pt 2) × Pt 2 => jac (mapGinv q.1.1 q.1.2) q.2) =
      fun q => (matQ (q.1.1, if q.1.1 then rotJinv (q.2 - q.1.2) else q.2 - q.1.2))ᵀ := by
    funext q; rw [← jac_mapGinv_transpose, Matrix.transpose_transpose]
  rw [e]
  refine Continuous.matrix_transpose ?_
  refine continuous_of_bool_param (fun ι z x => (matQ (ι, if ι then rotJinv (x - z) else x - z)))
    fun ι => ?_
  refine continuous_matQ_joint.comp ?_
  cases ι
  · simp only [Bool.false_eq_true, if_false]; fun_prop
  · simp only [if_true]
    have : Continuous rotJinv := contDiff_rotJinv.continuous
    fun_prop

lemma blockMapInv_snoc {L : ℕ} (w : Fin (L + 1) → Bool × Pt 2) (x : Pt 2) :
    blockMapInv w x = blockMapInv (Fin.init w) (mapGinv (w (Fin.last L)).1 (w (Fin.last L)).2 x) := by
  rw [blockMapInv, blockMapInv, List.ofFn_succ', List.concat_eq_append, List.foldr_append]
  rfl

lemma prodQ_snoc {L : ℕ} (w : Fin (L + 1) → Bool × Pt 2) :
    prodQ w = matQ (w (Fin.last L)) * prodQ (Fin.init w) := by
  rw [prodQ, prodQ, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  simp [Fin.init]

lemma blockMapInv_zero (w : Fin 0 → Bool × Pt 2) : blockMapInv w = id := by
  funext x; simp [blockMapInv]

lemma contDiff_blockMapInv {L : ℕ} (w : Fin L → Bool × Pt 2) : ContDiff ℝ ∞ (blockMapInv w) :=
  (unifDerivBdd_foldr L).1 _ ⟨List.ofFn w, List.length_ofFn, rfl⟩

lemma jac_comp' {f g : Pt 2 → Pt 2} {x : Pt 2} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) : jac (f ∘ g) x = jac f (g x) * jac g x := by
  apply jac_eq_of_hasFDerivAt
  have h := hf.hasFDerivAt.comp x hg.hasFDerivAt
  rw [fderiv_eq_matCLM_jac, fderiv_eq_matCLM_jac, matCLM_mul] at h
  exact h

lemma jac_id' (x : Pt 2) : jac id x = 1 := by
  apply jac_eq_of_hasFDerivAt
  convert hasFDerivAt_id (𝕜 := ℝ) x using 1
  ext v : 1; simp [matCLM_apply]

lemma jac_blockMapInv_snoc {L : ℕ} (w : Fin (L + 1) → Bool × Pt 2) (x : Pt 2) :
    jac (blockMapInv w) x = jac (blockMapInv (Fin.init w))
        (mapGinv (w (Fin.last L)).1 (w (Fin.last L)).2 x) *
      jac (mapGinv (w (Fin.last L)).1 (w (Fin.last L)).2) x := by
  have e : blockMapInv w = blockMapInv (Fin.init w) ∘
      mapGinv (w (Fin.last L)).1 (w (Fin.last L)).2 := funext fun x => blockMapInv_snoc w x
  rw [e, jac_comp' ((contDiff_blockMapInv _).differentiable (by simp) _)
    ((contDiff_mapGinv _ _).differentiable (by simp) _)]

lemma continuous_jac_blockMapInv (L : ℕ) :
    Continuous fun p : (Fin L → Bool × Pt 2) × Pt 2 => jac (blockMapInv p.1) p.2 := by
  induction L with
  | zero =>
    have : (fun p : (Fin 0 → Bool × Pt 2) × Pt 2 => jac (blockMapInv p.1) p.2) = fun _ => 1 := by
      funext p; rw [blockMapInv_zero, jac_id']
    rw [this]; exact continuous_const
  | succ L ih =>
    simp only [jac_blockMapInv_snoc]
    have hlast : Continuous fun p : (Fin (L + 1) → Bool × Pt 2) × Pt 2 => p.1 (Fin.last L) :=
      (continuous_apply _).comp continuous_fst
    have hinit : Continuous fun p : (Fin (L + 1) → Bool × Pt 2) × Pt 2 => Fin.init p.1 :=
      continuous_pi fun i => (continuous_apply _).comp continuous_fst
    have h1 := continuous_mapGinv_joint.comp (hlast.prodMk continuous_snd)
    have h2 := continuous_jac_mapGinv_joint.comp (hlast.prodMk continuous_snd)
    exact (ih.comp (hinit.prodMk h1)).matrix_mul h2


lemma measurable_matEntries_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {f : X → Matrix (Fin 2) (Fin 2) ℝ} (hf : Continuous f) :
    Measurable fun x => matEntries (f x) :=
  (show Continuous fun x => matEntries (f x) from hf).measurable

lemma map_prod_congr_fst {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (F G : α × β → γ) (hF : Measurable F) (hG : Measurable G)
    (h : ∀ a, ν.map (fun b => F (a, b)) = ν.map (fun b => G (a, b))) :
    (μ.prod ν).map F = (μ.prod ν).map G := by
  ext s hs
  rw [Measure.map_apply hF hs, Measure.map_apply hG hs, Measure.prod_apply (hF hs),
    Measure.prod_apply (hG hs)]
  refine lintegral_congr fun a => ?_
  have := congrFun (congrArg DFunLike.coe (h a)) s
  rw [Measure.map_apply (f := fun b => F (a, b)) (hF.comp measurable_prodMk_left) hs,
    Measure.map_apply (f := fun b => G (a, b)) (hG.comp measurable_prodMk_left) hs] at this
  exact this

lemma map_prod_congr_snd {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (F G : α × β → γ) (hF : Measurable F) (hG : Measurable G)
    (h : ∀ b, μ.map (fun a => F (a, b)) = μ.map (fun a => G (a, b))) :
    (μ.prod ν).map F = (μ.prod ν).map G := by
  ext s hs
  rw [Measure.map_apply hF hs, Measure.map_apply hG hs, Measure.prod_apply_symm (hF hs),
    Measure.prod_apply_symm (hG hs)]
  refine lintegral_congr fun b => ?_
  have := congrFun (congrArg DFunLike.coe (h b)) s
  rw [Measure.map_apply (f := fun a => F (a, b)) (hF.comp measurable_prodMk_right) hs,
    Measure.map_apply (f := fun a => G (a, b)) (hG.comp measurable_prodMk_right) hs] at this
  exact this

lemma pi_map_snoc {L : ℕ} {γ : Type*} [MeasurableSpace γ]
    (H : (Bool × Pt 2) × (Fin L → Bool × Pt 2) → γ) (hH : Measurable H) :
    (Measure.pi fun _ : Fin (L + 1) => stepMeasure).map (fun w => H (w (Fin.last L), Fin.init w)) =
      (stepMeasure.prod (Measure.pi fun _ : Fin L => stepMeasure)).map H := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (L + 1) => stepMeasure) (Fin.last L)
  rw [← hmp.map_eq, Measure.map_map hH (MeasurableEquiv.measurable _)]
  congr 1
  funext w
  simp [MeasurableEquiv.piFinSuccAbove]

/-- **Lemma 2.7, first part.**  For fixed `x`, `D𝓕⁻¹(x)ᵀ` has the law of `Q_L ⋯ Q_1`. -/
lemma blockMapInv_jac_law (L : ℕ) (x : Pt 2) :
    (Measure.pi fun _ : Fin L => stepMeasure).map
        (fun w => matEntries (jac (blockMapInv w) x)ᵀ) =
      (Measure.pi fun _ : Fin L => stepMeasure).map (fun w => matEntries (prodQ w)) := by
  induction L generalizing x with
  | zero =>
    congr 1; funext w
    rw [blockMapInv_zero, jac_id']; simp [prodQ]
  | succ L ih =>
    set C : Bool × Pt 2 → Matrix (Fin 2) (Fin 2) ℝ := fun a => (jac (mapGinv a.1 a.2) x)ᵀ
    set y : Bool × Pt 2 → Pt 2 := fun a => mapGinv a.1 a.2 x
    have hCc : Continuous C :=
      (continuous_jac_mapGinv_joint.comp (continuous_id.prodMk continuous_const)).matrix_transpose
    have hyc : Continuous y := continuous_mapGinv_joint.comp (continuous_id.prodMk continuous_const)
    have hJc := continuous_jac_blockMapInv L
    set H1 : (Bool × Pt 2) × (Fin L → Bool × Pt 2) → Fin 2 → Fin 2 → ℝ :=
      fun p => matEntries (C p.1 * (jac (blockMapInv p.2) (y p.1))ᵀ)
    set H2 : (Bool × Pt 2) × (Fin L → Bool × Pt 2) → Fin 2 → Fin 2 → ℝ :=
      fun p => matEntries (matQ p.1 * prodQ p.2)
    set H3 : (Bool × Pt 2) × (Fin L → Bool × Pt 2) → Fin 2 → Fin 2 → ℝ :=
      fun p => matEntries (C p.1 * prodQ p.2)
    have hH1 : Measurable H1 := measurable_matEntries_of_continuous
      ((hCc.comp continuous_fst).matrix_mul
        (hJc.comp (continuous_snd.prodMk (hyc.comp continuous_fst))).matrix_transpose)
    have hH2 : Measurable H2 := measurable_matEntries_of_continuous
      ((continuous_matQ_joint.comp continuous_fst).matrix_mul
        ((continuous_prodQ L).comp continuous_snd))
    have hH3 : Measurable H3 := measurable_matEntries_of_continuous
      ((hCc.comp continuous_fst).matrix_mul ((continuous_prodQ L).comp continuous_snd))
    have hL : (fun w : Fin (L + 1) → Bool × Pt 2 => matEntries (jac (blockMapInv w) x)ᵀ) =
        fun w => H1 (w (Fin.last L), Fin.init w) := by
      funext w; simp only [H1, C, y, jac_blockMapInv_snoc, Matrix.transpose_mul]
    have hR : (fun w : Fin (L + 1) → Bool × Pt 2 => matEntries (prodQ w)) =
        fun w => H2 (w (Fin.last L), Fin.init w) := by
      funext w; simp only [H2, prodQ_snoc]
    rw [hL, hR, pi_map_snoc _ hH1, pi_map_snoc _ hH2]
    refine (map_prod_congr_fst _ _ H1 H3 hH1 hH3 fun a => ?_).trans
      (map_prod_congr_snd _ _ H3 H2 hH3 hH2 fun b => ?_)
    · set g : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ := fun m => matEntries (C a * Matrix.of m)
      have hg : Measurable g := measurable_matEntries_of_continuous (continuous_const.matrix_mul
        (show Continuous fun m : Fin 2 → Fin 2 → ℝ => Matrix.of m from continuous_id))
      have hJm : Measurable fun b : Fin L → Bool × Pt 2 =>
          matEntries (jac (blockMapInv b) (y a))ᵀ :=
        measurable_matEntries_of_continuous
          (hJc.comp (continuous_id.prodMk continuous_const)).matrix_transpose
      have e1 : (fun b => H1 (a, b)) = g ∘ fun b => matEntries (jac (blockMapInv b) (y a))ᵀ := rfl
      have e2 : (fun b => H3 (a, b)) = g ∘ fun b => matEntries (prodQ b) := rfl
      rw [e1, e2, ← Measure.map_map hg hJm, ih (y a), Measure.map_map hg (measurable_prodQ_entries L)]
    · set g : (Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ := fun m => matEntries (Matrix.of m * prodQ b)
      have hg : Measurable g := measurable_matEntries_of_continuous
        ((show Continuous fun m : Fin 2 → Fin 2 → ℝ => Matrix.of m from continuous_id).matrix_mul
          continuous_const)
      have hCm : Measurable fun a => matEntries (C a) := measurable_matEntries_of_continuous hCc
      have hQm : Measurable fun a => matEntries (matQ a) :=
        measurable_matEntries_of_continuous continuous_matQ_joint
      have e1 : (fun a => H3 (a, b)) = g ∘ fun a => matEntries (C a) := rfl
      have e2 : (fun a => H2 (a, b)) = g ∘ fun a => matEntries (matQ a) := rfl
      rw [e1, e2, ← Measure.map_map hg hCm, ← Measure.map_map hg hQm]
      exact congrArg (fun m => m.map g) (single_derivative_law x)

/-- **Lemma 2.7.**  If the negative moment bound of Lemma 2.5 holds for `(σ,L)`, then for every
fixed `x`, `D𝓕⁻¹(x)ᵀ` has the law of `Q_L ⋯ Q_1`, hence
`sup_{x,|e|=1} 𝔼|D𝓕⁻¹(x)ᵀ e|^{-σ} ≤ 1/(128 q^σ)`; moreover all positive-order derivatives of
the block maps and of their inverses are bounded uniformly over the parameters. -/
theorem block_map_negative (q σ : ℝ) (L : ℕ) (h : NegMomentBound q σ L) :
    (∀ x, (Measure.pi fun _ : Fin L => stepMeasure).map
        (fun w => matEntries (jac (blockMapInv w) x)ᵀ) =
      (Measure.pi fun _ : Fin L => stepMeasure).map (fun w => matEntries (prodQ w))) ∧
    (∀ x, ∀ e : Pt 2, euclNorm e = 1 →
      ∫ w, euclNorm ((jac (blockMapInv w) x)ᵀ *ᵥ e) ^ (-σ)
          ∂(Measure.pi fun _ : Fin L => stepMeasure) ≤ 1 / (128 * q ^ σ)) ∧
    (∀ w : Fin L → Bool × Pt 2, Function.LeftInverse (blockMapInv w) (blockMap w) ∧
      Function.RightInverse (blockMapInv w) (blockMap w)) ∧
    (∀ a : ℕ, 1 ≤ a → ∃ C, ∀ (w : Fin L → Bool × Pt 2) x, ‖iteratedFDeriv ℝ a (blockMap w) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ a (blockMapInv w) x‖ ≤ C) :=
  ⟨blockMapInv_jac_law L, fun x e he => neg_moment_of_law q σ L h _
    (measurable_matEntries_of_continuous
      ((continuous_jac_blockMapInv L).comp
        (continuous_id.prodMk continuous_const)).matrix_transpose).aemeasurable
    (blockMapInv_jac_law L x) e he,
    blockMap_inverse, blockMap_deriv_bounds L⟩

end AnomDiss
