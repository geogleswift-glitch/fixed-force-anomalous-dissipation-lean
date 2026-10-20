module

public import RequestProject.Shears

/-!
# Section 2.2: controls with vanishing time moments

The four-dimensional space `𝓔` of shear eigenfields, flows of controls, the moment correction
lemma, controls realizing the block maps with vanishing time moments (Lemma 2.13), the block
parameter space `Ω_b` (Definition 2.14) and the damped response `B_{μ,ω}` (Definition 2.15,
Lemma 2.16).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- The basis `(sin 2πy, 0), (cos 2πy, 0), (0, sin 2πx), (0, cos 2πx)` of `𝓔`. -/
def eBasis (i : Fin 4) (x : Pt 2) : Pt 2 :=
  match i with
  | 0 => ![Real.sin (2 * π * x 1), 0]
  | 1 => ![Real.cos (2 * π * x 1), 0]
  | 2 => ![0, Real.sin (2 * π * x 0)]
  | 3 => ![0, Real.cos (2 * π * x 0)]

/-- The element `∑ᵢ cᵢ eᵢ` of `𝓔` with coefficient vector `c` (Definition 2.8). -/
def eField (c : Fin 4 → ℝ) (x : Pt 2) : Pt 2 := ∑ i, c i • eBasis i x

/-! ### Explicit calculus for the eigenfields -/


noncomputable def sc (α β : ℝ) (t : ℝ) : ℝ := α * Real.sin (2 * π * t) + β * Real.cos (2 * π * t)

lemma hasDerivAt_sc (α β t : ℝ) : HasDerivAt (sc α β) (sc (-(2 * π * β)) (2 * π * α) t) t := by
  have h1 := ((hasDerivAt_id t).const_mul (2 * π)).sin
  have h2 := ((hasDerivAt_id t).const_mul (2 * π)).cos
  convert (h1.const_mul α).fun_add (h2.const_mul β) using 1
  · rfl
  · simp [sc]; ring

lemma deriv_sc (α β : ℝ) : deriv (sc α β) = sc (-(2 * π * β)) (2 * π * α) :=
  funext fun t => (hasDerivAt_sc α β t).deriv

lemma differentiable_sc (α β : ℝ) : Differentiable ℝ (sc α β) :=
  fun t => (hasDerivAt_sc α β t).differentiableAt

def pair2 (a b : ℝ → ℝ) (x : Pt 2) : Pt 2 := ![a (x 1), b (x 0)]

lemma hasFDerivAt_coord (k : Fin 2) (x : Pt 2) :
    HasFDerivAt (fun y : Pt 2 => y k) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k) x :=
  hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) k x

lemma hasFDerivAt_pair2 (a b : ℝ → ℝ) (x : Pt 2) (ha : DifferentiableAt ℝ a (x 1))
    (hb : DifferentiableAt ℝ b (x 0)) :
    HasFDerivAt (pair2 a b) (ContinuousLinearMap.pi fun k : Fin 2 =>
      if k = 0 then deriv a (x 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
      else deriv b (x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x := by
  rw [hasFDerivAt_pi']
  intro k
  fin_cases k
  · simp only [pair2]
    have := ha.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_coord 1 x)
    convert this using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp
  · simp only [pair2]
    have := hb.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_coord 0 x)
    convert this using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp

lemma pd_pair2_sc (α β γ δ : ℝ) (i : Fin 2) :
    pd i (pair2 (sc α β) (sc γ δ)) =
      pair2 (sc ((Pi.single i 1 : Pt 2) 1 * -(2 * π * β)) ((Pi.single i 1 : Pt 2) 1 * (2 * π * α)))
        (sc ((Pi.single i 1 : Pt 2) 0 * -(2 * π * δ)) ((Pi.single i 1 : Pt 2) 0 * (2 * π * γ))) := by
  funext x
  rw [pd, (hasFDerivAt_pair2 _ _ x (differentiable_sc _ _ _) (differentiable_sc _ _ _)).fderiv]
  ext k; fin_cases k <;> simp [pair2, deriv_sc, sc] <;> ring

lemma pd_prod2 (p q : ℝ → ℝ) (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) (i : Fin 2) :
    pd i (fun x : Pt 2 => p (x 0) * q (x 1)) = fun x =>
      (Pi.single i 1 : Pt 2) 0 * deriv p (x 0) * q (x 1) +
      p (x 0) * ((Pi.single i 1 : Pt 2) 1 * deriv q (x 1)) := by
  funext x
  have h0 := (hp (x 0)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_coord 0 x)
  have h1 := (hq (x 1)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_coord 1 x)
  have h := h0.mul h1
  rw [pd, show (fun x : Pt 2 => p (x 0) * q (x 1)) =
    ((p ∘ fun y : Pt 2 => y 0) * (q ∘ fun y : Pt 2 => y 1)) from rfl, h.fderiv]
  simp
  ring

lemma eField_eq (c : Fin 4 → ℝ) : eField c = pair2 (sc (c 0) (c 1)) (sc (c 2) (c 3)) := by
  funext x; ext k; fin_cases k <;> simp [eField, eBasis, pair2, sc, Fin.sum_univ_four]

lemma sc_add_int (α β t : ℝ) (n : ℤ) : sc α β (t + n) = sc α β t := by
  simp only [sc]
  have : 2 * π * (t + n) = 2 * π * t + n * (2 * π) := by ring
  rw [this, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

lemma contDiff_sc (α β : ℝ) : ContDiff ℝ ∞ (sc α β) := by
  unfold sc; fun_prop

lemma integral_sc (α β : ℝ) : ∫ t in (0:ℝ)..1, sc α β t = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h : ∀ t, HasDerivAt (sc (β / (2 * π)) (-(α / (2 * π)))) (sc α β t) t := by
    intro t
    convert hasDerivAt_sc _ _ t using 2 <;> field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h t)
    ((differentiable_sc α β).continuous.intervalIntegrable _ _)]
  have := sc_add_int (β / (2 * π)) (-(α / (2 * π))) 0 1
  simp at this
  rw [this]; ring

lemma cell_measure_pi : (volume : Measure (Pt 2)).restrict (cell 2) =
    Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Icc 0 1)) := by
  have hcell : cell 2 = Set.univ.pi (fun _ : Fin 2 => Icc (0:ℝ) 1) := by
    rw [cell, ← Set.pi_univ_Icc]; rfl
  rw [hcell, volume_pi, Measure.restrict_pi_pi]

lemma integral_cell_coord (g : ℝ → ℝ) (k : Fin 2) (hg : ∫ t in (0:ℝ)..1, g t = 0) :
    ∫ x in cell 2, g (x k) = 0 := by
  rw [cell_measure_pi]
  have : (fun x : Pt 2 => g (x k)) = fun x => ∏ i, (if i = k then g else fun _ => 1) (x i) := by
    funext x; fin_cases k <;> simp
  rw [this, integral_fintype_prod_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [← intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc, hg]

lemma integral_pair2 (α β γ δ : ℝ) : ∫ x in cell 2, pair2 (sc α β) (sc γ δ) x = 0 := by
  have hint : Integrable (pair2 (sc α β) (sc γ δ)) ((volume : Measure (Pt 2)).restrict (cell 2)) := by
    have hc : Continuous (pair2 (sc α β) (sc γ δ)) := continuous_pi fun k => by
      fin_cases k
      · exact (differentiable_sc α β).continuous.comp (continuous_apply 1)
      · exact (differentiable_sc γ δ).continuous.comp (continuous_apply 0)
    exact hc.integrableOn_Icc
  ext k
  rw [← ContinuousLinearMap.proj_apply (R := ℝ) k (∫ x in cell 2, pair2 (sc α β) (sc γ δ) x),
    ← ContinuousLinearMap.integral_comp_comm _ hint]
  fin_cases k
  · simpa [pair2] using integral_cell_coord (sc α β) 1 (integral_sc α β)
  · simpa [pair2] using integral_cell_coord (sc γ δ) 0 (integral_sc γ δ)

/-- **Lemma 2.9.**  Every `b ∈ 𝓔` is smooth, periodic, mean zero, divergence free, satisfies
`Δb = -4π² b`, and `b · ∇b` is the gradient of a smooth periodic function, so that its Leray
projection vanishes: `𝒫(b · ∇b) = 0`. -/
theorem eigenspace_properties (c : Fin 4 → ℝ) :
    ContDiff ℝ ∞ (eField c) ∧ IsPeriodic (eField c) ∧ (∫ x in cell 2, eField c x) = 0 ∧
    (∀ x, divergence (eField c) x = 0) ∧ (∀ x, lap (eField c) x = -(4 * π ^ 2) • eField c x) ∧
    ∃ φ : Pt 2 → ℝ, ContDiff ℝ ∞ φ ∧ IsPeriodic φ ∧
      ∀ x, conv (eField c) (eField c) x = grad φ x := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eField_eq]
    refine contDiff_pi.2 fun k => ?_
    fin_cases k
    · exact (contDiff_sc _ _).comp (contDiff_apply ℝ ℝ 1)
    · exact (contDiff_sc _ _).comp (contDiff_apply ℝ ℝ 0)
  · intro x n
    rw [eField_eq]
    ext k; fin_cases k <;> simp [pair2, intVec, sc_add_int]
  · rw [eField_eq]; exact integral_pair2 _ _ _ _
  · intro x
    simp [eField_eq, divergence, pd_pair2_sc, pair2, Fin.sum_univ_two, sc]
  · intro x
    rw [eField_eq]
    simp only [lap, pd_pair2_sc, Fin.sum_univ_two]
    ext k; fin_cases k <;> simp [pair2, sc] <;> ring
  set p := sc (-(2 * π * c 3) * (-(1 / (4 * π ^ 2)))) (2 * π * c 2 * (-(1 / (4 * π ^ 2))))
    with hp
  set q := sc (-(2 * π * c 1)) (2 * π * c 0) with hq
  refine ⟨fun x => p (x 0) * q (x 1), ?_, ?_, ?_⟩
  · have := contDiff_sc (-(2 * π * c 3) * (-(1 / (4 * π ^ 2)))) (2 * π * c 2 * (-(1 / (4 * π ^ 2))))
    have := contDiff_sc (-(2 * π * c 1)) (2 * π * c 0)
    fun_prop
  · intro x n
    simp [intVec, p, q, sc_add_int]
  · intro x
    have hpd := pd_prod2 p q (differentiable_sc _ _) (differentiable_sc _ _)
    ext k
    change _ = pd k (fun x : Pt 2 => p (x 0) * q (x 1)) x
    rw [hpd, hp, hq]
    rw [eField_eq]
    simp only [conv, pd_pair2_sc, Fin.sum_univ_two, deriv_sc]
    fin_cases k <;> simp [pair2, sc, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
      field_simp <;> ring

/-- `Φ` is the flow of the time-dependent vector field `b` started at time `0`:
`∂ₛΦ(s,x) = b(s, Φ(s,x))`, `Φ(0,x) = x` (Definition 2.10). -/
def IsFlowOf (b : ℝ → Pt 2 → Pt 2) (Φ : ℝ → Pt 2 → Pt 2) : Prop :=
  (∀ x, Φ 0 x = x) ∧ ∀ s x, HasDerivAt (fun s => Φ s x) (b s (Φ s x)) s


section MomentCorrection

/-- The polynomial `∑_{k<n} p_k X^k` with coefficient vector `p`. -/
noncomputable def polyOfCoeffs (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] Polynomial ℝ :=
  ∑ k : Fin n, (Polynomial.monomial (k : ℕ)).comp (LinearMap.proj k)

variable {n : ℕ}

lemma polyOfCoeffs_apply (p : Fin n → ℝ) :
    polyOfCoeffs n p = ∑ k : Fin n, Polynomial.monomial (k : ℕ) (p k) := by
  simp [polyOfCoeffs]

lemma eval_polyOfCoeffs (p : Fin n → ℝ) (s : ℝ) :
    (polyOfCoeffs n p).eval s = ∑ k : Fin n, p k * s ^ (k : ℕ) := by
  simp [polyOfCoeffs_apply, Polynomial.eval_finset_sum]

lemma coeff_polyOfCoeffs (p : Fin n → ℝ) (j : ℕ) :
    (polyOfCoeffs n p).coeff j = if h : j < n then p ⟨j, h⟩ else 0 := by
  rw [polyOfCoeffs_apply, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro k _ hk; rw [if_neg]; intro e; exact hk (Fin.ext e)
    · simp
  · exact Finset.sum_eq_zero fun k _ => if_neg (by omega)

lemma degree_polyOfCoeffs_lt (p : Fin n → ℝ) : (polyOfCoeffs n p).degree < n := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyOfCoeffs, dif_neg (by omega)]

lemma polyOfCoeffs_injective : Function.Injective (polyOfCoeffs n) := by
  intro p q h
  funext k
  have := congrArg (fun P => Polynomial.coeff P k) h
  simpa [coeff_polyOfCoeffs] using this

lemma polyOfCoeffs_of_degree_lt (P : Polynomial ℝ) (hP : P.degree < n) :
    P = polyOfCoeffs n (fun k => P.coeff k) := by
  ext j
  rw [coeff_polyOfCoeffs]
  split_ifs with h
  · rfl
  · exact (Polynomial.degree_lt_iff_coeff_zero P n).1 hP j (by omega)

/-- The Gram matrix `G_{rk} = ∫_a^b s^{r+k} ψ(s) ds`. -/
noncomputable def momentGram (n : ℕ) (a b : ℝ) (ψ : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun r k => ∫ s in a..b, s ^ ((r : ℕ) + k) * ψ s

lemma moment_polyOfCoeffs (a b : ℝ) (ψ : ℝ → ℝ) (hψ : Continuous ψ) (p : Fin n → ℝ)
    (r : ℕ) : ∫ s in a..b, s ^ r * (ψ s * (polyOfCoeffs n p).eval s) =
      ∑ k : Fin n, p k * ∫ s in a..b, s ^ (r + k) * ψ s := by
  simp_rw [eval_polyOfCoeffs, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext s; rw [pow_add]; ring
  · intro k _
    exact (by fun_prop : Continuous fun s => s ^ r * (ψ s * (p k * s ^ (k : ℕ)))).intervalIntegrable _ _

lemma momentGram_mulVec (a b : ℝ) (ψ : ℝ → ℝ) (hψ : Continuous ψ) (p : Fin n → ℝ) (r : Fin n) :
    (momentGram n a b ψ *ᵥ p) r = ∫ s in a..b, s ^ (r : ℕ) * (ψ s * (polyOfCoeffs n p).eval s) := by
  rw [moment_polyOfCoeffs a b ψ hψ p r]
  simp [Matrix.mulVec, dotProduct, momentGram, mul_comm]

lemma momentGram_quadratic (a b : ℝ) (ψ : ℝ → ℝ) (hψ : Continuous ψ) (p : Fin n → ℝ) :
    ∑ r, p r * (momentGram n a b ψ *ᵥ p) r =
      ∫ s in a..b, (polyOfCoeffs n p).eval s * (ψ s * (polyOfCoeffs n p).eval s) := by
  simp_rw [momentGram_mulVec a b ψ hψ p]
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finset_sum]
  · congr 1; funext s
    rw [eval_polyOfCoeffs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  · intro k _
    have : Continuous fun s => (polyOfCoeffs n p).eval s := Polynomial.continuous _
    exact (by fun_prop : Continuous fun s => p k * (s ^ (k : ℕ) * (ψ s *
      (polyOfCoeffs n p).eval s))).intervalIntegrable _ _

lemma momentGram_injective (a b : ℝ) (hab : a < b) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hψJ : tsupport ψ ⊆ Ioo a b) (hψnn : ∀ s, 0 ≤ ψ s)
    (hpos : ∃ c d, c < d ∧ ∀ s ∈ Ioo c d, 0 < ψ s) :
    Function.Injective (Matrix.mulVecLin (momentGram n a b ψ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  simp only [Matrix.mulVecLin_apply] at hp
  have h0 := momentGram_quadratic a b ψ hψ p
  rw [hp] at h0
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h0
  by_contra hne
  set P := polyOfCoeffs n p
  have hP : P ≠ 0 := fun h => hne (polyOfCoeffs_injective (by rw [map_zero]; exact h))
  obtain ⟨c, d, hcd, hcpos⟩ := hpos
  obtain ⟨s₀, hs₀, hroot⟩ : ∃ s₀ ∈ Ioo c d, ¬ P.IsRoot s₀ := by
    by_contra h
    push_neg at h
    exact hP (Polynomial.eq_zero_of_infinite_isRoot P
      ((Set.Ioo_infinite hcd).mono fun s hs => h s hs))
  have hψs₀ := hcpos s₀ hs₀
  have hs₀ab : s₀ ∈ Ioo a b := hψJ (subset_tsupport _ (ne_of_gt hψs₀))
  have hpos' : 0 < ∫ s in a..b, P.eval s * (ψ s * P.eval s) := by
    apply intervalIntegral.integral_pos hab
    · exact (by fun_prop : Continuous fun s => P.eval s * (ψ s * P.eval s)).continuousOn
    · intro s _
      have := hψnn s
      nlinarith [sq_nonneg (P.eval s)]
    · refine ⟨s₀, Ioo_subset_Icc_self hs₀ab, ?_⟩
      have : P.eval s₀ ≠ 0 := hroot
      have : 0 < P.eval s₀ ^ 2 := by positivity
      nlinarith
  linarith

lemma deriv_mul_polyOfCoeffs (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ) (q : Fin n → ℝ) (s : ℝ) :
    deriv (fun s => ψ s * (polyOfCoeffs n q).eval s) s =
      ∑ k : Fin n, q k * deriv (fun s => ψ s * s ^ (k : ℕ)) s := by
  have : (fun s => ψ s * (polyOfCoeffs n q).eval s) =
      fun s => ∑ k : Fin n, q k * (ψ s * s ^ (k : ℕ)) := by
    funext s; rw [eval_polyOfCoeffs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this, deriv_fun_sum (A := fun (k : Fin n) s => q k * (ψ s * s ^ (k : ℕ)))
    (fun k _ => by fun_prop)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact deriv_const_mul _ (by fun_prop)

end MomentCorrection

/-- **Lemma 2.11** (finite moment correction).  Let `J = (a,b)` and let `ψ ∈ C^∞` be
nonnegative, supported in `J` and positive on a nonempty open subinterval.  For every
`(m_1, …, m_{M-1})` there is a unique polynomial `P` of degree `≤ M-2` such that `φ = ψ P` has
the prescribed moments `∫_J s^{r-1} φ = m_r`; `P` depends linearly on `m`, and
`‖φ'‖_{L¹(J)} ≤ C max_r |m_r|`.  (Moments are indexed from `0` here: `r : Fin (M-1)` stands
for the paper's `r+1`.  The paper's side conditions `M ≥ 2`, `J ⋐ (0,1)` and compactness of the
support of `ψ` are not needed for the proof and have been dropped.) -/
theorem finite_moment_correction (M : ℕ) (a b : ℝ) (hab : a < b) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψJ : tsupport ψ ⊆ Ioo a b) (hψnn : ∀ s, 0 ≤ ψ s)
    (hpos : ∃ c d, c < d ∧ ∀ s ∈ Ioo c d, 0 < ψ s) :
    ∃ (Λ : (Fin (M - 1) → ℝ) →ₗ[ℝ] Polynomial ℝ) (C : ℝ), ∀ m : Fin (M - 1) → ℝ,
      (Λ m).degree < ((M - 1 : ℕ) : WithBot ℕ) ∧
      (∀ r : Fin (M - 1), ∫ s in a..b, s ^ (r : ℕ) * (ψ s * (Λ m).eval s) = m r) ∧
      (∀ P : Polynomial ℝ, P.degree < ((M - 1 : ℕ) : WithBot ℕ) →
        (∀ r : Fin (M - 1), ∫ s in a..b, s ^ (r : ℕ) * (ψ s * P.eval s) = m r) → P = Λ m) ∧
      ∫ s in a..b, |deriv (fun s => ψ s * (Λ m).eval s) s| ≤ C * ‖m‖ := by
  set n := M - 1
  have hψc := hψ.continuous
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  set G := momentGram n a b ψ
  have hinj := momentGram_injective (n := n) a b hab ψ hψc hψJ hψnn hpos
  set L := LinearEquiv.ofInjectiveEndo (Matrix.mulVecLin G) hinj
  set Λ := (polyOfCoeffs n).comp L.symm.toLinearMap
  set Lc := LinearMap.toContinuousLinearMap (L.symm.toLinearMap)
  set g : Fin n → ℝ → ℝ := fun k s => deriv (fun s => ψ s * s ^ (k : ℕ)) s
  have hgc : ∀ k, Continuous (g k) := fun k =>
    (hψ.mul (contDiff_id.pow _)).continuous_deriv (by simp)
  set I := ∫ s in a..b, ∑ k, |g k s|
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg hab.le fun s _ =>
    Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ⟨Λ, ‖Lc‖ * I, fun m => ⟨degree_polyOfCoeffs_lt _, ?_, ?_, ?_⟩⟩
  · intro r
    show ∫ s in a..b, s ^ (r : ℕ) * (ψ s * (polyOfCoeffs n (L.symm m)).eval s) = m r
    rw [← momentGram_mulVec a b ψ hψc]
    show (Matrix.mulVecLin G (L.symm m)) r = m r
    have : Matrix.mulVecLin G (L.symm m) = L (L.symm m) := rfl
    rw [this, L.apply_symm_apply]
  · intro P hP hmom
    have hPeq := polyOfCoeffs_of_degree_lt P hP
    have h1 : Matrix.mulVecLin G (fun k : Fin n => P.coeff k) = m := by
      funext r
      simp only [Matrix.mulVecLin_apply]
      rw [momentGram_mulVec a b ψ hψc, ← hPeq]; exact hmom r
    have h2 : (fun k : Fin n => P.coeff k) = L.symm m := by
      apply L.injective; rw [L.apply_symm_apply]; exact h1
    rw [hPeq, h2]; rfl
  · set q := L.symm m
    have hΛ : Λ m = polyOfCoeffs n q := rfl
    rw [hΛ]
    have hcont : Continuous fun s => |deriv (fun s => ψ s * (polyOfCoeffs n q).eval s) s| :=
      ((hψ.mul (by simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) (polyOfCoeffs n q) ∞)
        ).continuous_deriv (by simp)).abs
    calc ∫ s in a..b, |deriv (fun s => ψ s * (polyOfCoeffs n q).eval s) s|
        ≤ ∫ s in a..b, ‖q‖ * ∑ k, |g k s| := by
          refine intervalIntegral.integral_mono_on hab.le (hcont.intervalIntegrable _ _)
            ((continuous_const.mul (continuous_finset_sum _ fun k _ => (hgc k).abs)).intervalIntegrable _ _)
            fun s _ => ?_
          rw [deriv_mul_polyOfCoeffs ψ hψd q s, Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm q k) (abs_nonneg _)
      _ = ‖q‖ * I := intervalIntegral.integral_const_mul _ _
      _ ≤ (‖Lc‖ * ‖m‖) * I := mul_le_mul_of_nonneg_right (Lc.le_opNorm m) hI
      _ = ‖Lc‖ * I * ‖m‖ := by ring



lemma periodic_fderiv {d : ℕ} (X : Pt d → Pt d) (hp : IsPeriodic X) :
    IsPeriodic (fderiv ℝ X) := by
  intro x n
  rw [← fderiv_comp_add_right]
  congr 1
  funext y; exact hp y n

/-- **Lemma 2.12.**  If `c ∈ C_c^∞` has zero integral over `(a,b)`, then the flow of the
time-dependent field `c(s) X` from time `a` to time `b` is the identity.  (Only smoothness and
compact support of `c` are needed; the paper's assumption `supp c ⊆ (a,b)` is not used.) -/
theorem zero_integral_autonomous_control (X : Pt 2 → Pt 2) (hX : ContDiff ℝ ∞ X)
    (hXper : IsPeriodic X) (a b : ℝ) (hab : a < b) (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcsupp : HasCompactSupport c) (Φ : ℝ → Pt 2 → Pt 2)
    (hΦ0 : ∀ x, Φ a x = x)
    (hΦ : ∀ s ∈ Icc a b, ∀ x, HasDerivWithinAt (fun s => Φ s x) (c s • X (Φ s x)) (Icc a b) s)
    (hint : ∫ s in a..b, c s = 0) : ∀ x, Φ b x = x := by
  intro x
  -- global bounds for `X`
  have hXd : Differentiable ℝ X := hX.differentiable (by simp)
  obtain ⟨B, hB⟩ := periodic_bdd X hX.continuous hXper
  obtain ⟨D, hD⟩ := periodic_bdd (fderiv ℝ X) (hX.continuous_fderiv (by simp))
    (periodic_fderiv X hXper)
  set K : ℝ≥0 := ⟨max D 0, le_max_right _ _⟩
  have hXL : LipschitzWith K X := lipschitzWith_of_nnnorm_fderiv_le hXd fun y => by
    rw [← NNReal.coe_le_coe]
    change ‖fderiv ℝ X y‖ ≤ max D 0
    exact (hD y).trans (le_max_left _ _)
  obtain ⟨Kc, hKc⟩ := hc.continuous.bounded_above_of_compact_support hcsupp
  -- the time change `C(s) = ∫_a^s c`
  set C : ℝ → ℝ := fun s => ∫ r in a..s, c r
  have hCd : ∀ s, HasDerivAt C (c s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hc.continuous.intervalIntegrable _ _)
      (hc.continuous.stronglyMeasurableAtFilter _ _) hc.continuous.continuousAt
  have hCc : Continuous C := continuous_iff_continuousAt.2 fun s => (hCd s).continuousAt
  obtain ⟨smin, -, hsmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le) hCc.continuousOn
  obtain ⟨smax, -, hsmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab.le) hCc.continuousOn
  set m := C smin
  set M := C smax
  have hCa : C a = 0 := by simp [C]
  have hm0 : m ≤ 0 := hCa ▸ hsmin ⟨le_rfl, hab.le⟩
  have hM0 : 0 ≤ M := hCa ▸ hsmax ⟨le_rfl, hab.le⟩
  have hCmaps : MapsTo C (Icc a b) (Icc m M) := fun s hs => ⟨hsmin hs, hsmax hs⟩
  -- the autonomous flow on `[m, M]`
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set Bn : ℝ≥0 := ⟨B, hB0⟩
  set an : ℝ≥0 := ⟨B * (M - m), mul_nonneg hB0 (by linarith)⟩
  have hPL : IsPicardLindelof (fun _ => X) (tmin := m) (tmax := M) ⟨0, hm0, hM0⟩ x an 0 Bn K :=
    IsPicardLindelof.of_time_independent (fun y _ => hB y) (hXL.lipschitzOnWith)
      (by
        simp only [an, Bn, NNReal.coe_zero, sub_zero]
        change B * max M (0 - m) ≤ B * (M - m)
        apply mul_le_mul_of_nonneg_left _ hB0
        apply max_le <;> linarith)
  obtain ⟨φ, hφ0, hφ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  -- `φ ∘ C` solves the same equation as `Φ · x`
  have hg : ∀ s ∈ Icc a b, HasDerivWithinAt (φ ∘ C) (c s • X ((φ ∘ C) s)) (Icc a b) s :=
    fun s hs => (hφ (C s) (hCmaps hs)).scomp s (hCd s).hasDerivWithinAt hCmaps
  have hLip : ∀ t ∈ Ico a b, LipschitzOnWith (⟨Kc, (norm_nonneg _).trans (hKc 0)⟩ * K)
      (fun y => c t • X y) univ := by
    intro t _
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun y z => ?_)
    rw [dist_smul₀]
    calc ‖c t‖ * dist (X y) (X z) ≤ Kc * (K * dist y z) :=
          mul_le_mul (hKc t) (hXL.dist_le_mul y z) dist_nonneg ((norm_nonneg _).trans (hKc 0))
      _ = _ := by
        change Kc * ((K : ℝ) * dist y z) = (Kc * (K : ℝ)) * dist y z
        ring
  have heq := ODE_solution_unique_of_mem_Icc_right hLip
    (fun s hs => (hΦ s hs x).continuousWithinAt)
    (fun s hs => (hΦ s (Ico_subset_Icc_self hs) x).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (fun _ _ => mem_univ _)
    (fun s hs => (hg s hs).continuousWithinAt)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (fun _ _ => mem_univ _)
    (by simp [hΦ0, hCa, hφ0])
  have := heq ⟨hab.le, le_rfl⟩
  simp only [Function.comp_apply] at this
  rw [this]
  have : C b = 0 := hint
  rw [this, hφ0]


/-! ### Norms used for the controls -/

/-- The `C^a` norm `sup_x ∑_{k ≤ a} |D^k h(x)|`, valued in `[0,∞]`. -/
def cNormE {d : ℕ} (a : ℕ) (h : Pt d → Pt d) : ℝ≥0∞ :=
  ⨆ x, ∑ k ∈ Finset.range (a + 1), ‖iteratedFDeriv ℝ k h x‖ₑ

/-- Euclidean operator norm of a linear map of `ℝ^d`. -/
def eucOp {d : ℕ} (A : Pt d →L[ℝ] Pt d) : ℝ :=
  ⨆ e : {e : Pt d // euclNorm e = 1}, euclNorm (A e.1)

/-- The data provided by **Lemma 2.13** for a fixed number `M` of vanishing moments and fixed
spatial bounds `S a`: a family of controls `b_ω(s) = ∑ᵢ coef ω s i • eᵢ ∈ 𝓔`, indexed by the
parameters `ω = (ιᵢ, zᵢ)_{i ≤ L}` of the block map, smooth in time and in the phases, supported
in a fixed compact subinterval of `(0,1)`, whose terminal flow map is the block map `𝓕_ω`, with
vanishing moments `∫₀¹ sʳ b_ω(s) ds = 0` for `0 ≤ r < M`, with `∫₀¹ ‖b_ω(s)‖_{C^a} ds ≤ S a`
(and `∫₀¹ ‖∇b_ω(s)‖_{L^∞, op} ds ≤ S 1`), and with all mixed derivatives bounded uniformly
in `ω`. -/
structure ControlFamily (L M : ℕ) (S : ℕ → ℝ) where
  coef : (Fin L → Bool × Pt 2) → ℝ → Fin 4 → ℝ
  a₀ : ℝ
  b₀ : ℝ
  ha₀ : 0 < a₀
  hab₀ : a₀ < b₀
  hb₀ : b₀ < 1
  support : ∀ w s, s ∉ Icc a₀ b₀ → coef w s = 0
  smooth : ∀ ιs : Fin L → Bool,
    ContDiff ℝ ∞ (fun p : (Fin L → Pt 2) × ℝ => coef (fun i => (ιs i, p.1 i)) p.2)
  terminal : ∀ w, ∃ Φ, IsFlowOf (fun s => eField (coef w s)) Φ ∧ Φ 1 = blockMap w
  moments : ∀ w, ∀ r < M, ∫ s in (0 : ℝ)..1, s ^ r • coef w s = 0
  bound : ∀ a w, ∫⁻ s in Icc 0 1, cNormE a (eField (coef w s)) ≤ ENNReal.ofReal (S a)
  bound_grad : ∀ w, ∫⁻ s in Icc 0 1, ⨆ x, ENNReal.ofReal (eucOp (fderiv ℝ (eField (coef w s)) x))
    ≤ ENNReal.ofReal (S 1)
  mixed : ∀ r : ℕ, ∃ C, ∀ w s, ‖iteratedDeriv r (coef w) s‖ ≤ C

/- **Lemma 2.13** (controls) is stated and proved as `controls_exist` in
`RequestProject/ControlsFinal.lean`, after the construction of the controls. -/

/-! ### The block parameter space and damped responses -/

/-- The single-block parameter space `Ω_b`: the `L` pairs `(ιᵢ, zᵢ)` and one extra global
translation `z₀ ∈ 𝕋²` (Definition 2.14). -/
abbrev BlockParam (L : ℕ) := (Fin L → Bool × Pt 2) × Pt 2

/-- The law on `Ω_b`: product of uniform measures (Definition 2.14). -/
def blockMeasure (L : ℕ) : Measure (BlockParam L) :=
  (Measure.pi fun _ : Fin L => stepMeasure).prod uniformTorus

instance (L : ℕ) : IsProbabilityMeasure (blockMeasure L) := by
  unfold blockMeasure; infer_instance

/-- The control `b_ω(s,x) = b(s, x - z₀)` attached to a block parameter `ω`. -/
def bField {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) (w : BlockParam L) (s : ℝ)
    (x : Pt 2) : Pt 2 :=
  eField (cf.coef w.1 s) (x - w.2)

/-- The time derivative `∂ₛ b_ω`. -/
def bDot {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) (w : BlockParam L) (s : ℝ)
    (x : Pt 2) : Pt 2 :=
  eField (deriv (cf.coef w.1) s) (x - w.2)

/-- The damped response
`B_{μ,ω}(s) = b_ω(s) - μ ∫₀ˢ e^{-μ(s-r)} b_ω(r) dr` (Definition 2.15). -/
def dampedB {L M : ℕ} {S : ℕ → ℝ} (cf : ControlFamily L M S) (μ : ℝ) (w : BlockParam L)
    (s : ℝ) (x : Pt 2) : Pt 2 :=
  bField cf w s x - μ • ∫ r in (0 : ℝ)..s, Real.exp (-μ * (s - r)) • bField cf w r x


end AnomDiss
