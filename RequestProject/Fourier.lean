module

public import RequestProject.Controls
public import RequestProject.DampedResponse
public import RequestProject.TorusFourier
public import RequestProject.WeightedFourier
public import RequestProject.NonStationary

/-!
# Section 3: Fourier estimates for advection–diffusion

Quasi-periodic Fourier coefficients of torus diffeomorphisms (Definition 3.2), the semiclassical
observable lemma, the non-stationary phase bound, the weighted Fourier drift estimate
(Lemma 3.5), the cell problem and its Lie splitting (Definitions 3.6–3.7, Lemmas 3.8–3.10) and
the diffusive Fourier drift estimate (Proposition 3.11).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/- The coefficients `coeffC` (Definition 3.2), the weights `weightW` and the Parseval part of
**Lemma 3.3** (`coeff_parseval`) are in `RequestProject/SemiclassicalCore.lean`. -/

/-- **Lemma 3.3** (semiclassical observable), test function part: for `f ∈ C_c^∞(ℝ²)`,
`∑ₙ f((ξ+n)/ρ)|c_n^Ψ(ξ)|² = ∫_{𝕋²} f(DΨ(y)ᵀe) dy + O_f(ρ⁻¹)` for `ξ = ρe`, uniformly when
`‖D²Ψ‖_∞` is bounded. -/
theorem semiclassical_observable (f : Pt 2 → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (K : ℝ) : ∃ C : ℝ, ∀ Ψ : Pt 2 → Pt 2, ContDiff ℝ 2 Ψ → IsLift Ψ →
      (∀ y, ‖iteratedFDeriv ℝ 2 Ψ y‖ ≤ K) → ∀ e : Pt 2, euclNorm e = 1 → ∀ ρ : ℝ, 1 ≤ ρ →
      |(∑' n, f (ρ⁻¹ • (ρ • e + intVec n)) * ‖coeffC Ψ (ρ • e) n‖ ^ 2) -
        ∫ y in cell 2, f ((jac Ψ y)ᵀ *ᵥ e)| ≤ C / ρ := by
  obtain ⟨C, hC⟩ := semiclassical_core f hf hfc K
  refine ⟨C, fun Ψ hΨ hlift hK e he ρ hρ => ?_⟩
  simp only [coeffC_eq_fc_scPhase]
  exact hC Ψ hΨ hlift hK e he ρ hρ

/-- **Lemma 3.4** (non-stationary phase for low outputs).  If `|DΨ(y)ᵀe| ≥ 4a` and the
derivatives of `Ψ` up to order `J+1` are bounded, then
`∑_{|ξ+n| ≤ aρ} |c_n^Ψ(ξ)|² ≤ C_J ρ^{2-2J}`.  (The paper states this for `J ≥ 1`; the proof
works for every `J ≥ 0`, so that restriction is dropped.) -/
theorem nonstationary_low_output (a : ℝ) (ha : 0 < a) (K : ℕ → ℝ) (J : ℕ) :
    ∃ C : ℝ, ∀ Ψ : Pt 2 → Pt 2, ContDiff ℝ ∞ Ψ → IsLift Ψ →
      (∀ y, ∀ e : Pt 2, euclNorm e = 1 → 4 * a ≤ euclNorm ((jac Ψ y)ᵀ *ᵥ e)) →
      (∀ y, ∀ k, 1 ≤ k → k ≤ J + 1 → ‖iteratedFDeriv ℝ k Ψ y‖ ≤ K k) →
      ∀ e : Pt 2, euclNorm e = 1 → ∀ ρ : ℝ, 1 ≤ ρ →
      (∑' n, if euclNorm (ρ • e + intVec n) ≤ a * ρ then ‖coeffC Ψ (ρ • e) n‖ ^ 2 else 0)
        ≤ C * ρ ^ (2 - 2 * (J : ℝ)) :=
  nonstationary_low_output_core a ha K J

/-- **Lemma 3.5** (weighted Fourier estimate).  Let `Ψ` be a random smooth area-preserving
diffeomorphism of `𝕋²` isotopic to the identity, with uniform bounds `K a` on all positive-order
derivatives of `Ψ` and `Ψ⁻¹`, satisfying `sup_{|e|=1} 𝔼∫|DΨ(y)ᵀe|^{-σ} dy ≤ 1/(32 q^σ)`.  Then
there is `R₀ ≥ 1`, depending only on `q`, `σ` and the bounds, such that for `R ≥ R₀`, `k ≥ 1`
and `|ℓ| ≥ Rk`, `𝔼 ∑ₙ W_{qk}(ℓ + kn)|c_n^Ψ(ℓ/k)|² ≤ ½ W_k(ℓ)`. -/
theorem lemma_fourier (q : ℕ) (hq : 3 ≤ q) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (K : ℕ → ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω')
      [IsProbabilityMeasure P] (Ψ Ψinv : Ω' → Pt 2 → Pt 2),
      Measurable (Function.uncurry Ψ) →
      (∀ o, ContDiff ℝ ∞ (Ψ o) ∧ ContDiff ℝ ∞ (Ψinv o) ∧ IsLift (Ψ o) ∧
        Function.LeftInverse (Ψinv o) (Ψ o) ∧ Function.RightInverse (Ψinv o) (Ψ o) ∧
        ∀ y, (jac (Ψ o) y).det = 1) →
      (∀ o y, ∀ a, 1 ≤ a → ‖iteratedFDeriv ℝ a (Ψ o) y‖ ≤ K a ∧
        ‖iteratedFDeriv ℝ a (Ψinv o) y‖ ≤ K a) →
      (∀ e : Pt 2, euclNorm e = 1 →
        ∫ o, (∫ y in cell 2, euclNorm ((jac (Ψ o) y)ᵀ *ᵥ e) ^ (-σ)) ∂P ≤ 1 / (32 * (q : ℝ) ^ σ)) →
      ∀ R, R₀ ≤ R → ∀ k : ℕ, 1 ≤ k → ∀ ℓ : Fin 2 → ℤ, R * k ≤ euclNorm (intVec ℓ) →
        ∫ o, ∑' n, weightW σ R ((q : ℝ) * k) (intVec ℓ + (k : ℝ) • intVec n) *
            ‖coeffC (Ψ o) ((k : ℝ)⁻¹ • intVec ℓ) n‖ ^ 2 ∂P
          ≤ weightW σ R k (intVec ℓ) / 2 := by
  exact lemma_fourier_core q hq σ hσ0 hσ1 K

/-! ### Heat convolution and splitting (Section 3.2) -/

/-- A quasi-periodic classical solution on the unit time interval of the cell problem
`∂ₛh + B·∇h = (μ/4π²)Δh`, `h(0) = e_ξ` (Definition 3.6); `h(s,·)e_{-ξ}` is periodic. -/
structure IsCellSolution (B : ℝ → Pt 2 → Pt 2) (μ : ℝ) (ξ : Pt 2) (h : ℝ → Pt 2 → ℂ) :
    Prop where
  regular : ∃ β, 0 < β ∧ β < 1 ∧ IsParabolicC12 1 β h
  quasi_periodic : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y (n : Fin 2 → ℤ),
    h s (y + intVec n) = expChar ξ (intVec n) * h s y
  init : h 0 = expChar ξ
  eqn : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y,
    dt 1 h s y + conv (B s) (h s) y = (μ / (4 * π ^ 2)) • lap (h s) y

/-- The coefficients `a_m^{μ,ω}(ξ)` of the time-one output `T_{μ,ω}(e_ξ) = ∑ₘ aₘ e_{ξ+m}`. -/
def cellCoeff (h : ℝ → Pt 2 → ℂ) (ξ : Pt 2) (m : Fin 2 → ℤ) : ℂ :=
  ∫ y in cell 2, h 1 y * expChar (-(ξ + intVec m)) y

/-- `ψ` is the inverse flow map of `B` over `[t₀, t₁]`. -/
def IsInverseFlowMap (B : ℝ → Pt 2 → Pt 2) (t₀ t₁ : ℝ) (ψ : Pt 2 → Pt 2) : Prop :=
  ∃ Φ : ℝ → Pt 2 → Pt 2, (∀ x, Φ t₀ x = x) ∧
    (∀ s x, HasDerivAt (fun s => Φ s x) (B s (Φ s x)) s) ∧
    ∀ x, ψ (Φ t₁ x) = x ∧ Φ t₁ (ψ x) = x

/-- The centered Gaussian law on `ℝ²` with covariance `v I₂`. -/
def gauss2 (v : ℝ≥0) : Measure (Pt 2) := Measure.pi fun _ : Fin 2 => gaussianReal 0 v

/-- The heat semigroup `H_τ h(x) = 𝔼 h(x + ζ)`, `ζ ~ N(0, 2κτ I₂)`, written with the
variance `v = 2κτ`. -/
def heatOp (v : ℝ≥0) (h : Pt 2 → ℂ) (x : Pt 2) : ℂ := ∫ ζ, h (x + ζ) ∂(gauss2 v)

/-- The variance `2κa = 2 (μ/4π²)(1/n)` of a single heat step of the splitting. -/
def splitVar (μ : ℝ) (n : ℕ) : ℝ≥0 := Real.toNNReal (2 * (μ / (4 * π ^ 2)) / n)

/-- The Lie splitting operator `P_j = H_a U_j ⋯ H_a U_1`, `U_i h = h ∘ ψ_i` (Definition 3.7). -/
def splitOp (μ : ℝ) (n : ℕ) (ψ : ℕ → Pt 2 → Pt 2) : ℕ → (Pt 2 → ℂ) → Pt 2 → ℂ
  | 0, h => h
  | j + 1, h => heatOp (splitVar μ n) (splitOp μ n ψ j h ∘ ψ (j + 1))

/-- The random map `Ψ_j = f_1 ∘ ⋯ ∘ f_j`, `f_i(y) = ψ_i(y + ζ_i)`; for `j = n` this is the map
`x = X_n ↦ X_0` of Definition 3.7. -/
def splitMap (ψ : ℕ → Pt 2 → Pt 2) (ζ : ℕ → Pt 2) : ℕ → Pt 2 → Pt 2
  | 0 => id
  | j + 1 => splitMap ψ ζ j ∘ fun y => ψ (j + 1) (y + ζ (j + 1))

/-- The law of the Gaussian increments `(ζᵢ)ᵢ` (only `ζ_1, …, ζ_n` are used). -/
def gaussSeq (v : ℝ≥0) : Measure (ℕ → Pt 2) := Measure.infinitePi fun _ : ℕ => gauss2 v

/-- The inverse flow maps used in the splitting of `B_{μ,ω}` with `n` steps. -/
def IsSplitting (B : ℝ → Pt 2 → Pt 2) (n : ℕ) (ψ : ℕ → Pt 2 → Pt 2) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → IsInverseFlowMap B ((i - 1 : ℝ) / n) ((i : ℝ) / n) (ψ i)

/- **Lemma 3.8** (`split_representation`) is stated and proved in
`RequestProject/SplitRepFull.lean`, using the `C^∞` flow theory of `RequestProject/FlowSmoothMain.lean`
and the composition estimates of `RequestProject/CompBounds.lean`. -/

/- **Lemma 3.9** (`split_map_closeness`) is stated and proved in
`RequestProject/SplitSup.lean`. -/

/-- The `H²(𝕋²)` norm of a `C²` function. -/
def h2Norm (h : Pt 2 → ℂ) : ℝ :=
  Real.sqrt (∫ y in cell 2, (‖h y‖ ^ 2 + ∑ i, ‖pd i h y‖ ^ 2 + ∑ i, ∑ j, ‖pd i (pd j h) y‖ ^ 2))

/- **Lemma 3.10** (`split_convergence`) is stated and proved in
`RequestProject/SplitL2.lean`. -/

/- **Proposition 3.11** (`diffusive_fourier`) is stated and proved in
`RequestProject/DiffusiveFourier.lean`. -/

end AnomDiss
