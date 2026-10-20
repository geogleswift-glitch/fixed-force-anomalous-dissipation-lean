module

public import Mathlib

/-!
# Fixed-force anomalous dissipation for three-dimensional Navier–Stokes

Authors: Tao Tao, Baishu Zeng and Haiqi Zhang.

This independent statement surface represents the unit torus by periodic lifts
on real coordinate space, with normalized Lebesgue measure on the unit cell.
For every error tolerance in (0,1), one smooth initial datum and one force work
for a strictly decreasing sequence of positive viscosities tending to zero.
The same classical velocity and pressure witnesses have every indicated
Hölder exponent in (0,1), a common velocity bound, and the stated positive
viscous dissipation. No PDE existence or regularity theorem is a premise.

The transparent definitions below are the exact mathematical definitions used
by the proof library. This file deliberately imports only Mathlib. Its single
proof hole is the advertised challenge; Solution supplies the actual proof in
a separate environment and Comparator checks the statement and its complete
definition dependency closure.
-/
@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- Points of the lift `ℝ^d` of the torus `𝕋^d`. -/
abbrev Pt (d : ℕ) := Fin d → ℝ

/-- The integer vector `n ∈ ℤ^d` viewed as a point of `ℝ^d`. -/
def intVec {d : ℕ} (n : Fin d → ℤ) : Pt d := fun i => (n i : ℝ)

/-- A function on `ℝ^d` is `ℤ^d`-periodic, i.e. it is a function on the torus `𝕋^d`. -/
def IsPeriodic {d : ℕ} {α : Type*} (h : Pt d → α) : Prop :=
  ∀ (x : Pt d) (n : Fin d → ℤ), h (x + intVec n) = h x

/-- The unit cell `[0,1]^d`; integrating over it is integrating against normalized Lebesgue
measure on the torus. -/
def cell (d : ℕ) : Set (Pt d) := Icc 0 1

/-- Euclidean inner product on `ℝ^d`. -/
def dot {d : ℕ} (u v : Pt d) : ℝ := ∑ i, u i * v i

/-- Euclidean norm on `ℝ^d`. -/
def euclNorm {d : ℕ} (v : Pt d) : ℝ := Real.sqrt (∑ i, v i ^ 2)

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial derivative `∂_i h (x)`. -/
def pd (i : Fin d) (h : Pt d → E) (x : Pt d) : E := fderiv ℝ h x (Pi.single i 1)

/-- Divergence of a vector field. -/
def divergence (v : Pt d → Pt d) (x : Pt d) : ℝ := ∑ i, pd i v x i

/-- Laplacian. -/
def lap (h : Pt d → E) (x : Pt d) : E := ∑ i, pd i (pd i h) x

/-- Convective derivative `(u · ∇) h`. -/
def conv (u : Pt d → Pt d) (h : Pt d → E) (x : Pt d) : E := ∑ j, u x j • pd j h x

/-- Gradient of a scalar function. -/
def grad (p : Pt d → ℝ) (x : Pt d) : Pt d := fun i => pd i p x

/-- `|∇h|²` for a scalar function. -/
def gradSq (h : Pt d → ℝ) (x : Pt d) : ℝ := ∑ i, pd i h x ^ 2

/-- `|∇v|²` (squared Frobenius norm) for a vector field. -/
def gradSqV (v : Pt d → Pt d) (x : Pt d) : ℝ := ∑ i, ∑ k, pd i v x k ^ 2

/-- Squared `L²(𝕋^d)` norm of a scalar function. -/
def l2sq (h : Pt d → ℝ) : ℝ := ∫ x in cell d, h x ^ 2

/-- Squared `L²(𝕋^d)` norm of a vector field. -/
def l2sqV (v : Pt d → Pt d) : ℝ := ∫ x in cell d, ∑ k, v x k ^ 2

/-- Time derivative on `[0,T]` (one-sided at the endpoints). -/
def dt (T : ℝ) (u : ℝ → Pt d → E) (t : ℝ) (x : Pt d) : E :=
  derivWithin (fun s => u s x) (Icc 0 T) t

/-- Scalar dissipation `D^ν_θ(t) = ν ∫_0^t ‖∇θ(s)‖₂² ds` (Definition 1.4). -/
def dissipation (ν : ℝ) (θ : ℝ → Pt d → ℝ) (t : ℝ) : ℝ :=
  ν * ∫ s in (0 : ℝ)..t, ∫ x in cell d, gradSq (θ s) x

/-! ### Hölder spaces -/

/-- The `C^α` norm (sup norm plus `α`-Hölder seminorm), valued in `[0,∞]`. -/
def holderNorm (α : ℝ) (h : Pt d → E) : ℝ≥0∞ :=
  (⨆ x, ‖h x‖ₑ) + ⨆ x, ⨆ y, ‖h x - h y‖ₑ / ‖x - y‖ₑ ^ α

/-- Project encoding of a `C^∞` map from `ℝ` into the Banach space `C^α`: there are iterated
derivatives `D r`, each `D r t` has finite `C^α` norm, and `D (r+1)` is the derivative of `D r`
in the `C^α` norm. Continuity of every Banach-valued derivative is not separately required by
this predicate, so release documentation must not silently identify it with the full textbook
Banach-valued `C^∞` definition. -/
def IsSmoothHolderValued (α : ℝ) (f : ℝ → Pt d → E) : Prop :=
  ∃ D : ℕ → ℝ → Pt d → E, D 0 = f ∧ (∀ r t, holderNorm α (D r t) < ⊤) ∧
    ∀ r t, Tendsto (fun h : ℝ => holderNorm α (h⁻¹ • (D r (t + h) - D r t) - D (r + 1) t))
      (𝓝[≠] 0) (𝓝 0)

/-- A force which is smooth in time with values in every `C^α_σ(𝕋^d)`, `0 < α < 1`.
(Each time slice is moreover required to be a smooth divergence-free periodic field.) -/
structure IsTimeSmoothForce (f : ℝ → Pt d → Pt d) : Prop where
  periodic : ∀ t, IsPeriodic (f t)
  smooth_slice : ∀ t, ContDiff ℝ ∞ (f t)
  div_free : ∀ t x, divergence (f t) x = 0
  smooth_holder : ∀ α, 0 < α → α < 1 → IsSmoothHolderValued α f

/-- Project encoding of a force in `⋂_{0<α<1} C_c^∞((0,1); C^α_σ(𝕋^d))`.
The encoding additionally requires each time slice to be spatially `ContDiff ℝ ∞`; see
`IsSmoothHolderValued` for the precise time-valued regularity used here. -/
structure IsAdmissibleForce (f : ℝ → Pt d → Pt d) : Prop extends IsTimeSmoothForce f where
  compact_support : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ ∀ t, t ∉ Icc a b → f t = 0

/-! ### Parabolic Hölder spaces on `[0,T] × 𝕋^d` -/

/-- Parabolic `β`-Hölder continuity on `[0,T] × ℝ^d`. -/
def ParHolder (T β : ℝ) (g : ℝ → Pt d → E) : Prop :=
  ∃ C, ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x y,
    ‖g t x - g s y‖ ≤ C * (‖x - y‖ ^ β + |t - s| ^ (β / 2))

/-- `γ`-Hölder continuity in time, uniformly in space. -/
def TimeHolder (T γ : ℝ) (g : ℝ → Pt d → E) : Prop :=
  ∃ C, ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x, ‖g t x - g s x‖ ≤ C * |t - s| ^ γ

/-- Boundedness on `[0,T] × ℝ^d`. -/
def BddOn (T : ℝ) (g : ℝ → Pt d → E) : Prop :=
  ∃ C, ∀ t ∈ Icc 0 T, ∀ x, ‖g t x‖ ≤ C

/-- Membership in the parabolic Hölder space `C^{1+β/2, 2+β}([0,T] × 𝕋^d)`. -/
structure IsParabolicC12 (T β : ℝ) (u : ℝ → Pt d → E) : Prop where
  smooth_x : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (u t)
  diff_t : ∀ x, ∀ t ∈ Icc 0 T, DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t
  bdd : BddOn T u
  bdd_dt : BddOn T (dt T u)
  holder_dt : ParHolder T β (dt T u)
  bdd_d1 : ∀ i, BddOn T (fun t => pd i (u t))
  holder_d1_time : ∀ i, TimeHolder T ((1 + β) / 2) (fun t => pd i (u t))
  bdd_d2 : ∀ i j, BddOn T (fun t => pd i (pd j (u t)))
  holder_d2 : ∀ i j, ParHolder T β (fun t => pd i (pd j (u t)))

/-- Membership in the parabolic Hölder space `C^{β/2, 1+β}([0,T] × 𝕋^d)`. -/
structure IsParabolicC01 (T β : ℝ) (p : ℝ → Pt d → E) : Prop where
  smooth_x : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (p t)
  bdd : BddOn T p
  holder_time : TimeHolder T (β / 2) p
  bdd_d1 : ∀ i, BddOn T (fun t => pd i (p t))
  holder_d1 : ∀ i, ParHolder T β (fun t => pd i (p t))

/-- Membership in the Hölder space `C^{2+β}(𝕋^d)`. -/
def IsHolderC2 (β : ℝ) (h : Pt d → E) : Prop :=
  ContDiff ℝ 2 h ∧ ∃ C, ∀ i j x y, ‖pd i (pd j h) x - pd i (pd j h) y‖ ≤ C * ‖x - y‖ ^ β

/-! ### Classical solutions -/

/-- Definition 1.3: a classical solution `(u,p)` on `[0,T] × 𝕋^d` of the forced Navier–Stokes
system `∂ₜu + u·∇u + ∇p = νΔu + f`, `div u = 0`, `u(0) = u₀`. -/
structure IsClassicalNS (T ν : ℝ) (u₀ : Pt d → Pt d) (f : ℝ → Pt d → Pt d)
    (u : ℝ → Pt d → Pt d) (p : ℝ → Pt d → ℝ) : Prop where
  periodic_u : ∀ t ∈ Icc 0 T, IsPeriodic (u t)
  periodic_p : ∀ t ∈ Icc 0 T, IsPeriodic (p t)
  regular : ∃ β, 0 < β ∧ β < 1 ∧ IsParabolicC12 T β u ∧ IsParabolicC01 T β p
  init : u 0 = u₀
  div_free : ∀ t ∈ Icc 0 T, ∀ x, divergence (u t) x = 0
  eqn : ∀ t ∈ Icc 0 T, ∀ x,
    dt T u t x + conv (u t) (u t) x + grad (p t) x = ν • lap (u t) x + f t x

/-- The fixed-force construction on the normalized three-dimensional torus.
The initial datum and force are independent of the viscosity index; all
parabolic Hölder exponents hold for the same velocity and pressure witnesses. -/
theorem fixed_force_anomalous_dissipation (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ (u₀ : Pt 3 → Pt 3) (f : ℝ → Pt 3 → Pt 3) (ν : ℕ → ℝ),
      ContDiff ℝ ∞ u₀ ∧ IsPeriodic u₀ ∧ (∀ x, divergence u₀ x = 0) ∧ l2sqV u₀ = 1 ∧
      IsAdmissibleForce f ∧ (∀ m, 0 < ν m) ∧ StrictAnti ν ∧ Tendsto ν atTop (𝓝 0) ∧
      ∃ (u : ℕ → ℝ → Pt 3 → Pt 3) (p : ℕ → ℝ → Pt 3 → ℝ),
        (∀ m, IsClassicalNS 1 (ν m) u₀ f (u m) (p m)) ∧
        (∀ m β, 0 < β → β < 1 →
          IsParabolicC12 1 β (u m) ∧ IsParabolicC01 1 β (p m)) ∧
        (∃ C, ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u m t x‖ ≤ C) ∧
        ∀ m, (1 - ε) / 2 ≤ ν m * ∫ t in (0 : ℝ)..1, ∫ x in cell 3, gradSqV (u m t) x := by
  sorry

end AnomDiss
