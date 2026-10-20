module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Simultaneous uniform compactness of countably many coefficient curves

Arzelà--Ascoli gives a compact set of curves at each fixed coordinate. Their
countable product is sequentially compact. Initial coordinates before their
frequency is retained are harmless: clamping the sequence index at a fixed
coordinate threshold agrees with the actual sequence eventually.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped BoundedContinuousFunction NNReal

noncomputable section

namespace AnomDiss

/-- A countable family of uniformly bounded coefficient curves with an
eventual, coordinate-wise uniform Lipschitz constant has one subsequence that
converges uniformly at every coordinate. -/
theorem exists_countable_uniform_curve_subsequence
    {ι X : Type*} [Countable ι] [PseudoMetricSpace X] [CompactSpace X]
    (f : ℕ → ι → (X →ᵇ ℂ)) (R : ι → ℝ) (L : ι → ℝ≥0)
    (hb : ∀ n i x, ‖f n i x‖ ≤ R i)
    (hL : ∀ i, ∃ N : ℕ, ∀ n, N ≤ n → LipschitzWith (L i) (f n i)) :
    ∃ a : ι → (X →ᵇ ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun n => f (φ n) i) atTop (𝓝 (a i)) := by
  classical
  choose N hN using hL
  let g : ℕ → ι → (X →ᵇ ℂ) := fun n i => f (max n (N i)) i
  let K : ι → Set (X →ᵇ ℂ) := fun i => closure (range (fun n => g n i))
  have hgL (n : ℕ) (i : ι) : LipschitzWith (L i) (g n i) :=
    hN i (max n (N i)) (le_max_right _ _)
  have hK (i : ι) : IsCompact (K i) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) (R i))
      (isCompact_closedBall _ _) (range (fun n => g n i))
    · intro q x hq
      obtain ⟨n, rfl⟩ := hq
      simpa only [mem_closedBall, dist_zero_right] using hb (max n (N i)) i x
    · apply Metric.equicontinuous_of_continuity_modulus (fun r => (L i : ℝ) * r)
      · simpa only [id_eq, mul_zero] using
          (((continuous_const (y := (L i : ℝ))).fun_mul continuous_id).tendsto (0 : ℝ))
      · intro x y q
        obtain ⟨n, hn⟩ := q.2
        rw [← hn]
        exact (hgL n i).dist_le_mul x y
  have hprod : IsCompact {a : ι → (X →ᵇ ℂ) | ∀ i, a i ∈ K i} :=
    isCompact_pi_infinite hK
  obtain ⟨a, -, φ, hφ, hlim⟩ := hprod.tendsto_subseq (x := g)
    (fun n i => subset_closure (mem_range_self n))
  refine ⟨a, φ, hφ, fun i => ?_⟩
  have hlimi : Tendsto (fun n => g (φ n) i) atTop (𝓝 (a i)) :=
    (tendsto_pi_nhds.1 hlim) i
  have hlarge : ∀ᶠ n in atTop, N i ≤ φ n :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop (N i))
  have heq : (fun n => f (φ n) i) =ᶠ[atTop] fun n => g (φ n) i := by
    filter_upwards [hlarge] with n hn
    simp only [g, max_eq_left hn]
  exact (tendsto_congr' heq).2 hlimi

/-- The convergence above means uniform convergence on the entire compact
time domain, not merely pointwise convergence. -/
theorem bounded_curve_tendsto_uniform {X : Type*} [TopologicalSpace X]
    {f : ℕ → (X →ᵇ ℂ)} {a : X →ᵇ ℂ}
    (hf : Tendsto f atTop (𝓝 a)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, ‖f n x - a x‖ < ε := by
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 hf ε hε] with n hn
  intro x
  rw [← dist_eq_norm]
  exact (BoundedContinuousFunction.dist_coe_le_dist x).trans_lt hn

end AnomDiss
