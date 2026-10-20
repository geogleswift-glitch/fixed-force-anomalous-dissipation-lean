module

public import RequestProject.NSFiniteGalerkinCore
public import RequestProject.NSGalerkinTests

/-!
# Calculus and estimates for actual finite Galerkin state curves

This module applies the spatial calculations to the genuine finite-dimensional
`L²` state space. Time derivatives of the curl are consequences of the state
ODE. The bounds use the original force in the tested equation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff InnerProductSpace

noncomputable section

namespace AnomDiss.FiniteSolenoidalSpace

set_option maxHeartbeats 800000

variable (G : FiniteSolenoidalSpace)

theorem continuous_eval : Continuous (fun q : G.State × Pt 2 => G.eval q.1 q.2) :=
  ns_finite_linear_evaluation_continuous G.eval (fun v => (G.eval_contDiff v).continuous)

theorem continuous_partial_eval (j : Fin 2) :
    Continuous (fun q : G.State × Pt 2 => pd j (G.eval q.1) q.2) :=
  ns_partial_evaluation_continuous G.eval (fun v => (G.eval_contDiff v).of_le (by decide)) j

theorem continuous_curl_eval :
    Continuous (fun q : G.State × Pt 2 => curl2 (G.eval q.1) q.2) :=
  ns_curl_evaluation_continuous G.eval (fun v => (G.eval_contDiff v).of_le (by decide))

theorem continuous_laplacian_eval :
    Continuous (fun q : G.State × Pt 2 => lap (G.eval q.1) q.2) :=
  ns_laplacian_evaluation_continuous G.eval (fun v => (G.eval_contDiff v).of_le (by decide))

theorem hasDerivAt_curl_eval {u : ℝ → G.State} {u' : G.State} {t : ℝ}
    (hu : HasDerivAt u u' t) (x : Pt 2) :
    HasDerivAt (fun s => curl2 (G.eval (u s)) x) (curl2 (G.eval u') x) t :=
  ns_hasDerivAt_curl_evaluation G.eval
    (fun v => (G.eval_contDiff v).differentiable (by simp)) hu x

theorem hasDerivAt_laplacian_eval {u : ℝ → G.State} {u' : G.State} {t : ℝ}
    (hu : HasDerivAt u u' t) (x : Pt 2) :
    HasDerivAt (fun s => lap (G.eval (u s)) x) (lap (G.eval u') x) t :=
  ns_hasDerivAt_laplacian_evaluation G.eval
    (fun v => (G.eval_contDiff v).of_le (by decide)) hu x

private theorem curve_pair_continuousOn {a b : ℝ} {u : ℝ → G.State}
    (hu : ContinuousOn u (Icc a b)) :
    ContinuousOn (fun q : ℝ × Pt 2 => (u q.1, q.2)) (Icc a b ×ˢ univ) :=
  (hu.comp continuousOn_fst (fun _ h => h.1)).prodMk continuousOn_snd

theorem continuousOn_eval_curve {a b : ℝ} {u : ℝ → G.State}
    (hu : ContinuousOn u (Icc a b)) :
    ContinuousOn (fun q : ℝ × Pt 2 => G.eval (u q.1) q.2) (Icc a b ×ˢ univ) :=
  G.continuous_eval.comp_continuousOn (G.curve_pair_continuousOn hu)

theorem continuousOn_curl_curve {a b : ℝ} {u : ℝ → G.State}
    (hu : ContinuousOn u (Icc a b)) :
    ContinuousOn (fun q : ℝ × Pt 2 => curl2 (G.eval (u q.1)) q.2) (Icc a b ×ˢ univ) :=
  G.continuous_curl_eval.comp_continuousOn (G.curve_pair_continuousOn hu)

theorem continuousOn_laplacian_curve {a b : ℝ} {u : ℝ → G.State}
    (hu : ContinuousOn u (Icc a b)) :
    ContinuousOn (fun q : ℝ × Pt 2 => lap (G.eval (u q.1)) q.2) (Icc a b ×ˢ univ) := by
  let H : G.State × Pt 2 → Pt 2 := fun q => lap (G.eval q.1) q.2
  have hH : Continuous H := G.continuous_laplacian_eval
  have hpair : ContinuousOn (fun q : ℝ × Pt 2 => (u q.1, q.2)) (Icc a b ×ˢ univ) :=
    G.curve_pair_continuousOn hu
  have hcomp := hH.comp_continuousOn hpair
  change ContinuousOn (fun q : ℝ × Pt 2 => lap (G.eval (u q.1)) q.2)
    (Icc a b ×ˢ univ) at hcomp
  exact hcomp

/-- The tested finite-dimensional equation supplies both energy identities.
Laplacian invariance is supplied by the actual Fourier subspace. -/
theorem curve_tests (ν : ℝ) (u u' : G.State) (g : Pt 2 → Pt 2)
    (hlap : ∀ v : G.State, lap (G.eval v) ∈ G.space)
    (hweak : ∀ w : G.State,
      cellVectorPair (G.eval w) (G.eval u') +
          cellVectorPair (G.eval w) (conv (G.eval u) (G.eval u)) =
        ν * cellVectorPair (G.eval w) (lap (G.eval u)) + cellVectorPair (G.eval w) g) :
    ((∫ x in cell 2, dot (G.eval u x) (G.eval u' x)) +
      ν * (∫ x in cell 2, gradSqV (G.eval u) x) =
        (∫ x in cell 2, dot (G.eval u x) (g x))) ∧
    (-(∫ x in cell 2, dot (lap (G.eval u) x) (G.eval u' x)) +
      ν * l2sqV (lap (G.eval u)) = -(∫ x in cell 2, dot (lap (G.eval u) x) (g x))) := by
  refine ns_galerkin_tests G.space ν (G.eval u) (G.eval u') g
    ((G.eval_contDiff u).of_le (by decide)) (G.eval_periodic u) (G.eval_solenoidal u)
    u.2 (hlap u) ?_
  intro w hw
  exact hweak ⟨w, hw⟩

/-- The spatial energy bound for the true finite-dimensional curve. -/
theorem curve_energy_bound {a b ν : ℝ} (hab : a ≤ b) (hν : 0 < ν)
    (u u' : ℝ → G.State) (g : ℝ → Pt 2 → Pt 2)
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hg : ContinuousOn (fun q : ℝ × Pt 2 => g q.1 q.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt u (u' s) s)
    (htest : ∀ s ∈ Ioo a b,
      (∫ x in cell 2, dot (G.eval (u s) x) (G.eval (u' s) x)) +
          ν * (∫ x in cell 2, gradSqV (G.eval (u s)) x) =
        (∫ x in cell 2, dot (G.eval (u s) x) (g s x))) :
    ∀ t ∈ Icc a b, l2sqV (G.eval (u t)) ≤
      (l2sqV (G.eval (u a)) + ∫ s in a..b, l2sqV (g s)) * exp (b - a) :=
  ns_galerkin_energy_bound hab hν (fun s => G.eval (u s)) (fun s => G.eval (u' s)) g
    (G.continuousOn_eval_curve hu) (G.continuousOn_eval_curve hu') hg
    (fun s hs x => G.hasDerivAt_eval (hd s hs) x) htest

/-- Uniform `H¹` and integrated `H²` bounds for actual finite-state curves,
with their vorticity time derivative derived from the coefficient ODE. -/
theorem curve_enstrophy_bound {a b ν : ℝ} (hab : a ≤ b) (hν : 0 < ν)
    (u u' : ℝ → G.State) (g : ℝ → Pt 2 → Pt 2)
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hg : ContinuousOn (fun q : ℝ × Pt 2 => g q.1 q.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt u (u' s) s)
    (htest : ∀ s ∈ Ioo a b,
      -(∫ x in cell 2, dot (lap (G.eval (u s)) x) (G.eval (u' s) x)) +
          ν * l2sqV (lap (G.eval (u s))) =
        -(∫ x in cell 2, dot (lap (G.eval (u s)) x) (g s x))) :
    (∀ t ∈ Icc a b,
      (∫ x in cell 2, gradSqV (G.eval (u t)) x) +
          ν * (∫ s in a..t, l2sqV (lap (G.eval (u s)))) ≤
        (∫ x in cell 2, gradSqV (G.eval (u a)) x) +
          (1 / ν) * (∫ s in a..t, l2sqV (g s))) ∧
    (∀ t ∈ Icc a b,
      (∫ x in cell 2, gradSqV (G.eval (u t)) x) ≤
        (∫ x in cell 2, gradSqV (G.eval (u a)) x) +
          (1 / ν) * (∫ s in a..b, l2sqV (g s))) ∧
    ν * (∫ s in a..b, l2sqV (lap (G.eval (u s)))) ≤
      (∫ x in cell 2, gradSqV (G.eval (u a)) x) +
        (1 / ν) * (∫ s in a..b, l2sqV (g s)) :=
  ns_galerkin_enstrophy_bound hab hν (fun s => G.eval (u s)) (fun s => G.eval (u' s)) g
    (G.continuousOn_curl_curve hu) (G.continuousOn_curl_curve hu')
    (G.continuousOn_laplacian_curve hu) hg
    (fun s _ => ⟨(G.eval_contDiff (u s)).of_le (by decide), G.eval_periodic (u s),
      G.eval_solenoidal (u s), (G.eval_contDiff (u' s)).of_le (by decide), G.eval_periodic (u' s)⟩)
    (fun s hs x => G.hasDerivAt_curl_eval (hd s hs) x) htest

end AnomDiss.FiniteSolenoidalSpace
