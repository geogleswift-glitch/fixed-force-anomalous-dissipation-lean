module

public import RequestProject.HeatDuhamelTime
public import RequestProject.RightDerivativePrimitive
public import RequestProject.ScalarDuhamelGradientContinuity

/-!
# The inhomogeneous heat equation on closed time slabs

Spatial Hölder cancellation gives a continuous Hessian of the actual Duhamel
term. Its right time derivative then extends to the classical one-sided
derivative on the whole closed slab, including the terminal endpoint.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

theorem continuousOn_pd2_heatDuhamel_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    (i j : Fin 2) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × Pt 2 => pd i (pd j (heatDuhamel ν F p.1)) p.2)
      {p | p.1 ∈ Icc (0 : ℝ) T} := by
  have hc := (continuousOn_fderiv_duhamelComponent_holder
    hν hF hp hC hH hβ hholder j hT).clm_apply
      (continuousOn_const : ContinuousOn (fun _ : ℝ × Pt 2 => Pi.single i (1 : ℝ))
        {p | p.1 ∈ Icc (0 : ℝ) T})
  apply hc.congr
  intro p hp'
  have he : pd j (heatDuhamel ν F p.1) = duhamelComponent ν F j p.1 :=
    funext (pd_heatDuhamel_eq_duhamelComponent hν hF hp hC hp'.1 j)
  change pd i (pd j (heatDuhamel ν F p.1)) p.2 = pd i (duhamelComponent ν F j p.1) p.2
  rw [he]

theorem continuousOn_lap_heatDuhamel_holder {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × Pt 2 => lap (heatDuhamel ν F p.1) p.2)
      {p | p.1 ∈ Icc (0 : ℝ) T} :=
  continuousOn_finset_sum _ fun i _ =>
    continuousOn_pd2_heatDuhamel_holder hν hF hp hC hH hβ hholder i i hT

set_option diagnostics true in
set_option maxHeartbeats 200000 in
/-- Actual time differentiability on the full closed slab; source time differentiability is absent. -/
theorem hasDerivWithinAt_heatDuhamel_Icc {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) (x : Pt 2) :
    HasDerivWithinAt (fun s => heatDuhamel ν F s x)
      (ν • lap (heatDuhamel ν F t) x + F t x) (Icc 0 T) t := by
  let U : ℝ → ℂ := fun s => heatDuhamel ν F s x
  let R : ℝ → ℂ := fun s => ν • lap (heatDuhamel ν F s) x + F s x
  run_tac Lean.logInfo "stage: definitions"
  have hmap : Continuous (fun s : ℝ => (s, x)) := continuous_id.prodMk continuous_const
  have hmaps : MapsTo (fun s : ℝ => (s, x)) (Icc 0 T)
      {p : ℝ × Pt 2 | p.1 ∈ Icc (0 : ℝ) T} := fun s hs => hs
  run_tac Lean.logInfo "stage: time embedding"
  have hlap : ContinuousOn (fun p : ℝ × Pt 2 => lap (heatDuhamel ν F p.1) p.2)
      {p : ℝ × Pt 2 | p.1 ∈ Icc (0 : ℝ) T} :=
    continuousOn_lap_heatDuhamel_holder (F := F) (β := β) hν hF hp hC hH hβ hholder hT
  run_tac Lean.logInfo "stage: Hessian continuity"
  have hl : ContinuousOn (fun s => lap (heatDuhamel ν F s) x) (Icc (0 : ℝ) T) :=
    ContinuousOn.comp' (f := fun s : ℝ => (s, x)) hlap hmap.continuousOn hmaps
  run_tac Lean.logInfo "stage: restricted Laplacian continuity"
  have hFs : Continuous (fun s => F s x) := hF.comp hmap
  have hdcont : ContinuousOn R
      (Icc (0 : ℝ) T) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => ν) (Icc (0 : ℝ) T)).smul hl).add
      hFs.continuousOn
  run_tac Lean.logInfo "stage: right-hand side continuity"
  have hc : Continuous U := (continuous_heatDuhamel ν hF hC).comp hmap
  have hright (s : ℝ) (hs : s ∈ Ico 0 T) : HasDerivWithinAt U (R s) (Ici s) s :=
    hasDerivWithinAt_heatDuhamel_right hν hF hp hC hH hβ hholder hs.1 x
  run_tac Lean.logInfo "stage: right derivative"
  exact hasDerivWithinAt_Icc_of_continuous_right_derivative_on
    (f := U) (f' := R) (T := T) (t := t) hT hc.continuousOn hdcont hright ht

/-- The genuine ordinary-source Duhamel term satisfies `∂ₜU = νΔU + F` using `dt`. -/
theorem dt_heatDuhamel_Icc {ν β : ℝ} (hν : 0 < ν)
    {F : ℝ → Pt 2 → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ s, IsPeriodic (F s)) {C H : ℝ} (hC : ∀ s x, ‖F s x‖ ≤ C)
    (hH : 0 ≤ H) (hβ : 0 < β)
    (hholder : ∀ s x y, ‖F s x - F s y‖ ≤ H * ‖x - y‖ ^ β)
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T) (x : Pt 2) :
    dt T (heatDuhamel ν F) t x = ν • lap (heatDuhamel ν F t) x + F t x :=
  (hasDerivWithinAt_heatDuhamel_Icc hν hF hp hC hH hβ hholder hT.le ht x).derivWithin
    (uniqueDiffOn_Icc hT t ht)

end AnomDiss
