module

public import RequestProject.ScalarGlobalC2Bridge
public import RequestProject.ScalarMildGradient

/-!
# Time equation of the actual scalar mild fixed point

Spatial regularity of the flux derivatives allows the original Gaussian
integral equation to be differentiated on the closed time interval. Neither
time differentiability nor a PDE equation for the solution is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

theorem hasDerivWithinAt_duhamelComponent_of_flux_derivative_holder
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hβ : 0 < β)
    {F : ℝ → Pt 2 → ℂ} (i : Fin 2)
    (hF : Continuous (Function.uncurry (fun s x => pd i (F s) x)))
    (hFs : ∀ s, ContDiff ℝ 1 (F s)) (hp : ∀ s, IsPeriodic (F s))
    {C H : ℝ} (hC : ∀ s x, ‖pd i (F s) x‖ ≤ C) (hH : 0 ≤ H)
    (hholder : ∀ s x y, ‖pd i (F s) x - pd i (F s) y‖ ≤ H * ‖x - y‖ ^ β)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Pt 2) :
    HasDerivWithinAt (fun s => duhamelComponent ν F i s x)
      (ν • lap (duhamelComponent ν F i t) x + pd i (F t) x) (Icc 0 T) t := by
  have hperiodic : ∀ s, IsPeriodic (pd i (F s)) := fun s => isPeriodic_pd (F s) (hp s) i
  have he (s : ℝ) (hs : 0 ≤ s) :
      duhamelComponent ν F i s = heatDuhamel ν (fun r => pd i (F r)) s :=
    funext (duhamelComponent_eq_heatDuhamel_pd hν hFs hp hs i)
  have hd := hasDerivWithinAt_heatDuhamel_Icc hν hF hperiodic hC hH hβ hholder hT ht x
  rw [← he t ht.1] at hd
  exact hd.congr_of_mem (fun s hs => congrFun (he s hs.1) x) ht

/-- The fixed point satisfies the actual divergence-form parabolic equation,
with one-sided time derivatives at both endpoints. -/
theorem scalar_mild_fixedPoint_hasDerivWithinAt_of_flux_derivative_holder
    {ν T β : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hβ : 0 < β)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ)
    {u : SlabScalar T} (hu : scalarMildMap hν hT b f u = u)
    (hfc : ContDiff ℝ 2 (f : Pt 2 → ℂ)) (hfper : IsPeriodic f)
    (hflux : ∀ i : Fin 2,
      let G := extendSlabScalar hT (b i * u)
      Continuous (Function.uncurry (fun s x => pd i (G s) x)) ∧
      (∀ s, ContDiff ℝ 1 (G s)) ∧
      (∀ s, IsPeriodic (G s)) ∧
      (∃ C, ∀ s x, ‖pd i (G s) x‖ ≤ C) ∧
      (∃ H, 0 ≤ H ∧ ∀ s x y,
        ‖pd i (G s) x - pd i (G s) y‖ ≤ H * ‖x - y‖ ^ β))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Pt 2) :
    HasDerivWithinAt (fun s => extendSlabScalar hT u s x)
      (ν • lap (extendSlabScalar hT u t) x -
        ∑ i : Fin 2, pd i (extendSlabScalar hT (b i * u) t) x) (Icc 0 T) t := by
  let A : ℝ → Pt 2 → ℂ := fun s => heatOp (Real.toNNReal (2 * ν * s)) f
  let D : Fin 2 → ℝ → Pt 2 → ℂ := fun i =>
    duhamelComponent ν (extendSlabScalar hT (b i * u)) i
  have he : ∀ s ∈ Icc 0 T, extendSlabScalar hT u s =
      fun y => A s y - D 0 s y - D 1 s y := by
    intro s hs
    funext y
    rw [extendSlabScalar_of_mem hT u hs]
    have hh := congrArg (fun w : SlabScalar T => w (⟨s, hs⟩, y)) hu
    simpa [scalarMildMap, A, D, Fin.sum_univ_two, sub_add_eq_sub_sub] using hh.symm
  have hDs : ∀ i, ContDiff ℝ 2 (D i t) := by
    intro i
    obtain ⟨hc, hs, hp, ⟨C, hC⟩, ⟨H, hH, hholder⟩⟩ := hflux i
    exact contDiff_two_duhamelComponent_of_flux_derivative_holder hν i hc hs hp hC hH
      hβ hholder ht.1
  have hAs : ContDiff ℝ 2 (A t) := by
    rcases ht.1.eq_or_lt with h | h
    · have he0 : A t = f := by
        funext y
        simp [A, ← h, heatOp_zero f.continuous]
      rw [he0]
      exact hfc
    · exact contDiff_two_heatOp_continuous_periodic f.continuous hfper (by
        rw [Real.coe_toNNReal _ (by positivity)]
        positivity)
  have hlap : lap (extendSlabScalar hT u t) x = lap (A t) x -
      lap (D 0 t) x - lap (D 1 t) x := by
    rw [he t ht, lap_sub_fun _ _ (hAs.sub (hDs 0)) (hDs 1),
      lap_sub_fun _ _ hAs (hDs 0)]
  have hDd : ∀ i : Fin 2, HasDerivWithinAt (fun s => D i s x)
      (ν • lap (D i t) x + pd i (extendSlabScalar hT (b i * u) t) x) (Icc 0 T) t := by
    intro i
    obtain ⟨hc, hs, hp, ⟨C, hC⟩, ⟨H, hH, hholder⟩⟩ := hflux i
    exact hasDerivWithinAt_duhamelComponent_of_flux_derivative_holder hν hT hβ i hc hs hp
      hC hH hholder ht x
  have hd := ((hasDerivWithinAt_heatOp_Icc hfc hfper hν.le ht x).sub (hDd 0)).sub (hDd 1)
  apply (hd.congr_of_mem (fun s hs => congrFun (he s hs) x) ht).congr_deriv
  rw [hlap, Fin.sum_univ_two, smul_sub, smul_sub]
  abel

end AnomDiss
