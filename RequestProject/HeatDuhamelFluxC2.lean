module

public import RequestProject.HeatDuhamelClassical
public import RequestProject.HeatDuhamelDivergence

/-!
# A `C²` bridge for divergence-form Duhamel terms

The scalar mild equation is written with the spatial derivative of a heat Duhamel term.
The previously available estimates controlled that term as a `C¹` function.  When the flux
itself is `C¹` and its spatial derivative is Hölder, integration by parts identifies the term
with an ordinary-source Duhamel integral whose source is Hölder; the ordinary heat estimate then
gives a genuine `C²` spatial slice.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

/-- A divergence-form Duhamel component is `C²` when its flux derivative is Hölder. -/
theorem contDiff_two_duhamelComponent_of_flux_derivative_holder {ν β : ℝ}
    (hν : 0 < ν) {F : ℝ → Pt 2 → ℂ} (i : Fin 2)
    (hF : Continuous (Function.uncurry (fun s x => pd i (F s) x)))
    (hFs : ∀ s, ContDiff ℝ 1 (F s)) (hp : ∀ s, IsPeriodic (F s))
    {C H : ℝ} (hC : ∀ s x, ‖pd i (F s) x‖ ≤ C) (hH : 0 ≤ H)
    (hβ : 0 < β)
    (hholder : ∀ s x y, ‖pd i (F s) x - pd i (F s) y‖ ≤ H * ‖x - y‖ ^ β)
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ 2 (duhamelComponent ν F i t) := by
  have hsource : ∀ s, IsPeriodic (pd i (F s)) := fun s => isPeriodic_pd (F s) (hp s) i
  have heq : duhamelComponent ν F i t =
      heatDuhamel ν (fun s => pd i (F s)) t := by
    funext x
    exact duhamelComponent_eq_heatDuhamel_pd hν hFs hp ht i x
  rw [heq]
  exact contDiff_two_heatDuhamel_holder hν hF hsource hC hH hβ hholder ht

end AnomDiss
