module

public import RequestProject.Transfer

/-!
# Section 6: uniform velocity bounds
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- The scalar vorticity `curl v = ∂₁v₂ - ∂₂v₁` (indices `0,1` in Lean). -/
def curl2 (v : Pt 2 → Pt 2) (x : Pt 2) : ℝ := pd 0 v x 1 - pd 1 v x 0

/- **Lemma 6.1** (two-dimensional interpolation) is stated and proved as
`two_dimensional_interpolation` in `RequestProject/Interpolation.lean`. -/

/- **Proposition 6.2** (uniform horizontal bound) is stated and proved as
`uniform_horizontal_bound` in `RequestProject/UniformBound.lean`; its proof uses Lemma 6.1 and the
vorticity `L⁴` estimates, which are developed in files importing this one. -/

end AnomDiss
