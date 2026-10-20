module

public import RequestProject.Residue
public import RequestProject.ScalarStages

/-! # Reconstruction of the original vector parabolic class from components -/

@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff
noncomputable section
namespace AnomDiss

theorem isParabolicC12_vector_of_components {d : ℕ} {T β : ℝ}
    (hT : 0 < T) {v : ℝ → Pt d → Pt 2}
    (hv : ∀ i : Fin 2, IsParabolicC12 T β (fun t x => v t x i)) :
    IsParabolicC12 T β v := by
  let L (i : Fin 2) : ℝ →L[ℝ] Pt 2 := ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) i
  have h0 := (hv 0).clm hT (L 0)
  have h1 := (hv 1).clm hT (L 1)
  apply (h0.add hT h1).congr
  intro t ht
  funext x i
  fin_cases i <;> simp [L, ContinuousLinearMap.single_apply, Pi.single_apply]

theorem isParabolicC12_vector_of_complex_components {d : ℕ} {T β : ℝ}
    (hT : 0 < T) {v : ℝ → Pt d → Pt 2}
    (hv : ∀ i : Fin 2, IsParabolicC12 T β (fun t x => (v t x i : ℂ))) :
    IsParabolicC12 T β v := by
  apply isParabolicC12_vector_of_components hT
  intro i
  exact (hv i).clm hT Complex.reCLM

end AnomDiss
