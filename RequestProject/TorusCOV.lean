module

public import RequestProject.H2Dens

/-!
# Area-preserving changes of variables on the torus

If `ψ` is a `C¹` lift of a torus diffeomorphism with Jacobian determinant `1`, then
`∫_{𝕋²} φ ∘ ψ = ∫_{𝕋²} φ` for every periodic `φ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace AnomDiss

/-- The integer lattice `ℤ² ⊂ ℝ²`. -/
def intLattice : AddSubgroup (Pt 2) :=
  AddMonoidHom.range (Pi.addMonoidHom fun i => (Int.castAddHom ℝ).comp (Pi.evalAddMonoidHom _ i))

lemma mem_intLattice {v : Pt 2} : v ∈ intLattice ↔ ∃ m : Fin 2 → ℤ, intVec m = v := by
  unfold intLattice
  rw [AddMonoidHom.mem_range]
  rfl

instance : Countable intLattice := by
  have h : (intLattice : Set (Pt 2)) = Set.range (fun m : Fin 2 → ℤ => intVec m) := by
    ext v; simp only [SetLike.mem_coe, mem_intLattice, Set.mem_range]
  have : (intLattice : Set (Pt 2)).Countable := by rw [h]; exact Set.countable_range _
  exact this.to_subtype

/-- The half-open unit cell. -/
def cellIco : Set (Pt 2) := Set.pi univ fun _ => Ico (0 : ℝ) 1

lemma cellIco_ae_eq_cell : cellIco =ᵐ[volume] cell 2 := by
  unfold cellIco cell
  rw [volume_pi]
  exact Measure.univ_pi_Ico_ae_eq_Icc (f := fun _ => (0 : ℝ)) (g := fun _ => 1)

lemma isAddFundamentalDomain_cellIco :
    IsAddFundamentalDomain intLattice cellIco (volume : Measure (Pt 2)) := by
  refine IsAddFundamentalDomain.mk' (MeasurableSet.univ_pi fun _ =>
    measurableSet_Ico).nullMeasurableSet fun x => ?_
  refine ⟨⟨intVec fun i => -⌊x i⌋, mem_intLattice.2 ⟨_, rfl⟩⟩, ?_, ?_⟩
  · intro i _
    simp only [AddSubgroup.vadd_def, vadd_eq_add, Pi.add_apply, intVec, Int.cast_neg]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  · rintro ⟨g, hg⟩ hmem
    obtain ⟨m, rfl⟩ := mem_intLattice.1 hg
    ext i
    have h := hmem i (mem_univ i)
    simp only [AddSubgroup.vadd_def, vadd_eq_add, Pi.add_apply, intVec] at h
    simp only [intVec, Int.cast_neg]
    have : m i = -⌊x i⌋ := by
      have hf : ⌊x i⌋ = -m i := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [h.1, h.2]
      omega
    rw [this]; push_cast; ring

/-- **Area-preserving change of variables on the torus.** -/
theorem integral_cell_comp_lift {ψ ψi : Pt 2 → Pt 2} (hψ : ContDiff ℝ 1 ψ) (hψi : Continuous ψi)
    (hl : Function.LeftInverse ψi ψ) (hr : Function.RightInverse ψi ψ) (hlift : IsLift ψ)
    (hdet : ∀ x, (jac ψ x).det = 1) {φ : Pt 2 → ℝ} (hφp : IsPeriodic φ) :
    ∫ x in cell 2, φ (ψ x) = ∫ x in cell 2, φ x := by
  have hD := isAddFundamentalDomain_cellIco
  have hmeas : MeasurableSet cellIco :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  -- `ψi` is a lift
  have hliftI : ∀ x (m : Fin 2 → ℤ), ψi (intVec m + x) = intVec m + ψi x := by
    intro x m
    have : ψ (intVec m + ψi x) = intVec m + x := by
      rw [add_comm, hlift, hr x, add_comm]
    rw [← this, hl]
  -- `ψi` is quasi-measure-preserving
  have hqmp : Measure.QuasiMeasurePreserving ψi volume volume := by
    refine ⟨hψi.measurable, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
    rw [Measure.map_apply hψi.measurable hs]
    have himg : ψi ⁻¹' s = ψ '' s := (congrFun (Set.image_eq_preimage_of_inverse hl hr) s).symm
    rw [himg]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hψ.differentiable one_ne_zero).differentiableOn hs0
  have hD' : IsAddFundamentalDomain intLattice (ψi ⁻¹' cellIco) volume := by
    refine hD.preimage_of_equiv hqmp (e := id) Function.bijective_id fun g x => ?_
    obtain ⟨m, hm⟩ := mem_intLattice.1 g.2
    simp only [id, AddSubgroup.vadd_def, vadd_eq_add, ← hm]
    exact hliftI x m
  have hφg : ∀ (g : intLattice) x, φ (g +ᵥ x) = φ x := by
    intro g x
    obtain ⟨m, hm⟩ := mem_intLattice.1 g.2
    simp only [AddSubgroup.vadd_def, vadd_eq_add, ← hm]
    rw [add_comm, hφp]
  have hfd := hD'.setIntegral_eq hD hφg
  -- the change of variables
  have himg : ψ '' cellIco = ψi ⁻¹' cellIco :=
    congrFun (Set.image_eq_preimage_of_inverse hl hr) cellIco
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hmeas
    (fun x _ => ((hψ.differentiable one_ne_zero) x).hasFDerivAt.hasFDerivWithinAt)
    (hl.injective.injOn) φ
  have hdet' : ∀ x, (fderiv ℝ ψ x).det = 1 := fun x => by
    show LinearMap.det (fderiv ℝ ψ x : Pt 2 →ₗ[ℝ] Pt 2) = 1
    rw [← hdet x, ← LinearMap.det_toMatrix' (fderiv ℝ ψ x : Pt 2 →ₗ[ℝ] Pt 2)]
    congr 1
  simp only [hdet', abs_one, one_smul] at hcov
  rw [setIntegral_congr_set cellIco_ae_eq_cell.symm, setIntegral_congr_set cellIco_ae_eq_cell.symm,
    ← hcov, himg, hfd]

end AnomDiss
