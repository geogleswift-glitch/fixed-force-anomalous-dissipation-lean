module

public import RequestProject.Basic

/-!
# Fourier analysis on `𝕋²`

Characters, Fourier coefficients and Parseval's identity on the two-dimensional torus
(Definition 1.1), for continuous periodic functions represented on the unit cell.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- The character `e_ξ(y) = e^{2πi ξ·y}` (for `ξ ∈ ℝ²`; for `ξ ∈ ℤ²` this is `e_ℓ`). -/
def expChar (ξ : Pt 2) (y : Pt 2) : ℂ := Complex.exp (2 * π * Complex.I * (dot ξ y : ℂ))

/-- Fourier coefficient `ĥ(ℓ) = ∫_{𝕋²} h(x) e^{-2πiℓ·x} dx` (Definition 1.1). -/
def fc (h : Pt 2 → ℂ) (ℓ : Fin 2 → ℤ) : ℂ := ∫ x in cell 2, h x * expChar (-intVec ℓ) x

lemma expChar_add_right (ξ x c : Pt 2) : expChar ξ (x + c) = expChar ξ x * expChar ξ c := by
  unfold expChar
  rw [← Complex.exp_add]
  congr 1
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  push_cast; ring

lemma expChar_mul (ξ η x : Pt 2) : expChar ξ x * expChar η x = expChar (ξ + η) x := by
  unfold expChar
  rw [← Complex.exp_add]
  congr 1
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  push_cast; ring

lemma continuous_expChar (ξ : Pt 2) : Continuous (expChar ξ) := by
  unfold expChar dot
  fun_prop

lemma norm_expChar (ξ x : Pt 2) : ‖expChar ξ x‖ = 1 := by
  simp only [expChar, Complex.norm_exp]
  have : (2 * π * Complex.I * ((dot ξ x : ℝ) : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero]

lemma expChar_intVec_eq_prod (m : Fin 2 → ℤ) (x : Pt 2) :
    expChar (intVec m) x = ∏ i, Complex.exp (2 * π * Complex.I * m i * x i) := by
  rw [expChar, dot, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [intVec]; ring

lemma expChar_intVec_intVec (ℓ n : Fin 2 → ℤ) : expChar (intVec ℓ) (intVec n) = 1 := by
  rw [expChar_intVec_eq_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have : 2 * π * Complex.I * (ℓ i : ℂ) * ((intVec n i : ℝ) : ℂ) = ((ℓ i * n i : ℤ) : ℂ) * (2 * π * Complex.I) := by
    simp [intVec]; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma isPeriodic_expChar (ℓ : Fin 2 → ℤ) : IsPeriodic (expChar (intVec ℓ)) := fun x n => by
  rw [expChar_add_right, expChar_intVec_intVec, mul_one]

section TorusParseval

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The projection `ℝ² → 𝕋²`. -/
def torusProj (y : Pt 2) : UnitAddTorus (Fin 2) := fun i => (y i : UnitAddCircle)

lemma measurePreserving_torusProj :
    MeasurePreserving torusProj (volume.restrict (cell 2)) volume := by
  have hcell : cell 2 = Set.univ.pi (fun _ : Fin 2 => Icc (0:ℝ) 1) := by
    rw [cell, ← Set.pi_univ_Icc]; rfl
  have h1 : (volume : Measure (Pt 2)).restrict (cell 2) =
      Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ioc 0 (0 + 1))) := by
    rw [hcell, volume_pi, Measure.restrict_pi_pi]
    congr 1; funext i
    rw [zero_add]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  rw [h1]
  have hm : MeasurePreserving ((↑) : ℝ → UnitAddCircle) ((volume : Measure ℝ).restrict (Ioc 0 (0 + 1)))
      AddCircle.haarAddCircle := by
    have := UnitAddCircle.measurePreserving_mk 0
    rwa [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] at this
  exact measurePreserving_pi _ (fun _ => AddCircle.haarAddCircle) (fun _ => hm)


/-- Representative in `[0,1)` of a point of the unit circle. -/
noncomputable def circRep (x : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 0 x : ℝ)

lemma measurable_circRep : Measurable circRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

lemma circRep_mem (x : UnitAddCircle) : circRep x ∈ Icc (0:ℝ) 1 := by
  have : circRep x ∈ Ico (0:ℝ) (0 + 1) := (AddCircle.equivIco 1 0 x).2
  exact Ico_subset_Icc_self (by simpa using this)

lemma circRep_coe (y : ℝ) : ∃ n : ℤ, circRep (y : UnitAddCircle) = y + n := by
  have h : ((circRep (y : UnitAddCircle) : ℝ) : UnitAddCircle) = (y : UnitAddCircle) :=
    (AddCircle.equivIco 1 0).symm_apply_apply _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h)
  refine ⟨-k, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  push_cast; linarith


/-- The function on `𝕋²` induced by a function on `ℝ²` (via representatives in `[0,1)²`). -/
noncomputable def torusLift {α : Type*} (h : Pt 2 → α) (x : UnitAddTorus (Fin 2)) : α :=
  h (fun i => circRep (x i))

lemma torusLift_proj {α : Type*} (h : Pt 2 → α) (hp : IsPeriodic h) (y : Pt 2) :
    torusLift h (torusProj y) = h y := by
  choose n hn using fun i => circRep_coe (y i)
  have : (fun i => circRep (torusProj y i)) = y + intVec n := by
    funext i; simp [torusProj, hn i, intVec]
  rw [torusLift, this, hp]

lemma measurable_torusLift (h : Pt 2 → ℝ) (hc : Continuous h) : Measurable (torusLift h) :=
  hc.measurable.comp (Measurable.of_eval fun i => measurable_circRep.comp (measurable_pi_apply i))

lemma torusLift_bdd (h : Pt 2 → ℝ) (hc : Continuous h) : ∃ C, ∀ x, ‖torusLift h x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Pt 2)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨C, fun x => hC _ ⟨fun i => (circRep_mem (x i)).1, fun i => (circRep_mem (x i)).2⟩⟩

lemma integral_torus_eq_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : UnitAddTorus (Fin 2) → E) (hG : AEStronglyMeasurable G volume) :
    ∫ x, G x = ∫ y in cell 2, G (torusProj y) := by
  rw [← measurePreserving_torusProj.map_eq] at hG ⊢
  exact integral_map measurePreserving_torusProj.measurable.aemeasurable hG

lemma mFourier_torusProj (n : Fin 2 → ℤ) (y : Pt 2) :
    UnitAddTorus.mFourier n (torusProj y) = expChar (intVec n) y := by
  show ∏ i, fourier (n i) ((y i : ℝ) : UnitAddCircle) = _
  simp only [fourier_coe_apply]
  rw [expChar, dot, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [intVec]; ring

/-- Parseval's identity on `𝕋²` for continuous periodic real functions. -/
theorem parseval_cell (h : Pt 2 → ℝ) (hc : Continuous h) (hp : IsPeriodic h) :
    HasSum (fun ℓ => ‖fc (fun x => (h x : ℂ)) ℓ‖ ^ 2) (l2sq h) := by
  set F : UnitAddTorus (Fin 2) → ℂ := fun x => ((torusLift h x : ℝ) : ℂ) with hF
  have hFm : Measurable F := Complex.measurable_ofReal.comp (measurable_torusLift h hc)
  obtain ⟨C, hC⟩ := torusLift_bdd h hc
  have hmem : MemLp F 2 volume := MemLp.of_bound hFm.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa [hF] using hC x)
  have hs := UnitAddTorus.hasSum_sq_mFourierCoeff (hmem.toLp F)
  have e1 : ∀ n, UnitAddTorus.mFourierCoeff (hmem.toLp F) n = UnitAddTorus.mFourierCoeff F n :=
    fun n => integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with t ht; rw [ht])
  have e2 : ∫ t, ‖hmem.toLp F t‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 :=
    integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with t ht; rw [ht])
  have e3 : ∀ n, UnitAddTorus.mFourierCoeff F n = fc (fun x => (h x : ℂ)) n := by
    intro n
    rw [UnitAddTorus.mFourierCoeff, integral_torus_eq_cell
      (fun t => UnitAddTorus.mFourier (-n) t • F t)
      (((UnitAddTorus.mFourier (-n)).continuous.measurable).smul hFm).aestronglyMeasurable, fc]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp only [hF, torusLift_proj h hp, mFourier_torusProj, smul_eq_mul]
    have : intVec (-n) = -intVec n := by funext i; simp [intVec]
    rw [this, mul_comm]
  have e4 : ∫ t, ‖F t‖ ^ 2 = l2sq h := by
    rw [integral_torus_eq_cell _ ((hFm.norm.pow_const 2).aestronglyMeasurable), l2sq]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp [hF, torusLift_proj h hp]
  simp only [e1, e2, e3, e4] at hs
  exact hs


lemma measurable_torusLift_complex (h : Pt 2 → ℂ) (hc : Continuous h) :
    Measurable (torusLift h) :=
  hc.measurable.comp (Measurable.of_eval fun i => measurable_circRep.comp (measurable_pi_apply i))

lemma torusLift_bdd_complex (h : Pt 2 → ℂ) (hc : Continuous h) :
    ∃ C, ∀ x, ‖torusLift h x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Pt 2)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨C, fun x => hC _ ⟨fun i => (circRep_mem (x i)).1, fun i => (circRep_mem (x i)).2⟩⟩

/-- Parseval's identity on `𝕋²` for continuous periodic complex functions. -/
theorem parseval_cell_complex (h : Pt 2 → ℂ) (hc : Continuous h) (hp : IsPeriodic h) :
    HasSum (fun ℓ => ‖fc h ℓ‖ ^ 2) (∫ x in cell 2, ‖h x‖ ^ 2) := by
  set F : UnitAddTorus (Fin 2) → ℂ := torusLift h with hF
  have hFm : Measurable F := measurable_torusLift_complex h hc
  obtain ⟨C, hC⟩ := torusLift_bdd_complex h hc
  have hmem : MemLp F 2 volume := MemLp.of_bound hFm.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa [hF] using hC x)
  have hs := UnitAddTorus.hasSum_sq_mFourierCoeff (hmem.toLp F)
  have e1 : ∀ n, UnitAddTorus.mFourierCoeff (hmem.toLp F) n = UnitAddTorus.mFourierCoeff F n :=
    fun n => integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with t ht; rw [ht])
  have e2 : ∫ t, ‖hmem.toLp F t‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 :=
    integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with t ht; rw [ht])
  have e3 : ∀ n, UnitAddTorus.mFourierCoeff F n = fc h n := by
    intro n
    rw [UnitAddTorus.mFourierCoeff, integral_torus_eq_cell
      (fun t => UnitAddTorus.mFourier (-n) t • F t)
      (((UnitAddTorus.mFourier (-n)).continuous.measurable).smul hFm).aestronglyMeasurable, fc]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp only [hF, torusLift_proj h hp, mFourier_torusProj, smul_eq_mul]
    have : intVec (-n) = -intVec n := by funext i; simp [intVec]
    rw [this, mul_comm]
  have e4 : ∫ t, ‖F t‖ ^ 2 = ∫ x in cell 2, ‖h x‖ ^ 2 := by
    rw [integral_torus_eq_cell _ ((hFm.norm.pow_const 2).aestronglyMeasurable)]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp [hF, torusLift_proj h hp]
  simp only [e1, e2, e3, e4] at hs
  exact hs

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular volume

lemma measurable_torusLift_borel {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] (h : Pt 2 → β) (hc : Continuous h) : Measurable (torusLift h) :=
  hc.measurable.comp (Measurable.of_eval fun i => measurable_circRep.comp (measurable_pi_apply i))

/-- Pushing the uniform law of `𝕋²` forward along a periodic function is unchanged by composing
with a map of `ℝ²` that descends to a measure-preserving map of `𝕋²`. -/
lemma map_cell_comp_of_torus {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (g : Pt 2 → β) (hg : Continuous g) (hp : IsPeriodic g) (T : Pt 2 → Pt 2)
    (τ : UnitAddTorus (Fin 2) → UnitAddTorus (Fin 2)) (hτ : MeasurePreserving τ volume volume)
    (hT : ∀ z, torusProj (T z) = τ (torusProj z)) :
    ((volume : Measure (Pt 2)).restrict (cell 2)).map (fun z => g (T z)) =
      ((volume : Measure (Pt 2)).restrict (cell 2)).map g := by
  have hm := measurable_torusLift_borel g hg
  have hproj := measurePreserving_torusProj
  have e1 : (fun z => g (T z)) = (torusLift g ∘ τ) ∘ torusProj := by
    funext z; simp [hT, ← torusLift_proj g hp (T z)]
  have e2 : g = torusLift g ∘ torusProj := by
    funext z; simp [torusLift_proj g hp z]
  rw [e1, ← Measure.map_map (hm.comp hτ.measurable) hproj.measurable, hproj.map_eq,
    ← Measure.map_map hm hτ.measurable, hτ.map_eq]
  conv_rhs => rw [e2, ← Measure.map_map hm hproj.measurable, hproj.map_eq]

/-- The law of `g(x - Z)` for `Z` uniform on `𝕋²` is the law of `g(Z)`. -/
lemma map_cell_sub_left {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (g : Pt 2 → β) (hg : Continuous g) (hp : IsPeriodic g) (x : Pt 2) :
    ((volume : Measure (Pt 2)).restrict (cell 2)).map (fun z => g (x - z)) =
      ((volume : Measure (Pt 2)).restrict (cell 2)).map g := by
  refine map_cell_comp_of_torus g hg hp (fun z => x - z) (fun u i => torusProj x i - u i) ?_ ?_
  · exact measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun i => Measure.measurePreserving_sub_left volume (torusProj x i)
  · intro z; funext i; simp [torusProj]

/-- The law of `g(x₁ - Z₁, Z₀ - x₀)` for `Z` uniform on `𝕋²` is the law of `g(Z)`. -/
lemma map_cell_rot_sub {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (g : Pt 2 → β) (hg : Continuous g) (hp : IsPeriodic g) (x : Pt 2) :
    ((volume : Measure (Pt 2)).restrict (cell 2)).map (fun z => g ![x 1 - z 1, z 0 - x 0]) =
      ((volume : Measure (Pt 2)).restrict (cell 2)).map g := by
  set h : Fin 2 → UnitAddCircle → UnitAddCircle :=
    fun i => if i = 0 then fun v => torusProj x 1 - v else fun v => v - torusProj x 0
  refine map_cell_comp_of_torus g hg hp (fun z => ![x 1 - z 1, z 0 - x 0])
    ((fun u i => h i (u i)) ∘ fun u i => u (Equiv.swap 0 1 i)) ?_ ?_
  · refine MeasurePreserving.comp (μb := (volume : Measure (UnitAddTorus (Fin 2)))) ?_ ?_
    · refine measurePreserving_pi (fun _ => volume) (fun _ => volume) fun i => ?_
      by_cases hi : i = 0
      · simp only [h, hi, if_true]; exact Measure.measurePreserving_sub_left volume _
      · simp only [h, hi, if_false]; exact measurePreserving_sub_right volume _
    · have := measurePreserving_piCongrLeft (fun _ : Fin 2 => (volume : Measure UnitAddCircle))
        (Equiv.swap (0 : Fin 2) 1)
      convert this using 1
      funext u i
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · intro z; funext i; fin_cases i <;> simp [torusProj, h]

end TorusParseval

end AnomDiss
