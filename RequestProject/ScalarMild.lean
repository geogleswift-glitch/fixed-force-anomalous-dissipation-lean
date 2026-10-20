module

public import RequestProject.ScalarDuhamel
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# A local mild solution of the scalar equation

The operator here uses the Gaussian heat semigroup and the actual divergence-form
Duhamel integral. The Banach fixed-point argument constructs a function, with
no PDE existence hypothesis. Classical derivatives and Hölder regularity are
separate further steps.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal BoundedContinuousFunction

noncomputable section

namespace AnomDiss

abbrev ScalarTimeSlab (T : ℝ) := Icc (0 : ℝ) T × Pt 2
abbrev SlabScalar (T : ℝ) := ScalarTimeSlab T →ᵇ ℂ

/-- A continuous time extension, constant before and after the closed slab. -/
def extendSlabScalar {T : ℝ} (hT : 0 ≤ T) (F : SlabScalar T)
    (s : ℝ) (x : Pt 2) : ℂ := F (projIcc 0 T hT s, x)

lemma continuous_extendSlabScalar {T : ℝ} (hT : 0 ≤ T) (F : SlabScalar T) :
    Continuous (Function.uncurry (extendSlabScalar hT F)) :=
  F.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd)

lemma norm_extendSlabScalar_le {T : ℝ} (hT : 0 ≤ T) (F : SlabScalar T)
    (s : ℝ) (x : Pt 2) : ‖extendSlabScalar hT F s x‖ ≤ ‖F‖ :=
  F.norm_coe_le_norm _

lemma extendSlabScalar_of_mem {T : ℝ} (hT : 0 ≤ T) (F : SlabScalar T)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : Pt 2) :
    extendSlabScalar hT F s x = F (⟨s, hs⟩, x) := by
  simp [extendSlabScalar, projIcc_of_mem hT hs]

lemma continuous_heat_initial (ν : ℝ) (f : Pt 2 →ᵇ ℂ) :
    Continuous fun p : ℝ × Pt 2 => heatOp (Real.toNNReal (2 * ν * p.1)) f p.2 := by
  simp_rw [heatOp_eq_scaled f.continuous]
  refine continuous_of_dominated (bound := fun _ => ‖f‖)
    (fun p => by
      have hA : Continuous (fun ζ : Pt 2 =>
          p.2 + Real.sqrt (Real.toNNReal (2 * ν * p.1)) • ζ) :=
        continuous_const.fun_add (continuous_const_smul _)
      simpa only [Function.comp_def] using (f.continuous.comp hA).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun ζ => f.norm_coe_le_norm _)
    (integrable_const ‖f‖) (Eventually.of_forall fun ζ => ?_)
  have hσ : Continuous (fun p : ℝ × Pt 2 =>
      Real.sqrt (Real.toNNReal (2 * ν * p.1))) := by
    simpa only [Function.comp_def] using
      Real.continuous_sqrt.comp (NNReal.continuous_coe.comp
        (continuous_real_toNNReal.comp ((continuous_const (y := 2 * ν)).fun_mul continuous_fst)))
  have hA : Continuous (fun p : ℝ × Pt 2 =>
      p.2 + Real.sqrt (Real.toNNReal (2 * ν * p.1)) • ζ) :=
    continuous_snd.fun_add (hσ.fun_smul (continuous_const (y := ζ)))
  simpa only [Function.comp_def] using f.continuous.comp hA

/-- The genuine homogeneous heat solution as a bounded continuous slab function. -/
def slabHeatInitial (ν T : ℝ) (f : Pt 2 →ᵇ ℂ) : SlabScalar T :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f p.2)
    ((continuous_heat_initial ν f).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
    ‖f‖ (fun p => norm_heatOp_le (fun x => f.norm_coe_le_norm x) _ p.2)

@[simp] lemma slabHeatInitial_apply (ν T : ℝ) (f : Pt 2 →ᵇ ℂ) (p : ScalarTimeSlab T) :
    slabHeatInitial ν T f p = heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f p.2 := rfl

lemma norm_slabHeatInitial_le (ν T : ℝ) (f : Pt 2 →ᵇ ℂ) :
    ‖slabHeatInitial ν T f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
    fun p => norm_heatOp_le (fun x => f.norm_coe_le_norm x) _ p.2

/-- One component of the actual Duhamel operator on a finite time slab. -/
def slabDuhamel {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (i : Fin 2) (F : SlabScalar T) : SlabScalar T :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => duhamelComponent ν (extendSlabScalar hT F) i p.1 p.2)
    ((continuousOn_duhamelComponent hν (continuous_extendSlabScalar hT F)
      (norm_extendSlabScalar_le hT F) i hT).comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p => p.1.property))
    (2 * duhamelScale ν ‖F‖ * Real.sqrt T)
    (fun p => (norm_duhamelComponent_le hν (continuous_extendSlabScalar hT F)
      (norm_extendSlabScalar_le hT F) i p.1.property.1 p.2).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt p.1.property.2)
          (mul_nonneg (by norm_num) (duhamelScale_nonneg (norm_nonneg F)))))

@[simp] lemma slabDuhamel_apply {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (i : Fin 2) (F : SlabScalar T) (p : ScalarTimeSlab T) :
    slabDuhamel hν hT i F p = duhamelComponent ν (extendSlabScalar hT F) i p.1 p.2 := rfl

lemma norm_slabDuhamel_le {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (i : Fin 2) (F : SlabScalar T) :
    ‖slabDuhamel hν hT i F‖ ≤ 2 * duhamelScale ν ‖F‖ * Real.sqrt T := by
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg (by norm_num) (duhamelScale_nonneg (norm_nonneg F)))
      (Real.sqrt_nonneg _))).2 fun p => ?_
  exact (norm_duhamelComponent_le hν (continuous_extendSlabScalar hT F)
    (norm_extendSlabScalar_le hT F) i p.1.property.1 p.2).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt p.1.property.2)
        (mul_nonneg (by norm_num) (duhamelScale_nonneg (norm_nonneg F))))

lemma slabDuhamel_uniform_distance {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (i : Fin 2) (F G : SlabScalar T) :
    ‖slabDuhamel hν hT i F - slabDuhamel hν hT i G‖ ≤
      2 * duhamelScale ν ‖F - G‖ * Real.sqrt T := by
  refine (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg (by norm_num) (duhamelScale_nonneg (norm_nonneg (F - G))))
      (Real.sqrt_nonneg _))).2 fun p => ?_
  have hD : ∀ s x, ‖extendSlabScalar hT F s x - extendSlabScalar hT G s x‖ ≤ ‖F - G‖ :=
    fun s x => (F - G).norm_coe_le_norm (projIcc 0 T hT s, x)
  exact (duhamelComponent_uniform_distance hν (continuous_extendSlabScalar hT F)
    (continuous_extendSlabScalar hT G) (norm_extendSlabScalar_le hT F)
    (norm_extendSlabScalar_le hT G) hD i p.1.property.1 p.2).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt p.1.property.2)
        (mul_nonneg (by norm_num) (duhamelScale_nonneg (norm_nonneg (F - G)))))

/-- Divergence-form scalar Picard operator, with fixed supplied drift coefficients. -/
def scalarMildMap {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ) (u : SlabScalar T) : SlabScalar T :=
  slabHeatInitial ν T f - ∑ i : Fin 2, slabDuhamel hν hT i (b i * u)

/-- The explicitly computed contraction constant for the two-dimensional drift. -/
def scalarMildRate (ν B T : ℝ) : ℝ := 4 * duhamelScale ν B * Real.sqrt T

lemma scalarMildRate_nonneg {ν B T : ℝ} (hB : 0 ≤ B) : 0 ≤ scalarMildRate ν B T :=
  mul_nonneg (mul_nonneg (by norm_num) (duhamelScale_nonneg hB)) (Real.sqrt_nonneg _)

lemma duhamelScale_mono {ν C D : ℝ} (hCD : C ≤ D) :
    duhamelScale ν C ≤ duhamelScale ν D :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCD (gmom_nonneg 1))
    (Real.sqrt_nonneg _)

lemma duhamelScale_mul (ν C D : ℝ) : duhamelScale ν (C * D) = duhamelScale ν C * D := by
  simp only [duhamelScale, div_eq_mul_inv]
  ring

theorem scalarMildMap_uniform_distance {ν T B : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (b : Fin 2 → SlabScalar T) (hb : ∀ i, ‖b i‖ ≤ B)
    (f : Pt 2 →ᵇ ℂ) (u w : SlabScalar T) :
    ‖scalarMildMap hν hT b f u - scalarMildMap hν hT b f w‖ ≤
      scalarMildRate ν B T * ‖u - w‖ := by
  have hd : ∀ i : Fin 2,
      ‖slabDuhamel hν hT i (b i * u) - slabDuhamel hν hT i (b i * w)‖ ≤
        2 * duhamelScale ν B * Real.sqrt T * ‖u - w‖ := by
    intro i
    have hs : ‖b i * u - b i * w‖ ≤ B * ‖u - w‖ := by
      rw [← mul_sub]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
    calc
      ‖slabDuhamel hν hT i (b i * u) - slabDuhamel hν hT i (b i * w)‖
          ≤ 2 * duhamelScale ν ‖b i * u - b i * w‖ * Real.sqrt T :=
        slabDuhamel_uniform_distance hν hT i _ _
      _ ≤ 2 * duhamelScale ν (B * ‖u - w‖) * Real.sqrt T := by
        gcongr
        exact duhamelScale_mono hs
      _ = 2 * duhamelScale ν B * Real.sqrt T * ‖u - w‖ := by
        rw [duhamelScale_mul]
        ring
  calc
    ‖scalarMildMap hν hT b f u - scalarMildMap hν hT b f w‖
        = ‖∑ i : Fin 2, (slabDuhamel hν hT i (b i * u) -
            slabDuhamel hν hT i (b i * w))‖ := by
      unfold scalarMildMap
      rw [sub_sub_sub_cancel_left, norm_sub_rev, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin 2, ‖slabDuhamel hν hT i (b i * u) -
          slabDuhamel hν hT i (b i * w)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, 2 * duhamelScale ν B * Real.sqrt T * ‖u - w‖ :=
      Finset.sum_le_sum fun i _ => hd i
    _ = scalarMildRate ν B T * ‖u - w‖ := by
      simp [scalarMildRate]
      ring

/-- Banach's theorem constructs the unique bounded continuous mild solution whenever
the explicit interval-length bound is satisfied. -/
theorem exists_unique_scalar_mild_fixedPoint {ν T B : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hB : 0 ≤ B) (b : Fin 2 → SlabScalar T) (hb : ∀ i, ‖b i‖ ≤ B)
    (f : Pt 2 →ᵇ ℂ) (hsmall : scalarMildRate ν B T < 1) :
    ∃! u : SlabScalar T, scalarMildMap hν hT b f u = u := by
  let K : ℝ≥0 := ⟨scalarMildRate ν B T, scalarMildRate_nonneg hB⟩
  have hc : ContractingWith K (scalarMildMap hν hT b f) := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
    simp only [dist_eq_norm]
    change ‖scalarMildMap hν hT b f u - scalarMildMap hν hT b f w‖ ≤
      scalarMildRate ν B T * ‖u - w‖
    exact scalarMildMap_uniform_distance hν hT b hb f u w
  exact ⟨hc.fixedPoint _, hc.fixedPoint_isFixedPt, fun u hu => hc.fixedPoint_unique hu⟩

/-- The constructed fixed point solves the actual Gaussian integral equation and
attains the prescribed initial data. -/
theorem exists_scalar_mild {ν T B : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hB : 0 ≤ B) (b : Fin 2 → SlabScalar T) (hb : ∀ i, ‖b i‖ ≤ B)
    (f : Pt 2 →ᵇ ℂ) (hsmall : scalarMildRate ν B T < 1) :
    ∃ u : SlabScalar T,
      (∀ p : ScalarTimeSlab T, u p =
        heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f p.2 -
          ∑ i : Fin 2, duhamelComponent ν
            (extendSlabScalar hT (b i * u)) i p.1 p.2) ∧
      (∀ x, u (⟨0, ⟨le_rfl, hT⟩⟩, x) = f x) := by
  obtain ⟨u, hu, _⟩ := exists_unique_scalar_mild_fixedPoint hν hT hB b hb f hsmall
  have he : ∀ p : ScalarTimeSlab T, u p =
      heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f p.2 -
        ∑ i : Fin 2, duhamelComponent ν (extendSlabScalar hT (b i * u)) i p.1 p.2 := by
    intro p
    have hp := congrArg (fun v : SlabScalar T => v p) hu
    simpa [scalarMildMap] using hp.symm
  refine ⟨u, he, fun x => ?_⟩
  simpa [heatOp_zero f.continuous] using he (⟨0, ⟨le_rfl, hT⟩⟩, x)

/-- Restriction from a longer slab preserves the uniform norm bound. -/
def restrictSlabScalar {S T : ℝ} (hST : S ≤ T) (F : SlabScalar T) : SlabScalar S :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => F (⟨p.1, ⟨p.1.property.1, p.1.property.2.trans hST⟩⟩, p.2))
    (F.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).subtype_mk
        (fun p => ⟨p.1.property.1, p.1.property.2.trans hST⟩) |>.prodMk continuous_snd))
    ‖F‖ (fun _ => F.norm_coe_le_norm _)

lemma norm_restrictSlabScalar_le {S T : ℝ} (hST : S ≤ T) (F : SlabScalar T) :
    ‖restrictSlabScalar hST F‖ ≤ ‖F‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun _ => F.norm_coe_le_norm _

/-- An explicitly positive local length that always makes the Picard operator contract. -/
def scalarLocalTime (ν B T : ℝ) : ℝ :=
  min T ((1 / (1 + 8 * duhamelScale ν B)) ^ 2)

lemma scalarLocalTime_pos {ν B T : ℝ} (hT : 0 < T) (hB : 0 ≤ B) :
    0 < scalarLocalTime ν B T := by
  have hs := duhamelScale_nonneg (ν := ν) hB
  unfold scalarLocalTime
  exact lt_min hT (sq_pos_of_pos (one_div_pos.2 (by positivity)))

lemma scalarLocalTime_le (ν B T : ℝ) : scalarLocalTime ν B T ≤ T := min_le_left _ _

lemma scalarMildRate_scalarLocalTime_lt_one {ν B T : ℝ} (hB : 0 ≤ B) :
    scalarMildRate ν B (scalarLocalTime ν B T) < 1 := by
  have hs : 0 ≤ duhamelScale ν B := duhamelScale_nonneg hB
  have hden : 0 < 1 + 8 * duhamelScale ν B := by positivity
  have hsqrt : Real.sqrt (scalarLocalTime ν B T) ≤ 1 / (1 + 8 * duhamelScale ν B) := by
    calc
      Real.sqrt (scalarLocalTime ν B T)
          ≤ Real.sqrt ((1 / (1 + 8 * duhamelScale ν B)) ^ 2) :=
        Real.sqrt_le_sqrt (min_le_right _ _)
      _ = 1 / (1 + 8 * duhamelScale ν B) :=
        Real.sqrt_sq (by positivity)
  unfold scalarMildRate
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (by norm_num) hs))
  rw [← mul_div_assoc, mul_one, div_lt_one hden]
  linarith

/-- Every supplied bounded continuous drift on a positive slab has a genuinely
constructed local mild solution on an explicitly positive shorter slab. -/
theorem exists_scalar_local_mild {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (b : Fin 2 → SlabScalar T) (f : Pt 2 →ᵇ ℂ) :
    ∃ (S : ℝ) (hS : 0 < S) (hST : S ≤ T) (u : SlabScalar S),
      (∀ p : ScalarTimeSlab S, u p =
        heatOp (Real.toNNReal (2 * ν * (p.1 : ℝ))) f p.2 -
          ∑ i : Fin 2, duhamelComponent ν
            (extendSlabScalar hS.le (restrictSlabScalar hST (b i) * u)) i p.1 p.2) ∧
      (∀ x, u (⟨0, ⟨le_rfl, hS.le⟩⟩, x) = f x) := by
  let B := ‖b 0‖ + ‖b 1‖
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  let S := scalarLocalTime ν B T
  have hS : 0 < S := scalarLocalTime_pos hT hB
  have hST : S ≤ T := scalarLocalTime_le ν B T
  have hb : ∀ i : Fin 2, ‖restrictSlabScalar hST (b i)‖ ≤ B := by
    intro i
    apply (norm_restrictSlabScalar_le hST (b i)).trans
    fin_cases i
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  obtain ⟨u, hu, hinit⟩ := exists_scalar_mild hν hS.le hB
    (fun i => restrictSlabScalar hST (b i)) hb f (scalarMildRate_scalarLocalTime_lt_one hB)
  exact ⟨S, hS, hST, u, hu, hinit⟩

end AnomDiss
