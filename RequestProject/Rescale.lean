module

public import RequestProject.Residue

/-!
# Parabolic rescaling

Behaviour of the parabolic Hölder classes and of classical scalar solutions under the change of
variables `(s, y) ↦ (a s, c y)` with `a, c > 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pd_smul_comp (f : Pt d → E) (c : ℝ) (i : Fin d) (y : Pt d)
    (hf : DifferentiableAt ℝ f (c • y)) :
    pd i (fun z => f (c • z)) y = c • pd i f (c • y) := by
  unfold pd
  have h := hf.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul c)
  show fderiv ℝ (f ∘ HSMul.hSMul c) y _ = _
  rw [h.fderiv]
  simp

lemma pd_const_smul_fun (f : Pt d → E) (c : ℝ) (i : Fin d) (y : Pt d)
    (hf : DifferentiableAt ℝ f y) :
    pd i (fun z => c • f z) y = c • pd i f y := by
  unfold pd
  rw [fderiv_fun_const_smul hf]
  rfl

lemma mem_Icc_mul {a T s : ℝ} (ha : 0 < a) (hs : s ∈ Icc 0 T) : a * s ∈ Icc 0 (a * T) :=
  ⟨mul_nonneg ha.le hs.1, mul_le_mul_of_nonneg_left hs.2 ha.le⟩

lemma BddOn.rescale {T a c : ℝ} (ha : 0 < a) {g : ℝ → Pt d → E} (hg : BddOn (a * T) g) (K : ℝ) :
    BddOn T (fun s y => K • g (a * s) (c • y)) := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨|K| * C, fun t ht x => ?_⟩
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC _ (mem_Icc_mul ha ht) _) (abs_nonneg _)

lemma rpow_rescale_le {a c β A B : ℝ} (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    (c * A) ^ β + (a * B) ^ (β / 2) ≤ (c ^ β + a ^ (β / 2)) * (A ^ β + B ^ (β / 2)) := by
  rw [Real.mul_rpow hc.le hA, Real.mul_rpow ha.le hB]
  have h1 : 0 ≤ c ^ β := Real.rpow_nonneg hc.le _
  have h2 : 0 ≤ a ^ (β / 2) := Real.rpow_nonneg ha.le _
  have h3 : 0 ≤ A ^ β := Real.rpow_nonneg hA _
  have h4 : 0 ≤ B ^ (β / 2) := Real.rpow_nonneg hB _
  nlinarith [mul_nonneg h1 h4, mul_nonneg h2 h3]

lemma ParHolder.rescale {T β a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {g : ℝ → Pt d → E} (hg : ParHolder (a * T) β g) (K : ℝ) :
    ParHolder T β (fun s y => K • g (a * s) (c • y)) := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨|K| * |C| * (c ^ β + a ^ (β / 2)), fun t ht s hs x y => ?_⟩
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have h := hC _ (mem_Icc_mul ha ht) _ (mem_Icc_mul ha hs) (c • x) (c • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← mul_sub, abs_mul,
    abs_of_pos ha] at h
  have hA : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hB : 0 ≤ |t - s| := abs_nonneg _
  have h' := rpow_rescale_le (β := β) ha hc hA hB
  have hpos : 0 ≤ (c * ‖x - y‖) ^ β + (a * |t - s|) ^ (β / 2) := by positivity
  calc |K| * ‖g (a * t) (c • x) - g (a * s) (c • y)‖
      ≤ |K| * (|C| * ((c * ‖x - y‖) ^ β + (a * |t - s|) ^ (β / 2))) := by
        refine mul_le_mul_of_nonneg_left (h.trans ?_) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    _ ≤ |K| * (|C| * ((c ^ β + a ^ (β / 2)) * (‖x - y‖ ^ β + |t - s| ^ (β / 2)))) := by
        gcongr
    _ = _ := by ring

lemma TimeHolder.rescale {T γ a c : ℝ} (ha : 0 < a)
    {g : ℝ → Pt d → E} (hg : TimeHolder (a * T) γ g) (K : ℝ) :
    TimeHolder T γ (fun s y => K • g (a * s) (c • y)) := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨|K| * |C| * a ^ γ, fun t ht s hs x => ?_⟩
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have h := hC _ (mem_Icc_mul ha ht) _ (mem_Icc_mul ha hs) (c • x)
  rw [← mul_sub, abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg _)] at h
  have hpos : 0 ≤ a ^ γ * |t - s| ^ γ := by positivity
  calc |K| * ‖g (a * t) (c • x) - g (a * s) (c • x)‖
      ≤ |K| * (|C| * (a ^ γ * |t - s| ^ γ)) := by
        refine mul_le_mul_of_nonneg_left (h.trans ?_) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    _ = _ := by ring

/-- Time derivative of a rescaled function. -/
lemma dt_rescale {T β a c : ℝ} (hT : 0 < T) (ha : 0 < a) {u : ℝ → Pt d → E}
    (hu : IsParabolicC12 (a * T) β u) (s : ℝ) (hs : s ∈ Icc 0 T) (y : Pt d) :
    dt T (fun s y => u (a * s) (c • y)) s y = a • dt (a * T) u (a * s) (c • y) := by
  have h1 : HasDerivWithinAt (fun r => u r (c • y)) (dt (a * T) u (a * s) (c • y))
      (Icc 0 (a * T)) (a * s) :=
    (hu.diff_t (c • y) (a * s) (mem_Icc_mul ha hs)).hasDerivWithinAt
  have h2 : HasDerivWithinAt (fun r : ℝ => a * r) a (Icc 0 T) s := by
    simpa using ((hasDerivAt_id s).const_mul a).hasDerivWithinAt
  have hmaps : MapsTo (fun r : ℝ => a * r) (Icc 0 T) (Icc 0 (a * T)) :=
    fun r hr => mem_Icc_mul ha hr
  have h3 := h1.scomp s h2 hmaps
  exact h3.derivWithin (uniqueDiffOn_Icc hT s hs)

/-- First spatial derivatives of a rescaled slice. -/
lemma pd_rescale_slice {T β a c : ℝ} (ha : 0 < a) {u : ℝ → Pt d → E}
    (hu : IsParabolicC12 (a * T) β u) (i : Fin d) (t : ℝ) (ht : t ∈ Icc 0 T) :
    pd i (fun y => u (a * t) (c • y)) = fun y => c • pd i (u (a * t)) (c • y) := by
  funext y
  exact pd_smul_comp _ c i y
    (((hu.smooth_x _ (mem_Icc_mul ha ht)).differentiable (by norm_num)) _)

/-- Second spatial derivatives of a rescaled slice. -/
lemma pd_pd_rescale_slice {T β a c : ℝ} (ha : 0 < a) {u : ℝ → Pt d → E}
    (hu : IsParabolicC12 (a * T) β u) (i j : Fin d) (t : ℝ) (ht : t ∈ Icc 0 T) :
    pd i (pd j (fun y => u (a * t) (c • y))) =
      fun y => (c * c) • pd i (pd j (u (a * t))) (c • y) := by
  rw [pd_rescale_slice ha hu j t ht]
  funext y
  have hd := differentiable_pd (hu.smooth_x _ (mem_Icc_mul ha ht)) j
  rw [pd_smul_comp (fun x => c • pd j (u (a * t)) x) c i y
      ((hd (c • y)).const_smul c),
    pd_const_smul_fun _ c i _ (hd (c • y)), smul_smul]

/-- The parabolic class `C^{1+β/2,2+β}` is invariant under `(s, y) ↦ (a s, c y)`. -/
lemma IsParabolicC12.rescale {T β a c : ℝ} (hT : 0 < T) (ha : 0 < a) (hc : 0 < c)
    {u : ℝ → Pt d → E} (hu : IsParabolicC12 (a * T) β u) :
    IsParabolicC12 T β (fun s y => u (a * s) (c • y)) := by
  have hone : ∀ (g : ℝ → Pt d → E), (fun s y => (1 : ℝ) • g (a * s) (c • y)) =
      fun s y => g (a * s) (c • y) := fun g => by simp
  have hdt : ∀ t ∈ Icc 0 T, dt T (fun s y => u (a * s) (c • y)) t =
      fun y => a • dt (a * T) u (a * t) (c • y) := fun t ht => funext fun y =>
    dt_rescale hT ha hu t ht y
  exact {
    smooth_x := fun t ht => (hu.smooth_x _ (mem_Icc_mul ha ht)).comp (contDiff_id.const_smul c)
    diff_t := fun x t ht => by
      have h1 := hu.diff_t (c • x) (a * t) (mem_Icc_mul ha ht)
      have h2 : DifferentiableWithinAt ℝ (fun r : ℝ => a * r) (Icc 0 T) t :=
        (differentiableAt_id.const_mul a).differentiableWithinAt
      exact h1.comp t h2 (fun r hr => mem_Icc_mul ha hr)
    bdd := by rw [← hone]; exact hu.bdd.rescale ha 1
    bdd_dt := bddOn_congr hdt (hu.bdd_dt.rescale ha a)
    holder_dt := parHolder_congr hdt (hu.holder_dt.rescale ha hc a)
    bdd_d1 := fun i => bddOn_congr (fun t ht => pd_rescale_slice ha hu i t ht)
      ((hu.bdd_d1 i).rescale ha c)
    holder_d1_time := fun i => timeHolder_congr (fun t ht => pd_rescale_slice ha hu i t ht)
      ((hu.holder_d1_time i).rescale ha c)
    bdd_d2 := fun i j => bddOn_congr (fun t ht => pd_pd_rescale_slice ha hu i j t ht)
      ((hu.bdd_d2 i j).rescale ha (c * c))
    holder_d2 := fun i j => parHolder_congr (fun t ht => pd_pd_rescale_slice ha hu i j t ht)
      ((hu.holder_d2 i j).rescale ha hc (c * c)) }

end AnomDiss
