module

public import RequestProject.PulseCalc

/-!
# Real Hölder bounds

A real-valued bookkeeping device for `C^α` norms: `HolderBd α h B` says `|h| ≤ B` and
`[h]_α ≤ B`.  It is stable under sums, scalar multiples, series and affine changes of variable,
and controls `holderNorm`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- `‖h‖_∞ ≤ B` and `[h]_α ≤ B`. -/
def HolderBd (α : ℝ) (h : Pt d → E) (B : ℝ) : Prop :=
  (∀ x, ‖h x‖ ≤ B) ∧ ∀ x y, ‖h x - h y‖ ≤ B * ‖x - y‖ ^ α

lemma HolderBd.nonneg {α : ℝ} {h : Pt d → E} {B : ℝ} (hh : HolderBd α h B) : 0 ≤ B :=
  (norm_nonneg _).trans (hh.1 0)

lemma HolderBd.mono {α : ℝ} {h : Pt d → E} {B B' : ℝ} (hh : HolderBd α h B) (hB : B ≤ B') :
    HolderBd α h B' :=
  ⟨fun x => (hh.1 x).trans hB, fun x y => (hh.2 x y).trans
    (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (norm_nonneg _) _))⟩

lemma HolderBd.add {α : ℝ} {f g : Pt d → E} {B C : ℝ} (hf : HolderBd α f B) (hg : HolderBd α g C) :
    HolderBd α (fun x => f x + g x) (B + C) := by
  refine ⟨fun x => (norm_add_le _ _).trans (add_le_add (hf.1 x) (hg.1 x)), fun x y => ?_⟩
  calc ‖f x + g x - (f y + g y)‖ = ‖(f x - f y) + (g x - g y)‖ := by congr 1; abel
    _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
    _ ≤ B * ‖x - y‖ ^ α + C * ‖x - y‖ ^ α := add_le_add (hf.2 x y) (hg.2 x y)
    _ = (B + C) * ‖x - y‖ ^ α := by ring

lemma HolderBd.smul [NormedSpace ℝ E] {α : ℝ} {f : Pt d → E} {B : ℝ} (hf : HolderBd α f B) (c : ℝ) :
    HolderBd α (fun x => c • f x) (|c| * B) := by
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hf.1 x) (abs_nonneg _)
  · rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf.2 x y) (abs_nonneg _)

lemma HolderBd.zero {α : ℝ} : HolderBd α (fun _ : Pt d => (0 : E)) 0 :=
  ⟨fun _ => by simp, fun _ _ => by simp⟩

lemma HolderBd.sum {ι : Type*} (s : Finset ι) {α : ℝ} {f : ι → Pt d → E} {B : ι → ℝ}
    (hf : ∀ i ∈ s, HolderBd α (f i) (B i)) :
    HolderBd α (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HolderBd.zero (α := α) (d := d) (E := E))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma HolderBd.comp_affine {α : ℝ} (hα : 0 ≤ α) {F : Pt d → E} {B : ℝ} (hF : HolderBd α F B)
    {k : ℝ} (hk : 1 ≤ k) (z : Pt d) :
    HolderBd α (fun x => F (k • x - z)) (k ^ α * B) := by
  have hB := hF.nonneg
  have hkα : 1 ≤ k ^ α := Real.one_le_rpow hk hα
  refine ⟨fun x => (hF.1 _).trans (le_mul_of_one_le_left hB hkα), fun x y => ?_⟩
  have e : (k • x - z) - (k • y - z) = k • (x - y) := by rw [smul_sub]; abel
  calc ‖F (k • x - z) - F (k • y - z)‖ ≤ B * ‖(k • x - z) - (k • y - z)‖ ^ α := hF.2 _ _
    _ = k ^ α * B * ‖x - y‖ ^ α := by
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
          Real.mul_rpow (by linarith) (norm_nonneg _)]
        ring

/-- Hölder bounds control the `C^α` norm. -/
lemma holderNorm_le_of_bd {α : ℝ} (hα : 0 < α) {h : Pt d → E} {B : ℝ} (hh : HolderBd α h B) :
    holderNorm α h ≤ ENNReal.ofReal (2 * B) := by
  have hB := hh.nonneg
  rw [show 2 * B = B + B by ring, ENNReal.ofReal_add hB hB]
  refine add_le_add (iSup_le fun x => ?_) (iSup_le fun x => iSup_le fun y => ?_)
  · rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hh.1 x)
  · rcases eq_or_ne x y with rfl | hxy
    · simp
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hr : ‖x - y‖ₑ ^ α = ENNReal.ofReal (‖x - y‖ ^ α) := by
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα.le]
    have hrpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hpos α
    rw [hr, ENNReal.div_le_iff (by simpa using hrpos) ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_mul hB, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hh.2 x y)

variable [CompleteSpace E]

lemma HolderBd.tsum {α : ℝ} {f : ℕ → Pt d → E} {B : ℕ → ℝ} (hf : ∀ j, HolderBd α (f j) (B j))
    (hB : Summable B) : HolderBd α (fun x => ∑' j, f j x) (∑' j, B j) := by
  have hs : ∀ x, Summable fun j => f j x := fun x =>
    Summable.of_norm_bounded hB fun j => (hf j).1 x
  refine ⟨fun x => tsum_of_norm_bounded hB.hasSum fun j => (hf j).1 x, fun x y => ?_⟩
  rw [← (hs x).tsum_sub (hs y)]
  refine tsum_of_norm_bounded ?_ fun j => (hf j).2 x y
  exact hB.hasSum.mul_right _

end AnomDiss
