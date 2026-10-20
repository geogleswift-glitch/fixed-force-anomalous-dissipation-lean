module

public import RequestProject.Basic

/-!
# Calculus for fields on `𝕋³` that are independent of `x₃`

Auxiliary material for Lemma 7.10 (embedding of the two-dimensional problem into three
dimensions): the projection `(x₁,x₂,x₃) ↦ (x₁,x₂)`, the embedding `(v, θ) ↦ (v₁, v₂, θ)` and
the behaviour of derivatives, integrals and Hölder conditions under it.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- The horizontal projection `(x₁,x₂,x₃) ↦ (x₁,x₂)`. -/
def proj3 (x : Pt 3) : Pt 2 := ![x 0, x 1]

/-- `(v, θ) ↦ u = (v₁, v₂, θ)`, independent of `x₃`. -/
def embedU (v : Pt 2 → Pt 2) (θ : Pt 2 → ℝ) (x : Pt 3) : Pt 3 :=
  ![v (proj3 x) 0, v (proj3 x) 1, θ (proj3 x)]

lemma abs_le_euclNorm {d : ℕ} (w : Pt d) (i : Fin d) : |w i| ≤ euclNorm w := by
  unfold euclNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => w j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma proj3_eq (x : Pt 3) : proj3 x = fun j => x (Fin.castSucc j) := by
  funext j; fin_cases j <;> rfl

/-- `proj3` as a continuous linear map. -/
def proj3L : Pt 3 →L[ℝ] Pt 2 :=
  ContinuousLinearMap.pi fun j : Fin 2 => ContinuousLinearMap.proj (Fin.castSucc j)

lemma proj3L_apply (x : Pt 3) : proj3L x = proj3 x := by
  rw [proj3_eq]; rfl

lemma proj3_comp_eq : proj3 = (proj3L : Pt 3 → Pt 2) := by
  funext x; rw [proj3L_apply]

lemma proj3_add (x y : Pt 3) : proj3 (x + y) = proj3 x + proj3 y := by
  rw [proj3_comp_eq]; exact map_add _ _ _

lemma proj3_sub (x y : Pt 3) : proj3 (x - y) = proj3 x - proj3 y := by
  rw [proj3_comp_eq]; exact map_sub _ _ _

lemma norm_proj3_le (x : Pt 3) : ‖proj3 x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun j => ?_)
  rw [proj3_eq]
  exact norm_le_pi_norm x _

lemma proj3_intVec (n : Fin 3 → ℤ) : proj3 (intVec n) = intVec (fun j => n (Fin.castSucc j)) := by
  rw [proj3_eq]; rfl

lemma contDiff_proj3 {n : WithTop ℕ∞} : ContDiff ℝ n proj3 := by
  rw [proj3_comp_eq]; exact proj3L.contDiff

lemma integral_cell3 (F : Pt 2 → ℝ) : ∫ x in cell 3, F (proj3 x) = ∫ y in cell 2, F y := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have he : ∀ x, e x = (x (Fin.last 2), proj3 x) := by
    intro x
    simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    rw [proj3_eq]
    ext j
    · rfl
    · simp only [Fin.removeNth]
      fin_cases j <;> rfl
  have hmp : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ _
  have hset : cell 3 = e ⁻¹' (Icc (0:ℝ) 1 ×ˢ cell 2) := by
    ext x
    simp only [cell, mem_preimage, he, mem_prod, mem_Icc, Pi.le_def, Pi.zero_apply,
      Pi.one_apply, proj3_eq]
    constructor
    · intro h; exact ⟨⟨h.1 _, h.2 _⟩, fun j => h.1 _, fun j => h.2 _⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
      all_goals first | exact h3 0 | exact h3 1 | exact h1 | exact h4 0 | exact h4 1 | exact h2
  rw [hset]
  have := hmp.setIntegral_preimage_emb e.measurableEmbedding
    (fun z : ℝ × Pt 2 => (fun _ : ℝ => (1:ℝ)) z.1 * F z.2) (Icc (0:ℝ) 1 ×ˢ cell 2)
  simp only [he, one_mul] at this
  rw [this]
  have h2 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Pt 2)))
    (fun _ : ℝ => (1:ℝ)) F (Icc 0 1) (cell 2)
  simp only [one_mul] at h2
  rw [← Measure.volume_eq_prod] at h2
  rw [h2]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pd_apply_pi {d m : ℕ} (F : Pt d → Pt m) (x : Pt d) (hF : DifferentiableAt ℝ F x)
    (i : Fin d) (k : Fin m) : pd i F x k = pd i (fun y => F y k) x := by
  unfold pd
  have : (fun y => F y k) = (ContinuousLinearMap.proj k : Pt m →L[ℝ] ℝ) ∘ F := rfl
  rw [this, fderiv_comp x (ContinuousLinearMap.proj k).differentiableAt hF]
  simp

lemma pd_comp_proj3 (h : Pt 2 → E) (x : Pt 3) (hd : DifferentiableAt ℝ h (proj3 x))
    (i : Fin 2) : pd (Fin.castSucc i) (fun y => h (proj3 y)) x = pd i h (proj3 x) := by
  unfold pd
  have : (fun y => h (proj3 y)) = h ∘ proj3L := by funext y; simp [proj3L_apply]
  rw [this, fderiv_comp x (by rwa [proj3L_apply]) proj3L.differentiableAt,
    ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, proj3L_apply]
  congr 1
  rw [proj3L_apply, proj3_eq]
  funext j
  simp only [Pi.single_apply, Fin.castSucc_inj]

lemma pd_comp_proj3_last (h : Pt 2 → E) (x : Pt 3) (hd : DifferentiableAt ℝ h (proj3 x)) :
    pd 2 (fun y => h (proj3 y)) x = 0 := by
  unfold pd
  have : (fun y => h (proj3 y)) = h ∘ proj3L := by funext y; simp [proj3L_apply]
  rw [this, fderiv_comp x (by rwa [proj3L_apply]) proj3L.differentiableAt,
    ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, proj3L_apply]
  have : proj3 (Pi.single 2 1) = 0 := by
    rw [proj3_eq]; funext j; fin_cases j <;> simp
  rw [this, map_zero]

section embed
variable {v : Pt 2 → Pt 2} {θ : Pt 2 → ℝ}

lemma differentiable_embedU (hv : Differentiable ℝ v) (hθ : Differentiable ℝ θ) :
    Differentiable ℝ (embedU v θ) := by
  intro x
  rw [differentiableAt_pi]
  have hp : DifferentiableAt ℝ proj3 x := (contDiff_proj3 (n := 1)).differentiable (by norm_num) x
  intro k
  fin_cases k
  · exact ((differentiableAt_pi.1 (hv (proj3 x))) 0).comp x hp
  · exact ((differentiableAt_pi.1 (hv (proj3 x))) 1).comp x hp
  · exact (hθ (proj3 x)).comp x hp

lemma pd_embedU_cast (hv : Differentiable ℝ v) (hθ : Differentiable ℝ θ) (i : Fin 2) :
    pd (Fin.castSucc i) (embedU v θ) = embedU (pd i v) (pd i θ) := by
  funext x
  ext k
  rw [pd_apply_pi _ _ (differentiable_embedU hv hθ x)]
  fin_cases k
  · change pd i.castSucc (fun y => v (proj3 y) 0) x = pd i v (proj3 x) 0
    rw [pd_comp_proj3 _ _ ((differentiableAt_pi.1 (hv _)) 0), pd_apply_pi _ _ (hv _)]
  · change pd i.castSucc (fun y => v (proj3 y) 1) x = pd i v (proj3 x) 1
    rw [pd_comp_proj3 _ _ ((differentiableAt_pi.1 (hv _)) 1), pd_apply_pi _ _ (hv _)]
  · change pd i.castSucc (fun y => θ (proj3 y)) x = pd i θ (proj3 x)
    rw [pd_comp_proj3 _ _ (hθ _)]

lemma pd_embedU_last (hv : Differentiable ℝ v) (hθ : Differentiable ℝ θ) :
    pd 2 (embedU v θ) = 0 := by
  funext x
  ext k
  rw [pd_apply_pi _ _ (differentiable_embedU hv hθ x)]
  fin_cases k
  · exact pd_comp_proj3_last (fun z => v z 0) x ((differentiableAt_pi.1 (hv _)) 0)
  · exact pd_comp_proj3_last (fun z => v z 1) x ((differentiableAt_pi.1 (hv _)) 1)
  · exact pd_comp_proj3_last θ x (hθ _)

lemma pd_zero_fun {d : ℕ} (i : Fin d) : pd i (0 : Pt d → E) = 0 := by
  funext x; simp [pd]

lemma pd_comp_proj3_fun_cast (h : Pt 2 → E) (hd : Differentiable ℝ h) (i : Fin 2) :
    pd (Fin.castSucc i) (fun y => h (proj3 y)) = fun y => pd i h (proj3 y) := by
  funext x; exact pd_comp_proj3 h x (hd _) i

lemma pd_comp_proj3_fun_last (h : Pt 2 → E) (hd : Differentiable ℝ h) :
    pd 2 (fun y => h (proj3 y)) = 0 := by
  funext x; exact pd_comp_proj3_last h x (hd _)

lemma differentiable_pd {d : ℕ} {h : Pt d → E} (hh : ContDiff ℝ 2 h) (i : Fin d) :
    Differentiable ℝ (pd i h) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (pd i h) := by
    unfold pd
    exact h1.clm_apply contDiff_const
  exact h2.differentiable (by norm_num)

lemma contDiff_pd {d : ℕ} {h : Pt d → E} {n : ℕ} (hh : ContDiff ℝ (n + 1) h) (i : Fin d) :
    ContDiff ℝ n (pd i h) := by
  have h1 : ContDiff ℝ n (fderiv ℝ h) := hh.fderiv_right (by norm_cast)
  unfold pd
  exact h1.clm_apply contDiff_const

lemma contDiff_embedU {n : WithTop ℕ∞} (hv : ContDiff ℝ n v) (hθ : ContDiff ℝ n θ) :
    ContDiff ℝ n (embedU v θ) := by
  rw [contDiff_pi]
  intro k
  fin_cases k
  · exact ((contDiff_pi.1 hv) 0).comp contDiff_proj3
  · exact ((contDiff_pi.1 hv) 1).comp contDiff_proj3
  · exact hθ.comp contDiff_proj3

lemma divergence_embedU (hv : Differentiable ℝ v) (hθ : Differentiable ℝ θ) (x : Pt 3) :
    divergence (embedU v θ) x = divergence v (proj3 x) := by
  unfold divergence
  rw [Fin.sum_univ_three, Fin.sum_univ_two]
  have h0 := congrFun (pd_embedU_cast hv hθ 0) x
  have h1 := congrFun (pd_embedU_cast hv hθ 1) x
  have h2 := congrFun (pd_embedU_last hv hθ) x
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h0 h1
  rw [h0, h1, h2]
  simp [embedU]

lemma lap_embedU (hv : ContDiff ℝ 2 v) (hθ : ContDiff ℝ 2 θ) (x : Pt 3) :
    lap (embedU v θ) x = embedU (lap v) (lap θ) x := by
  have hv1 := hv.differentiable (by norm_num)
  have hθ1 := hθ.differentiable (by norm_num)
  unfold lap
  rw [Fin.sum_univ_three]
  have e0 := pd_embedU_cast hv1 hθ1 0
  have e1 := pd_embedU_cast hv1 hθ1 1
  have e2 := pd_embedU_last hv1 hθ1
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at e0 e1
  rw [e0, e1, e2, pd_zero_fun]
  have f0 := congrFun (pd_embedU_cast (differentiable_pd hv 0) (differentiable_pd hθ 0) 0) x
  have f1 := congrFun (pd_embedU_cast (differentiable_pd hv 1) (differentiable_pd hθ 1) 1) x
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at f0 f1
  rw [f0, f1]
  ext k
  fin_cases k <;> simp [embedU, Fin.sum_univ_two]

lemma conv_embedU {w : Pt 2 → Pt 2} {φ : Pt 2 → ℝ} (hw : Differentiable ℝ w)
    (hφ : Differentiable ℝ φ) (x : Pt 3) :
    conv (embedU v θ) (embedU w φ) x = embedU (conv v w) (conv v φ) x := by
  unfold conv
  rw [Fin.sum_univ_three]
  have h0 := congrFun (pd_embedU_cast hw hφ 0) x
  have h1 := congrFun (pd_embedU_cast hw hφ 1) x
  have h2 := congrFun (pd_embedU_last hw hφ) x
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h0 h1
  rw [h0, h1, h2]
  ext k
  fin_cases k <;> simp [embedU, Fin.sum_univ_two]

lemma grad_comp_proj3 (p : Pt 2 → ℝ) (hp : Differentiable ℝ p) (x : Pt 3) :
    grad (fun y => p (proj3 y)) x = embedU (grad p) 0 x := by
  ext k
  fin_cases k
  · show pd 0 (fun y => p (proj3 y)) x = _
    exact pd_comp_proj3 p x (hp _) 0
  · show pd 1 (fun y => p (proj3 y)) x = _
    exact pd_comp_proj3 p x (hp _) 1
  · show pd 2 (fun y => p (proj3 y)) x = _
    rw [pd_comp_proj3_last p x (hp _)]
    simp [embedU]

lemma gradSqV_embedU (hv : Differentiable ℝ v) (hθ : Differentiable ℝ θ) (x : Pt 3) :
    gradSqV (embedU v θ) x = gradSqV v (proj3 x) + gradSq θ (proj3 x) := by
  unfold gradSqV gradSq
  rw [Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_two]
  have h0 := congrFun (pd_embedU_cast hv hθ 0) x
  have h1 := congrFun (pd_embedU_cast hv hθ 1) x
  have h2 := congrFun (pd_embedU_last hv hθ) x
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h0 h1
  rw [h0, h1, h2]
  simp [embedU, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

lemma isPeriodic_comp_proj3 {α : Type*} {h : Pt 2 → α} (hh : IsPeriodic h) :
    IsPeriodic (fun y => h (proj3 y)) := by
  intro x n
  simp only [proj3_add, proj3_intVec]
  exact hh _ _

lemma isPeriodic_embedU (hv : IsPeriodic v) (hθ : IsPeriodic θ) :
    IsPeriodic (embedU v θ) := by
  intro x n
  simp only [embedU, proj3_add, proj3_intVec, hv _ _, hθ _ _]

end embed

section holder
variable {T β γ : ℝ}

lemma norm_embedU_sub_le (a a' : Pt 2 → Pt 2) (b b' : Pt 2 → ℝ) (x y : Pt 3) :
    ‖embedU a b x - embedU a' b' y‖ ≤ ‖a (proj3 x) - a' (proj3 y)‖ + ‖b (proj3 x) - b' (proj3 y)‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun k => ?_)
  fin_cases k
  · have := norm_le_pi_norm (a (proj3 x) - a' (proj3 y)) 0
    simp only [embedU, Pi.sub_apply] at this ⊢
    simp only [Real.norm_eq_abs] at this ⊢
    simp; linarith [abs_nonneg (b (proj3 x) - b' (proj3 y))]
  · have := norm_le_pi_norm (a (proj3 x) - a' (proj3 y)) 1
    simp only [embedU, Pi.sub_apply] at this ⊢
    simp only [Real.norm_eq_abs] at this ⊢
    simp; linarith [abs_nonneg (b (proj3 x) - b' (proj3 y))]
  · simp [embedU]

lemma norm_embedU_le (a : Pt 2 → Pt 2) (b : Pt 2 → ℝ) (x : Pt 3) :
    ‖embedU a b x‖ ≤ ‖a (proj3 x)‖ + ‖b (proj3 x)‖ := by
  have := norm_embedU_sub_le a 0 b 0 x x
  simp only [Pi.zero_apply, sub_zero] at this
  have e : embedU (0 : Pt 2 → Pt 2) (0 : Pt 2 → ℝ) x = 0 := by
    ext k; fin_cases k <;> simp [embedU]
  rwa [e, sub_zero] at this

omit [NormedSpace ℝ E] in
lemma bddOn_congr {d : ℕ} {F G : ℝ → Pt d → E} (h : ∀ t ∈ Icc 0 T, F t = G t)
    (hG : BddOn T G) : BddOn T F := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun t ht x => by rw [h t ht]; exact hC t ht x⟩

omit [NormedSpace ℝ E] in
lemma parHolder_congr {d : ℕ} {F G : ℝ → Pt d → E} (h : ∀ t ∈ Icc 0 T, F t = G t)
    (hG : ParHolder T β G) : ParHolder T β F := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun t ht s hs x y => by rw [h t ht, h s hs]; exact hC t ht s hs x y⟩

omit [NormedSpace ℝ E] in
lemma timeHolder_congr {d : ℕ} {F G : ℝ → Pt d → E} (h : ∀ t ∈ Icc 0 T, F t = G t)
    (hG : TimeHolder T γ G) : TimeHolder T γ F := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun t ht s hs x => by rw [h t ht, h s hs]; exact hC t ht s hs x⟩

omit [NormedSpace ℝ E] in
lemma bddOn_zero {d : ℕ} : BddOn T (fun (_ : ℝ) (_ : Pt d) => (0 : E)) :=
  ⟨0, fun _ _ _ => by simp⟩

omit [NormedSpace ℝ E] in
lemma parHolder_zero {d : ℕ} : ParHolder T β (fun (_ : ℝ) (_ : Pt d) => (0 : E)) :=
  ⟨0, fun _ _ _ _ _ _ => by simp⟩

omit [NormedSpace ℝ E] in
lemma timeHolder_zero {d : ℕ} : TimeHolder T γ (fun (_ : ℝ) (_ : Pt d) => (0 : E)) :=
  ⟨0, fun _ _ _ _ _ => by simp⟩

omit [NormedSpace ℝ E] in
lemma bddOn_comp_proj3 {g : ℝ → Pt 2 → E} (hg : BddOn T g) :
    BddOn T (fun t x => g t (proj3 x)) := by
  obtain ⟨C, hC⟩ := hg
  exact ⟨C, fun t ht x => hC t ht _⟩

omit [NormedSpace ℝ E] in
lemma timeHolder_comp_proj3 {g : ℝ → Pt 2 → E} (hg : TimeHolder T γ g) :
    TimeHolder T γ (fun t x => g t (proj3 x)) := by
  obtain ⟨C, hC⟩ := hg
  exact ⟨C, fun t ht s hs x => hC t ht s hs _⟩

omit [NormedSpace ℝ E] in
lemma parHolder_comp_proj3 (hβ : 0 ≤ β) {g : ℝ → Pt 2 → E} (hg : ParHolder T β g) :
    ParHolder T β (fun t x => g t (proj3 x)) := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨|C|, fun t ht s hs x y => ?_⟩
  have h1 := hC t ht s hs (proj3 x) (proj3 y)
  have h2 : ‖proj3 x - proj3 y‖ ^ β ≤ ‖x - y‖ ^ β := by
    rw [← proj3_sub]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_proj3_le _) hβ
  have hP : 0 ≤ ‖proj3 x - proj3 y‖ ^ β + |t - s| ^ (β / 2) := by positivity
  calc ‖g t (proj3 x) - g s (proj3 y)‖ ≤ C * (‖proj3 x - proj3 y‖ ^ β + |t - s| ^ (β / 2)) := h1
    _ ≤ |C| * (‖proj3 x - proj3 y‖ ^ β + |t - s| ^ (β / 2)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hP
    _ ≤ |C| * (‖x - y‖ ^ β + |t - s| ^ (β / 2)) := by gcongr

lemma bddOn_embedU {a : ℝ → Pt 2 → Pt 2} {b : ℝ → Pt 2 → ℝ} (ha : BddOn T a) (hb : BddOn T b) :
    BddOn T (fun t => embedU (a t) (b t)) := by
  obtain ⟨C₁, h₁⟩ := ha
  obtain ⟨C₂, h₂⟩ := hb
  exact ⟨C₁ + C₂, fun t ht x => (norm_embedU_le _ _ x).trans (add_le_add (h₁ t ht _) (h₂ t ht _))⟩

lemma timeHolder_embedU {a : ℝ → Pt 2 → Pt 2} {b : ℝ → Pt 2 → ℝ} (ha : TimeHolder T γ a)
    (hb : TimeHolder T γ b) : TimeHolder T γ (fun t => embedU (a t) (b t)) := by
  obtain ⟨C₁, h₁⟩ := ha
  obtain ⟨C₂, h₂⟩ := hb
  exact ⟨C₁ + C₂, fun t ht s hs x => (norm_embedU_sub_le _ _ _ _ x x).trans
    (by rw [add_mul]; exact add_le_add (h₁ t ht s hs _) (h₂ t ht s hs _))⟩

lemma parHolder_embedU (hβ : 0 ≤ β) {a : ℝ → Pt 2 → Pt 2} {b : ℝ → Pt 2 → ℝ}
    (ha : ParHolder T β a) (hb : ParHolder T β b) :
    ParHolder T β (fun t => embedU (a t) (b t)) := by
  obtain ⟨C₁, h₁⟩ := parHolder_comp_proj3 hβ ha
  obtain ⟨C₂, h₂⟩ := parHolder_comp_proj3 hβ hb
  exact ⟨C₁ + C₂, fun t ht s hs x y => (norm_embedU_sub_le _ _ _ _ x y).trans
    (by rw [add_mul]; exact add_le_add (h₁ t ht s hs x y) (h₂ t ht s hs x y))⟩

end holder

section transfer
variable {T β : ℝ} {v : ℝ → Pt 2 → Pt 2} {θ : ℝ → Pt 2 → ℝ}

lemma dt_embedU (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hv : ∀ x, DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hθ : ∀ x, DifferentiableWithinAt ℝ (fun s => θ s x) (Icc 0 T) t) (x : Pt 3) :
    dt T (fun s => embedU (v s) (θ s)) t x = embedU (dt T v t) (dt T θ t) x := by
  unfold dt
  apply HasDerivWithinAt.derivWithin _ (uniqueDiffOn_Icc hT t ht)
  rw [hasDerivWithinAt_pi]
  intro k
  have hv' := (hv (proj3 x)).hasDerivWithinAt
  have hθ' := (hθ (proj3 x)).hasDerivWithinAt
  fin_cases k
  · exact (hasDerivWithinAt_pi.1 hv') 0
  · exact (hasDerivWithinAt_pi.1 hv') 1
  · exact hθ'

lemma diff_t_embedU {t : ℝ}
    (hv : ∀ x, DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hθ : ∀ x, DifferentiableWithinAt ℝ (fun s => θ s x) (Icc 0 T) t) (x : Pt 3) :
    DifferentiableWithinAt ℝ (fun s => embedU (v s) (θ s) x) (Icc 0 T) t := by
  rw [differentiableWithinAt_pi]
  intro k
  fin_cases k
  · exact (differentiableWithinAt_pi.1 (hv (proj3 x))) 0
  · exact (differentiableWithinAt_pi.1 (hv (proj3 x))) 1
  · exact hθ (proj3 x)

lemma pd_embedU_last' {v' : Pt 2 → Pt 2} {θ' : Pt 2 → ℝ} (hv : Differentiable ℝ v')
    (hθ : Differentiable ℝ θ') : pd (Fin.last 2) (embedU v' θ') = 0 :=
  pd_embedU_last hv hθ

theorem parabolicC12_embedU (hT : 0 < T) (hβ : 0 < β) (hv : IsParabolicC12 T β v)
    (hθ : IsParabolicC12 T β θ) : IsParabolicC12 T β (fun t => embedU (v t) (θ t)) := by
  have d1 : ∀ t ∈ Icc 0 T, Differentiable ℝ (v t) := fun t ht =>
    (hv.smooth_x t ht).differentiable (by norm_num)
  have d1' : ∀ t ∈ Icc 0 T, Differentiable ℝ (θ t) := fun t ht =>
    (hθ.smooth_x t ht).differentiable (by norm_num)
  refine ⟨fun t ht => contDiff_embedU (hv.smooth_x t ht) (hθ.smooth_x t ht),
    fun x t ht => diff_t_embedU (fun y => hv.diff_t y t ht) (fun y => hθ.diff_t y t ht) x,
    bddOn_embedU hv.bdd hθ.bdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bddOn_congr (fun t ht => funext (dt_embedU hT ht (fun y => hv.diff_t y t ht)
      (fun y => hθ.diff_t y t ht))) (bddOn_embedU hv.bdd_dt hθ.bdd_dt)
  · exact parHolder_congr (fun t ht => funext (dt_embedU hT ht (fun y => hv.diff_t y t ht)
      (fun y => hθ.diff_t y t ht))) (parHolder_embedU hβ.le hv.holder_dt hθ.holder_dt)
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · exact bddOn_congr (fun t ht => pd_embedU_cast (d1 t ht) (d1' t ht) i')
        (bddOn_embedU (hv.bdd_d1 i') (hθ.bdd_d1 i'))
    · exact bddOn_congr (fun t ht => pd_embedU_last' (d1 t ht) (d1' t ht)) bddOn_zero
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · exact timeHolder_congr (fun t ht => pd_embedU_cast (d1 t ht) (d1' t ht) i')
        (timeHolder_embedU (hv.holder_d1_time i') (hθ.holder_d1_time i'))
    · exact timeHolder_congr (fun t ht => pd_embedU_last' (d1 t ht) (d1' t ht)) timeHolder_zero
  · intro i j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · refine bddOn_congr (fun t ht => ?_) (bddOn_embedU (hv.bdd_d2 i' j') (hθ.bdd_d2 i' j'))
        rw [pd_embedU_cast (d1 t ht) (d1' t ht) j', pd_embedU_cast
          (differentiable_pd (hv.smooth_x t ht) j') (differentiable_pd (hθ.smooth_x t ht) j') i']
      · refine bddOn_congr (fun t ht => ?_) bddOn_zero
        rw [pd_embedU_cast (d1 t ht) (d1' t ht) j', pd_embedU_last'
          (differentiable_pd (hv.smooth_x t ht) j') (differentiable_pd (hθ.smooth_x t ht) j')]
        rfl
    · refine bddOn_congr (fun t ht => ?_) bddOn_zero
      rw [pd_embedU_last' (d1 t ht) (d1' t ht), pd_zero_fun]
      rfl
  · intro i j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · refine parHolder_congr (fun t ht => ?_)
          (parHolder_embedU hβ.le (hv.holder_d2 i' j') (hθ.holder_d2 i' j'))
        rw [pd_embedU_cast (d1 t ht) (d1' t ht) j', pd_embedU_cast
          (differentiable_pd (hv.smooth_x t ht) j') (differentiable_pd (hθ.smooth_x t ht) j') i']
      · refine parHolder_congr (fun t ht => ?_) parHolder_zero
        rw [pd_embedU_cast (d1 t ht) (d1' t ht) j', pd_embedU_last'
          (differentiable_pd (hv.smooth_x t ht) j') (differentiable_pd (hθ.smooth_x t ht) j')]
        rfl
    · refine parHolder_congr (fun t ht => ?_) parHolder_zero
      rw [pd_embedU_last' (d1 t ht) (d1' t ht), pd_zero_fun]
      rfl

theorem parabolicC01_comp_proj3 (hβ : 0 < β) {p : ℝ → Pt 2 → ℝ} (hp : IsParabolicC01 T β p) :
    IsParabolicC01 T β (fun t x => p t (proj3 x)) := by
  have d1 : ∀ t ∈ Icc 0 T, Differentiable ℝ (p t) := fun t ht =>
    (hp.smooth_x t ht).differentiable (by norm_num)
  refine ⟨fun t ht => (hp.smooth_x t ht).comp contDiff_proj3, bddOn_comp_proj3 hp.bdd,
    timeHolder_comp_proj3 hp.holder_time, ?_, ?_⟩
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · exact bddOn_congr (fun t ht => pd_comp_proj3_fun_cast _ (d1 t ht) i')
        (bddOn_comp_proj3 (hp.bdd_d1 i'))
    · exact bddOn_congr (fun t ht => pd_comp_proj3_fun_last _ (d1 t ht)) bddOn_zero
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · exact parHolder_congr (fun t ht => pd_comp_proj3_fun_cast _ (d1 t ht) i')
        (parHolder_comp_proj3 hβ.le (hp.holder_d1 i'))
    · exact parHolder_congr (fun t ht => pd_comp_proj3_fun_last _ (d1 t ht)) parHolder_zero

end transfer

end AnomDiss
