module

public import RequestProject.Markov

/-!
# Lemma 7.2: residue classes

Complex-valued classical solutions of the advection–diffusion equation are built from real ones
(External Result 1.6 is stated for real data), and are unique.  Since the pulse drift
`V_j^ν` is `k_j⁻¹ℤ²`-periodic, translating a solution by `k_j⁻¹ e_i` and multiplying by a phase
gives another solution; uniqueness then forces the Fourier coefficients of `T e_ℓ` to vanish
outside the residue class `ℓ + k_jℤ²`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {T β γ : ℝ}

/-! ### Bounds and Hölder conditions under linear maps, sums and translations -/

lemma BddOn.clm {g : ℝ → Pt d → E} (h : BddOn T g) (L : E →L[ℝ] F) :
    BddOn T (fun t x => L (g t x)) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨‖L‖ * C, fun t ht x =>
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC t ht x) (norm_nonneg _))⟩

lemma ParHolder.clm {g : ℝ → Pt d → E} (h : ParHolder T β g) (L : E →L[ℝ] F) :
    ParHolder T β (fun t x => L (g t x)) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖L‖ * C, fun t ht s hs x y => ?_⟩
  rw [← map_sub, mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC t ht s hs x y) (norm_nonneg _))

lemma TimeHolder.clm {g : ℝ → Pt d → E} (h : TimeHolder T γ g) (L : E →L[ℝ] F) :
    TimeHolder T γ (fun t x => L (g t x)) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖L‖ * C, fun t ht s hs x => ?_⟩
  rw [← map_sub, mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC t ht s hs x) (norm_nonneg _))

omit [NormedSpace ℝ E] in
lemma BddOn.add {g g' : ℝ → Pt d → E} (h : BddOn T g) (h' : BddOn T g') :
    BddOn T (fun t x => g t x + g' t x) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  exact ⟨C + C', fun t ht x => (norm_add_le _ _).trans (add_le_add (hC t ht x) (hC' t ht x))⟩

omit [NormedSpace ℝ E] in
lemma ParHolder.add {g g' : ℝ → Pt d → E} (h : ParHolder T β g) (h' : ParHolder T β g') :
    ParHolder T β (fun t x => g t x + g' t x) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', fun t ht s hs x y => ?_⟩
  rw [add_sub_add_comm, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC t ht s hs x y) (hC' t ht s hs x y))

omit [NormedSpace ℝ E] in
lemma TimeHolder.add {g g' : ℝ → Pt d → E} (h : TimeHolder T γ g) (h' : TimeHolder T γ g') :
    TimeHolder T γ (fun t x => g t x + g' t x) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', fun t ht s hs x => ?_⟩
  rw [add_sub_add_comm, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC t ht s hs x) (hC' t ht s hs x))

omit [NormedSpace ℝ E] in
lemma BddOn.translate {g : ℝ → Pt d → E} (h : BddOn T g) (c : Pt d) :
    BddOn T (fun t x => g t (x + c)) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun t ht x => hC t ht _⟩

omit [NormedSpace ℝ E] in
lemma ParHolder.translate {g : ℝ → Pt d → E} (h : ParHolder T β g) (c : Pt d) :
    ParHolder T β (fun t x => g t (x + c)) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun t ht s hs x y => ?_⟩
  have := hC t ht s hs (x + c) (y + c)
  rwa [add_sub_add_right_eq_sub] at this

omit [NormedSpace ℝ E] in
lemma TimeHolder.translate {g : ℝ → Pt d → E} (h : TimeHolder T γ g) (c : Pt d) :
    TimeHolder T γ (fun t x => g t (x + c)) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun t ht s hs x => hC t ht s hs _⟩

/-! ### Derivatives under linear maps, sums and translations -/

lemma dt_clm (hT : 0 < T) (L : E →L[ℝ] F) (u : ℝ → Pt d → E) (x : Pt d) {t : ℝ}
    (ht : t ∈ Icc 0 T) (hd : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t) :
    dt T (fun s y => L (u s y)) t x = L (dt T u t x) := by
  unfold dt
  exact (L.hasFDerivAt.comp_hasDerivWithinAt t hd.hasDerivWithinAt).derivWithin
    (uniqueDiffOn_Icc hT t ht)

lemma dt_add (hT : 0 < T) (u u' : ℝ → Pt d → E) (x : Pt d) {t : ℝ}
    (ht : t ∈ Icc 0 T) (hd : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hd' : DifferentiableWithinAt ℝ (fun s => u' s x) (Icc 0 T) t) :
    dt T (fun s y => u s y + u' s y) t x = dt T u t x + dt T u' t x := by
  unfold dt
  exact (hd.hasDerivWithinAt.add hd'.hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc hT t ht)

lemma pd_clm (L : E →L[ℝ] F) (f : Pt d → E) (i : Fin d) (x : Pt d)
    (hf : DifferentiableAt ℝ f x) : pd i (fun y => L (f y)) x = L (pd i f x) := by
  unfold pd
  have h : HasFDerivAt (fun y => L (f y)) (L.comp (fderiv ℝ f x)) x :=
    L.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

lemma pd_clm_fun (L : E →L[ℝ] F) (f : Pt d → E) (i : Fin d) (hf : Differentiable ℝ f) :
    pd i (fun y => L (f y)) = fun x => L (pd i f x) :=
  funext fun x => pd_clm L f i x (hf x)

lemma pd_add_fun (f g : Pt d → E) (i : Fin d) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) : pd i (fun y => f y + g y) = fun x => pd i f x + pd i g x := by
  funext x
  unfold pd
  rw [fderiv_fun_add (hf x) (hg x)]
  rfl

omit [NormedSpace ℝ E] in
lemma pd_translate [NormedSpace ℝ E] (f : Pt d → E) (i : Fin d) (c : Pt d) :
    pd i (fun y => f (y + c)) = fun x => pd i f (x + c) := by
  funext x
  unfold pd
  rw [fderiv_comp_add_right]

/-! ### Parabolic Hölder regularity under linear maps, sums and translations -/

lemma IsParabolicC12.clm (hT : 0 < T) {u : ℝ → Pt d → E} (hu : IsParabolicC12 T β u)
    (L : E →L[ℝ] F) : IsParabolicC12 T β (fun t x => L (u t x)) := by
  have hdiff : ∀ t ∈ Icc 0 T, Differentiable ℝ (u t) := fun t ht =>
    (hu.smooth_x t ht).differentiable (by norm_num)
  have hdt : ∀ t ∈ Icc 0 T, dt T (fun s y => L (u s y)) t = fun x => L (dt T u t x) :=
    fun t ht => funext fun x => dt_clm hT L u x ht (hu.diff_t x t ht)
  have hd1 : ∀ i, ∀ t ∈ Icc 0 T, pd i (fun y => L (u t y)) = fun x => L (pd i (u t) x) :=
    fun i t ht => pd_clm_fun L _ i (hdiff t ht)
  have hd2 : ∀ i j, ∀ t ∈ Icc 0 T,
      pd i (pd j (fun y => L (u t y))) = fun x => L (pd i (pd j (u t)) x) := fun i j t ht => by
    rw [hd1 j t ht]; exact pd_clm_fun L _ i (differentiable_pd (hu.smooth_x t ht) j)
  exact {
    smooth_x := fun t ht => L.contDiff.comp (hu.smooth_x t ht)
    diff_t := fun x t ht => L.differentiableAt.comp_differentiableWithinAt t (hu.diff_t x t ht)
    bdd := hu.bdd.clm L
    bdd_dt := bddOn_congr hdt (hu.bdd_dt.clm L)
    holder_dt := parHolder_congr hdt (hu.holder_dt.clm L)
    bdd_d1 := fun i => bddOn_congr (hd1 i) ((hu.bdd_d1 i).clm L)
    holder_d1_time := fun i => timeHolder_congr (hd1 i) ((hu.holder_d1_time i).clm L)
    bdd_d2 := fun i j => bddOn_congr (hd2 i j) ((hu.bdd_d2 i j).clm L)
    holder_d2 := fun i j => parHolder_congr (hd2 i j) ((hu.holder_d2 i j).clm L) }

lemma IsParabolicC12.add (hT : 0 < T) {u u' : ℝ → Pt d → E} (hu : IsParabolicC12 T β u)
    (hu' : IsParabolicC12 T β u') : IsParabolicC12 T β (fun t x => u t x + u' t x) := by
  have hdiff : ∀ t ∈ Icc 0 T, Differentiable ℝ (u t) := fun t ht =>
    (hu.smooth_x t ht).differentiable (by norm_num)
  have hdiff' : ∀ t ∈ Icc 0 T, Differentiable ℝ (u' t) := fun t ht =>
    (hu'.smooth_x t ht).differentiable (by norm_num)
  have hdt : ∀ t ∈ Icc 0 T, dt T (fun s y => u s y + u' s y) t =
      fun x => dt T u t x + dt T u' t x :=
    fun t ht => funext fun x => dt_add hT u u' x ht (hu.diff_t x t ht) (hu'.diff_t x t ht)
  have hd1 : ∀ i, ∀ t ∈ Icc 0 T, pd i (fun y => u t y + u' t y) =
      fun x => pd i (u t) x + pd i (u' t) x :=
    fun i t ht => pd_add_fun _ _ i (hdiff t ht) (hdiff' t ht)
  have hd2 : ∀ i j, ∀ t ∈ Icc 0 T, pd i (pd j (fun y => u t y + u' t y)) =
      fun x => pd i (pd j (u t)) x + pd i (pd j (u' t)) x := fun i j t ht => by
    rw [hd1 j t ht]
    exact pd_add_fun _ _ i (differentiable_pd (hu.smooth_x t ht) j)
      (differentiable_pd (hu'.smooth_x t ht) j)
  exact {
    smooth_x := fun t ht => (hu.smooth_x t ht).add (hu'.smooth_x t ht)
    diff_t := fun x t ht => (hu.diff_t x t ht).add (hu'.diff_t x t ht)
    bdd := hu.bdd.add hu'.bdd
    bdd_dt := bddOn_congr hdt (hu.bdd_dt.add hu'.bdd_dt)
    holder_dt := parHolder_congr hdt (hu.holder_dt.add hu'.holder_dt)
    bdd_d1 := fun i => bddOn_congr (hd1 i) ((hu.bdd_d1 i).add (hu'.bdd_d1 i))
    holder_d1_time := fun i => timeHolder_congr (hd1 i)
      ((hu.holder_d1_time i).add (hu'.holder_d1_time i))
    bdd_d2 := fun i j => bddOn_congr (hd2 i j) ((hu.bdd_d2 i j).add (hu'.bdd_d2 i j))
    holder_d2 := fun i j => parHolder_congr (hd2 i j) ((hu.holder_d2 i j).add (hu'.holder_d2 i j)) }

lemma IsParabolicC12.translate {u : ℝ → Pt d → E} (hu : IsParabolicC12 T β u) (c : Pt d) :
    IsParabolicC12 T β (fun t x => u t (x + c)) := by
  have hd1 : ∀ i, ∀ t ∈ Icc 0 T, pd i (fun y => u t (y + c)) = fun x => pd i (u t) (x + c) :=
    fun i t _ => pd_translate _ i c
  have hd2 : ∀ i j, ∀ t ∈ Icc 0 T,
      pd i (pd j (fun y => u t (y + c))) = fun x => pd i (pd j (u t)) (x + c) := fun i j t ht => by
    rw [hd1 j t ht]; exact pd_translate _ i c
  exact {
    smooth_x := fun t ht => (hu.smooth_x t ht).comp (contDiff_id.add contDiff_const)
    diff_t := fun x t ht => hu.diff_t (x + c) t ht
    bdd := hu.bdd.translate c
    bdd_dt := hu.bdd_dt.translate c
    holder_dt := hu.holder_dt.translate c
    bdd_d1 := fun i => bddOn_congr (hd1 i) ((hu.bdd_d1 i).translate c)
    holder_d1_time := fun i => timeHolder_congr (hd1 i) ((hu.holder_d1_time i).translate c)
    bdd_d2 := fun i j => bddOn_congr (hd2 i j) ((hu.bdd_d2 i j).translate c)
    holder_d2 := fun i j => parHolder_congr (hd2 i j) ((hu.holder_d2 i j).translate c) }

/-! ### Classical scalar solutions under linear maps, sums and translations -/

variable {ν : ℝ} {v : ℝ → Pt d → Pt d}

lemma IsClassicalScalar.clm (hT : 0 < T) {θ₀ : Pt d → E} {θ : ℝ → Pt d → E}
    (h : IsClassicalScalar T ν v θ₀ θ) (L : E →L[ℝ] F) :
    IsClassicalScalar T ν v (fun x => L (θ₀ x)) (fun t x => L (θ t x)) := by
  obtain ⟨β, hβ0, hβ1, reg⟩ := h.regular
  refine ⟨fun t ht x n => by simp only [h.periodic t ht x n], ⟨β, hβ0, hβ1, reg.clm hT L⟩,
    by simp only [h.init], fun t ht x => ?_⟩
  have hdiff : Differentiable ℝ (θ t) := (reg.smooth_x t ht).differentiable (by norm_num)
  have hd1 : ∀ i, pd i (fun y => L (θ t y)) = fun x => L (pd i (θ t) x) :=
    fun i => pd_clm_fun L _ i hdiff
  have hd2 : ∀ i, pd i (pd i (fun y => L (θ t y))) = fun x => L (pd i (pd i (θ t)) x) :=
    fun i => by rw [hd1 i]; exact pd_clm_fun L _ i (differentiable_pd (reg.smooth_x t ht) i)
  have e := congrArg L (h.eqn t ht x)
  rw [dt_clm hT L θ x ht (reg.diff_t x t ht)]
  simp only [lap]
  simp only [hd2]
  simp only [conv, lap, hd1, map_add, map_smul, map_sum] at e ⊢
  exact e

lemma IsClassicalScalar.add (hT : 0 < T) (hβ0 : 0 < β) (hβ1 : β < 1) {θ₀ θ₀' : Pt d → E}
    {θ θ' : ℝ → Pt d → E} (h : IsClassicalScalar T ν v θ₀ θ) (h' : IsClassicalScalar T ν v θ₀' θ')
    (reg : IsParabolicC12 T β θ) (reg' : IsParabolicC12 T β θ') :
    IsClassicalScalar T ν v (fun x => θ₀ x + θ₀' x) (fun t x => θ t x + θ' t x) := by
  refine ⟨fun t ht x n => by simp only [h.periodic t ht x n, h'.periodic t ht x n],
    ⟨β, hβ0, hβ1, reg.add hT reg'⟩,
    by simp only [h.init, h'.init], fun t ht x => ?_⟩
  have hdiff : Differentiable ℝ (θ t) := (reg.smooth_x t ht).differentiable (by norm_num)
  have hdiff' : Differentiable ℝ (θ' t) := (reg'.smooth_x t ht).differentiable (by norm_num)
  have hd1 : ∀ i, pd i (fun y => θ t y + θ' t y) = fun x => pd i (θ t) x + pd i (θ' t) x :=
    fun i => pd_add_fun _ _ i hdiff hdiff'
  have hd2 : ∀ i, pd i (pd i (fun y => θ t y + θ' t y)) =
      fun x => pd i (pd i (θ t)) x + pd i (pd i (θ' t)) x := fun i => by
    rw [hd1 i]
    exact pd_add_fun _ _ i (differentiable_pd (reg.smooth_x t ht) i)
      (differentiable_pd (reg'.smooth_x t ht) i)
  have e := h.eqn t ht x
  have e' := h'.eqn t ht x
  rw [dt_add hT θ θ' x ht (reg.diff_t x t ht) (reg'.diff_t x t ht)]
  simp only [lap]
  simp only [hd2]
  simp only [conv, lap, hd1, smul_add, Finset.sum_add_distrib] at e e' ⊢
  rw [← e, ← e']
  abel

lemma IsClassicalScalar.translate {θ₀ : Pt d → E} {θ : ℝ → Pt d → E}
    (h : IsClassicalScalar T ν v θ₀ θ) (c : Pt d) (hv : ∀ t ∈ Icc 0 T, ∀ x, v t (x + c) = v t x) :
    IsClassicalScalar T ν v (fun x => θ₀ (x + c)) (fun t x => θ t (x + c)) := by
  obtain ⟨β, hβ0, hβ1, reg⟩ := h.regular
  refine ⟨fun t ht x n => by simp only [add_right_comm x _ c, h.periodic t ht (x + c) n],
    ⟨β, hβ0, hβ1, reg.translate c⟩, by simp only [h.init], fun t ht x => ?_⟩
  have e := h.eqn t ht (x + c)
  show dt T θ t (x + c) + conv (v t) (fun y => θ t (y + c)) x = ν • lap (fun y => θ t (y + c)) x
  simp only [conv, lap, pd_translate, hv t ht x] at e ⊢
  exact e

/-! ### Complex-valued solutions -/

lemma complex_scalar_unique {T ν : ℝ} (hT : 0 < T) (hν : 0 ≤ ν) (v : ℝ → Pt 2 → Pt 2)
    (θ₀ : Pt 2 → ℂ) (θ θ' : ℝ → Pt 2 → ℂ) (h : IsClassicalScalar T ν v θ₀ θ)
    (h' : IsClassicalScalar T ν v θ₀ θ') : ∀ t ∈ Icc 0 T, θ t = θ' t := by
  intro t ht
  funext x
  have hre := congrFun (classical_scalar_unique T ν hν v _ _ _ (h.clm hT Complex.reCLM)
    (h'.clm hT Complex.reCLM) t ht) x
  have him := congrFun (classical_scalar_unique T ν hν v _ _ _ (h.clm hT Complex.imCLM)
    (h'.clm hT Complex.imCLM) t ht) x
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  exact Complex.ext hre him

lemma complex_scalar_exists (hSc : ExternalScalar) {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (v : ℝ → Pt 2 → Pt 2) (hvper : ∀ t ∈ Icc 0 T, IsPeriodic (v t))
    (hvreg : IsParabolicC01 T (1 / 2) v) (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0)
    (θ₀ : Pt 2 → ℂ) (hθ₀ : ContDiff ℝ ∞ θ₀) (hp : IsPeriodic θ₀) :
    ∃ θ, IsParabolicC12 T (1 / 2) θ ∧ IsClassicalScalar T ν v θ₀ θ := by
  have hre : ContDiff ℝ ∞ (fun x => (θ₀ x).re) := Complex.reCLM.contDiff.comp hθ₀
  have him : ContDiff ℝ ∞ (fun x => (θ₀ x).im) := Complex.imCLM.contDiff.comp hθ₀
  have hpre : IsPeriodic (fun x => (θ₀ x).re) := fun x n => by simp only [hp x n]
  have hpim : IsPeriodic (fun x => (θ₀ x).im) := fun x n => by simp only [hp x n]
  obtain ⟨a, ha1, ha2⟩ := stage_exists hSc hT hν v hvper hvreg hvdiv _ hpre
    (holderC2_of_smooth_periodic _ hre hpre (by norm_num) (by norm_num))
  obtain ⟨b, hb1, hb2⟩ := stage_exists hSc hT hν v hvper hvreg hvdiv _ hpim
    (holderC2_of_smooth_periodic _ him hpim (by norm_num) (by norm_num))
  set L1 : ℝ →L[ℝ] ℂ := Complex.ofRealCLM
  set L2 : ℝ →L[ℝ] ℂ := Complex.I • Complex.ofRealCLM
  have hsum := (ha2.clm hT L1).add hT (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (hb2.clm hT L2) (ha1.clm hT L1) (hb1.clm hT L2)
  have e : (fun x => L1 (θ₀ x).re + L2 (θ₀ x).im) = θ₀ := by
    funext x
    apply Complex.ext <;> simp [L1, L2]
  have hreg := (ha1.clm hT L1).add hT (hb1.clm hT L2)
  rw [e] at hsum
  exact ⟨_, hreg, hsum⟩

/-! ### Translation invariance of the cell integral -/

lemma integral_cell_add_right (g : Pt 2 → ℂ) (hg : Continuous g) (hp : IsPeriodic g) (c : Pt 2) :
    ∫ x in cell 2, g (x + c) = ∫ x in cell 2, g x := by
  have hpn : IsPeriodic (fun z => g (-z)) := fun x n => by
    show g (-(x + intVec n)) = g (-x)
    rw [neg_add, ← intVec_neg, hp]
  have h1 := map_cell_sub_left (fun z => g (-z)) (hg.comp continuous_neg) hpn (-c)
  have h2 := map_cell_sub_left g hg hp 0
  have e1 : (fun z => g (-(-c - z))) = fun z => g (z + c) := by
    funext z; congr 1; abel
  have e2 : (fun z => g (0 - z)) = fun z => g (-z) := by
    funext z; rw [zero_sub]
  rw [e1] at h1
  rw [e2] at h2
  have hmap := h1.trans h2
  have := congrArg (fun μ : Measure ℂ => ∫ y, y ∂μ) hmap
  rw [integral_map (show AEMeasurable (fun z => g (z + c)) _ from
      (hg.comp (continuous_id.add continuous_const)).aemeasurable)
      measurable_id'.aestronglyMeasurable,
    integral_map hg.aemeasurable measurable_id'.aestronglyMeasurable] at this
  exact this

/-! ### Characters -/


lemma contDiff_expChar (ξ : Pt 2) : ContDiff ℝ ∞ (expChar ξ) := by
  have hd : ContDiff ℝ ∞ (fun y : Pt 2 => dot ξ y) := by
    unfold dot
    exact ContDiff.sum (s := Finset.univ) fun i _ =>
      contDiff_const.mul (contDiff_apply ℝ ℝ i : ContDiff ℝ ∞ fun y : Pt 2 => y i)
  unfold expChar
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hd))



lemma expChar_shift (ξ : Pt 2) (k : ℝ) (i : Fin 2) :
    expChar ξ (k⁻¹ • (Pi.single i (1 : ℝ) : Pt 2)) = Complex.exp (2 * π * Complex.I * ((ξ i / k : ℝ) : ℂ)) := by
  unfold expChar
  congr 3
  simp only [dot, Fin.sum_univ_two]
  fin_cases i <;> simp [div_eq_mul_inv, mul_comm]

lemma dvd_of_exp_eq_one {a : ℤ} {k : ℕ} (hk : 0 < k)
    (h : Complex.exp (2 * π * Complex.I * (((a : ℝ) / k : ℝ) : ℂ)) = 1) : (k : ℤ) ∣ a := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have hπ : (2 * π * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have h1 : (((a : ℝ) / k : ℝ) : ℂ) = n := by
    have := hn
    rw [mul_comm (n : ℂ)] at this
    exact mul_left_cancel₀ hπ this
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have h2 : (a : ℝ) = n * k := by
    have := congrArg Complex.re h1
    simp at this
    field_simp at this
    linarith
  have h3 : a = (k : ℤ) * n := by
    have : (a : ℝ) = (((k : ℤ) * n : ℤ) : ℝ) := by rw [h2]; push_cast; ring
    exact_mod_cast this
  exact Dvd.intro n h3.symm

/-! ### Lemma 7.2 -/

/-- **Lemma 7.2** (residue classes).  `⟨T e_ℓ, e_m⟩ = 0` unless `m - ℓ ∈ k_j ℤ²`. -/
theorem residue_classes (hSc : ExternalScalar) (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (b : BlockParam L₀) (ℓ m : Fin 2 → ℤ) (h : ¬ ∃ n : Fin 2 → ℤ, m - ℓ = (qq ^ j : ℤ) • n) :
    pulseEntry N j b ℓ m = 0 := by
  have hν := viscosity_properties.2.2.1 N (hj.trans hjN)
  have hT := δs_pos j hj
  have hTmem : δs j ∈ Icc 0 (δs j) := ⟨hT.le, le_rfl⟩
  set k : ℕ := qq ^ j with hk
  have hk0 : 0 < k := by have := qq_ge; positivity
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  set v : ℝ → Pt 2 → Pt 2 := fun t => VpulseB (nuN N) j b (sj j + t) with hv
  have hD := vpulse_stage_props (nuN N) (fun _ => b) j
  have hvreg : IsParabolicC01 (δs j) (1 / 2) v :=
    parabolicC01_of_contDiff hT.le (by norm_num) (by norm_num) _ hD.2.1 hD.1
  obtain ⟨θ, -, hθ⟩ := complex_scalar_exists hSc hT hν v (fun t _ => hD.1 t) hvreg
    (fun t _ => hD.2.2 t) _ (contDiff_expChar _) (isPeriodic_expChar ℓ)
  have hout : pulseOp N j b (expChar (intVec ℓ)) = θ (δs j) := by
    have hex : ∃ out, ∃ θ' : ℝ → Pt 2 → ℂ, IsClassicalScalar (δs j) (nuN N)
        (fun t => VpulseB (nuN N) j b (sj j + t)) (expChar (intVec ℓ)) θ' ∧ θ' (δs j) = out :=
      ⟨_, θ, hθ, rfl⟩
    obtain ⟨θ', hθ', he⟩ := Classical.epsilon_spec hex
    unfold pulseOp
    rw [← he]
    exact complex_scalar_unique hT hν.le v _ θ' θ hθ' hθ _ hTmem
  -- the drift is invariant under translation by `k⁻¹ e_i`
  have hvshift : ∀ i : Fin 2, ∀ t x,
      v t (x + (k : ℝ)⁻¹ • (Pi.single i (1 : ℝ) : Pt 2)) = v t x := by
    intro i t x
    have e := fun y => congrFun (congrFun (vpulse_stage_eq (nuN N) (fun _ => b) j) t) y
    show Vpulse (nuN N) (fun _ => b) j (sj j + t) _ = Vpulse (nuN N) (fun _ => b) j (sj j + t) x
    rw [e, e]
    have hsh : ((qq ^ j : ℕ) : ℝ) • (x + (k : ℝ)⁻¹ • (Pi.single i (1 : ℝ) : Pt 2)) - b.2 =
        (((qq ^ j : ℕ) : ℝ) • x - b.2) + intVec (Pi.single i 1) := by
      funext l
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, intVec]
      rw [← hk]
      by_cases hl : l = i
      · subst hl; simp; field_simp; ring
      · simp [hl]
    rw [hsh, (eigenspace_properties _).2.1]
  -- the output is quasi-periodic under these translations
  set out := θ (δs j) with hout_def
  obtain ⟨β, -, -, hθreg⟩ := hθ.regular
  have houtc : Continuous out := (hθreg.smooth_x _ hTmem).continuous
  have houtp : IsPeriodic out := hθ.periodic _ hTmem
  have hquasi : ∀ i : Fin 2, ∀ x, out (x + (k : ℝ)⁻¹ • (Pi.single i (1 : ℝ) : Pt 2)) =
      expChar (intVec ℓ) ((k : ℝ)⁻¹ • (Pi.single i (1 : ℝ) : Pt 2)) * out x := by
    intro i x
    set c : Pt 2 := (k : ℝ)⁻¹ • (Pi.single i (1 : ℝ) : Pt 2) with hc
    set μ := (expChar (intVec ℓ) c)⁻¹ with hμ
    have hne : expChar (intVec ℓ) c ≠ 0 := Complex.exp_ne_zero _
    have hθ2 := (hθ.translate c (fun t _ y => hvshift i t y)).clm hT
      (ContinuousLinearMap.mul ℝ ℂ μ)
    have hinit : (fun y => ContinuousLinearMap.mul ℝ ℂ μ (expChar (intVec ℓ) (y + c))) =
        expChar (intVec ℓ) := by
      funext y
      rw [ContinuousLinearMap.mul_apply', expChar_add_right, hμ]
      field_simp
    rw [hinit] at hθ2
    have := congrFun (complex_scalar_unique hT hν.le v _ _ _ hθ2 hθ _ hTmem) x
    rw [ContinuousLinearMap.mul_apply', hμ] at this
    rw [hout_def, ← this, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  -- choose a coordinate where `m - ℓ` is not divisible by `k`
  obtain ⟨i, hi⟩ : ∃ i, ¬ (k : ℤ) ∣ (m - ℓ) i := by
    by_contra hcon
    push_neg at hcon
    refine h ⟨fun i => (m - ℓ) i / k, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast [hk] at hcon ⊢
    rw [Int.mul_ediv_cancel' (hcon i)]
  set c : Pt 2 := (k : ℝ)⁻¹ • (Pi.single i (1 : ℝ) : Pt 2) with hc
  set F : Pt 2 → ℂ := fun x => out x * expChar (-intVec m) x with hFdef
  have hFc : Continuous F := houtc.mul (continuous_expChar _)
  have hFp : IsPeriodic F := fun x n => by
    simp only [hFdef, houtp x n, ← intVec_neg, isPeriodic_expChar (-m) x n]
  have hF := integral_cell_add_right F hFc hFp c
  set ζ := expChar (intVec ℓ) c * expChar (-intVec m) c with hζ
  have hFx : ∀ x, F (x + c) = ζ * F x := by
    intro x
    have hq : out (x + c) = expChar (intVec ℓ) c * out x := hquasi i x
    simp only [hFdef, hζ]
    rw [hq, expChar_add_right]
    ring
  simp only [hFx] at hF
  rw [integral_const_mul] at hF
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [hζ, expChar_mul, hc, expChar_shift] at h1
    have h2 : ((intVec ℓ + -intVec m) i / (k : ℝ)) = (((ℓ - m) i : ℤ) : ℝ) / k := by
      simp [intVec, sub_eq_add_neg]
    rw [h2] at h1
    have := dvd_of_exp_eq_one hk0 h1
    apply hi
    have e : (m - ℓ) i = -((ℓ - m) i) := by simp
    rw [e]
    exact (dvd_neg).2 this
  unfold pulseEntry
  rw [hout]
  have hfc : fc out m = ∫ x in cell 2, F x := rfl
  rw [hfc]
  have h3 : (ζ - 1) * ∫ x in cell 2, F x = 0 := by rw [sub_mul, hF, one_mul, sub_self]
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4) hζ1
  · exact h4

end AnomDiss
