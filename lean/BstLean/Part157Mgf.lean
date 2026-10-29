import BstLean.Part157Charges

/-!
# Part 157, item 5: the indicator inequality `GaussFrameMGF` from the inequality (GP)

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, Lemma `t7:p02:GP` and Corollary `t7:p02:MGF`.

* `GaussGP`: the statement of Lemma `t7:p02:GP` for the maps `B_x G = G e(x)` (`G` a Gaussian
  matrix, `e(x)` a unit vector or `0`): for a jointly measurable `f` with `0 < a ≤ f ≤ b`,
  `E_G exp(L⁻¹ ∫ log f(x, G e(x)) dμ) ≤ exp(L⁻¹ ∫ log E_Z f(x, Z) dμ)`. A NAMED HYPOTHESIS
  (the geometric Brascamp–Lieb inequality for the Gaussian measure, continuous family). It is
  NOT proved in Lean.
* **`mgf_of_gp`**: `GaussGP → GaussFrameMGF`. This is the proof of Corollary `t7:p02:MGF` from
  Lemma `t7:p02:GP` (take `f = exp(s·1_S)`, then Jensen's inequality for the logarithm).
* `gaussMat_scale`: a Gaussian matrix with entry variance `v` is `√v` times a standard one.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156

/-- **The inequality (GP) for the maps `B_x G = G e(x)` (a named hypothesis; no network).**
`μ` is a probability measure on the inputs `x ∈ ℝ^N`; `e(x) ∈ ℝ^m` is measurable, a unit vector
or `0`; `G` is a matrix with `q` rows and `m` columns of independent standard Gaussian entries;
`f(x, z)` is jointly measurable with `0 < a ≤ f ≤ b`, and `f(x, ·)` is constant where
`e(x) = 0`. IF `∫ ⟨e(x), w⟩² dμ ≤ L·|w|²` for every `w`, with `L > 0`, THEN
`E_G exp(L⁻¹ ∫ log f(x, G e(x)) dμ(x)) ≤ exp(L⁻¹ ∫ log E_Z f(x, Z) dμ(x))`, `Z` a standard
Gaussian vector of `ℝ^q`.

Paper statement: `theorem7-02-world.tex`, Lemma `t7:p02:GP`, formula `t7:p02:GP-equation`, with
`D = q·m`, `d = q` and `B_x G = G e(x)` (then `B_x B_xᵀ = I_q` on the active set and
`∫ B_xᵀ B_x dμ = I_q ⊗ ∫ e eᵀ dμ`). -/
def GaussGP : Prop :=
  ∀ (N q m : ℕ) (μ : Measure (Fin N → ℝ)), IsProbabilityMeasure μ →
    ∀ (e : (Fin N → ℝ) → Fin m → ℝ), Measurable e → (∀ x, normSq (e x) = 1 ∨ e x = 0) →
    ∀ (f : (Fin N → ℝ) × (Fin q → ℝ) → ℝ), Measurable f →
    ∀ a b : ℝ, 0 < a → (∀ y, a ≤ f y) → (∀ y, f y ≤ b) →
    (∀ x, e x = 0 → ∀ z, f (x, z) = f (x, 0)) →
    ∀ L : ℝ, 0 < L →
    (∀ w : Fin m → ℝ, ∫ x, (∑ j, e x j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) →
    ∫ G, exp (1 / L * ∫ x, log (f (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 ≤
      exp (1 / L * ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ)

/-- The integral of an indicator of a preimage. -/
lemma integral_indicator_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {S : Set β} (hS : MeasurableSet S) :
    ∫ x, S.indicator (1 : β → ℝ) (φ x) ∂μ = μ.real (φ ⁻¹' S) := by
  rw [← integral_indicator_one (hφ hS)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases h : φ x ∈ S
  · have h' : x ∈ φ ⁻¹' S := h
    simp [h, h']
  · have h' : x ∉ φ ⁻¹' S := h
    simp [h, h']

/-- The residual is its length times its unit direction. -/
lemma res_eq_smul_eDir {m : ℕ} (b h : Fin m → ℝ) :
    res b h = √(normSq (res b h)) • eDir b h := by
  unfold eDir
  by_cases h0 : normSq (res b h) = 0
  · rw [eq_zero_of_normSq h0]
    simp
  · have hs : √(normSq (res b h)) ≠ 0 :=
      (Real.sqrt_ne_zero (normSq_nonneg _)).mpr h0
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- A Gaussian matrix with entry variance `v` is `√v` times a Gaussian matrix with entry
variance `1`. -/
theorem gaussMat_scale (q m : ℕ) (v : ℝ) :
    gaussMat q m v = (gaussMat q m 1).map (fun G => √v • G) := by
  unfold gaussMat
  have m2 : Measurable (fun G : Matrix (Fin q) (Fin m) ℝ => √v • G) :=
    (continuous_const_smul (√v)).measurable
  rw [Measure.map_map m2 (measurable_ofFlat _)]
  congr 1
  funext ξ
  ext i j
  simp [Real.sqrt_one]

/-- **Corollary `t7:p02:MGF` from Lemma `t7:p02:GP`**: the inequality (GP) gives the bound of
the moment generating function of the indicator mean. -/
theorem mgf_of_gp (hGP : GaussGP) : GaussFrameMGF := by
  intro N q m μ hμ b h hh S hS v L hv hL hframe s
  have := hμ
  -- notation
  have hr : Measurable (fun x : Fin N → ℝ => res b (h x)) := (measurable_res b).comp hh
  have me : Measurable (fun x : Fin N → ℝ => eDir b (h x)) := (measurable_eDir b).comp hh
  have mσ : Measurable (fun x : Fin N → ℝ => √v * √(normSq (res b (h x)))) :=
    measurable_const.mul (measurable_normSq.comp hr).sqrt
  have mK : Measurable (fun y : (Fin N → ℝ) × (Fin q → ℝ) =>
      (y.1, (√v * √(normSq (res b (h y.1)))) • y.2)) :=
    measurable_fst.prodMk ((mσ.comp measurable_fst).smul measurable_snd)
  have mI : Measurable (fun y : (Fin N → ℝ) × (Fin q → ℝ) =>
      S.indicator (1 : (Fin N → ℝ) × (Fin q → ℝ) → ℝ)
        (y.1, (√v * √(normSq (res b (h y.1)))) • y.2)) :=
    (measurable_one.indicator hS).comp mK
  have I01 : ∀ y : (Fin N → ℝ) × (Fin q → ℝ),
      S.indicator (1 : (Fin N → ℝ) × (Fin q → ℝ) → ℝ) y = 0 ∨
        S.indicator (1 : (Fin N → ℝ) × (Fin q → ℝ) → ℝ) y = 1 := by
    intro y
    by_cases hy : y ∈ S
    · right; simp [hy]
    · left; simp [hy]
  set f : (Fin N → ℝ) × (Fin q → ℝ) → ℝ := fun y =>
    exp (s * S.indicator (1 : (Fin N → ℝ) × (Fin q → ℝ) → ℝ)
      (y.1, (√v * √(normSq (res b (h y.1)))) • y.2)) with hf
  have mf : Measurable f := (mI.const_mul s).exp
  have hes : 0 < exp s := exp_pos s
  have hf01 : ∀ y, f y = 1 ∨ f y = exp s := by
    intro y
    rcases I01 (y.1, (√v * √(normSq (res b (h y.1)))) • y.2) with h0 | h1
    · left; simp [hf, h0]
    · right; simp [hf, h1]
  have ha : 0 < min 1 (exp s) := lt_min one_pos hes
  have hfa : ∀ y, min 1 (exp s) ≤ f y := by
    intro y
    rcases hf01 y with h0 | h1
    · rw [h0]; exact min_le_left _ _
    · rw [h1]; exact min_le_right _ _
  have hfb : ∀ y, f y ≤ max 1 (exp s) := by
    intro y
    rcases hf01 y with h0 | h1
    · rw [h0]; exact le_max_left _ _
    · rw [h1]; exact le_max_right _ _
  have hinact : ∀ x, eDir b (h x) = 0 → ∀ z, f (x, z) = f (x, 0) := by
    intro x hx z
    have h0 : res b (h x) = 0 := by
      rw [res_eq_smul_eDir, hx, smul_zero]
    have h1 : normSq (res b (h x)) = 0 := by rw [h0]; simp [normSq]
    simp [hf, h1]
  have key := hGP N q m μ hμ (fun x => eDir b (h x)) me (fun x => eDir_unit_or_zero b (h x))
    f mf (min 1 (exp s)) (max 1 (exp s)) ha hfa hfb hinact L hL hframe
  -- the target function of the matrix
  set p : Matrix (Fin q) (Fin m) ℝ → ℝ := fun M =>
    μ.real {x | (x, M.mulVec (res b (h x))) ∈ S} with hp
  have mJ : Measurable (fun z : Matrix (Fin q) (Fin m) ℝ × (Fin N → ℝ) =>
      (z.2, z.1.mulVec (res b (h z.2)))) :=
    measurable_snd.prodMk (measurable_mulVec_joint.comp
      (measurable_fst.prodMk (hr.comp measurable_snd)))
  have mp : Measurable p :=
    (measurable_measure_prodMk_left (ν := μ) (mJ hS)).ennreal_toReal
  -- the left side
  have eL : ∀ G : Matrix (Fin q) (Fin m) ℝ,
      ∫ x, log (f (x, G.mulVec (eDir b (h x)))) ∂μ = s * p (√v • G) := by
    intro G
    have e1 : ∀ x, log (f (x, G.mulVec (eDir b (h x)))) =
        s * S.indicator (1 : (Fin N → ℝ) × (Fin q → ℝ) → ℝ)
          (x, (√v • G).mulVec (res b (h x))) := by
      intro x
      have e2 : (√v * √(normSq (res b (h x)))) • G.mulVec (eDir b (h x)) =
          (√v • G).mulVec (res b (h x)) := by
        conv_rhs => rw [res_eq_smul_eDir b (h x)]
        rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
      simp only [hf]
      rw [Real.log_exp, e2]
    simp_rw [e1]
    rw [integral_const_mul]
    congr 1
    exact integral_indicator_comp μ (mJ.comp (measurable_prodMk_left (x := √v • G))) hS
  have hLHS : ∫ M, exp (s * p M / L) ∂gaussMat q m v =
      ∫ G, exp (1 / L * ∫ x, log (f (x, G.mulVec (eDir b (h x)))) ∂μ) ∂gaussMat q m 1 := by
    have m2 : Measurable (fun G : Matrix (Fin q) (Fin m) ℝ => √v • G) :=
      (continuous_const_smul (√v)).measurable
    rw [gaussMat_scale q m v, integral_map m2.aemeasurable
      (((mp.const_mul s).div_const L).exp).aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun G => ?_)
    change exp (s * p (√v • G) / L) = exp (1 / L * ∫ x, log (f (x, G.mulVec (eDir b (h x)))) ∂μ)
    rw [eL G]
    congr 1
    ring
  -- the right side: the inner mean
  set Q : (Fin N → ℝ) → ℝ := fun x =>
    (stdGauss (Fin q)).real {z | (x, (√v * √(normSq (res b (h x)))) • z) ∈ S} with hQ
  have mQ : Measurable Q :=
    (measurable_measure_prodMk_left (ν := stdGauss (Fin q)) (mK hS)).ennreal_toReal
  have Q0 : ∀ x, 0 ≤ Q x := fun x => measureReal_nonneg
  have Q1 : ∀ x, Q x ≤ 1 := fun x => measureReal_le_one
  have eR : ∀ x, ∫ z, f (x, z) ∂stdGauss (Fin q) = 1 - Q x + Q x * exp s := by
    intro x
    have e1 : ∀ z : Fin q → ℝ, f (x, z) = 1 + (exp s - 1) *
        S.indicator (1 : (Fin N → ℝ) × (Fin q → ℝ) → ℝ)
          (x, (√v * √(normSq (res b (h x)))) • z) := by
      intro z
      rcases I01 (x, (√v * √(normSq (res b (h x)))) • z) with h0 | h1
      · simp [hf, h0]
      · simp [hf, h1]
    simp_rw [e1]
    have mφ : Measurable (fun z : Fin q → ℝ => (x, (√v * √(normSq (res b (h x)))) • z)) :=
      mK.comp measurable_prodMk_left
    have iI : Integrable (fun z : Fin q → ℝ =>
        S.indicator (1 : (Fin N → ℝ) × (Fin q → ℝ) → ℝ)
          (x, (√v * √(normSq (res b (h x)))) • z)) (stdGauss (Fin q)) :=
      Integrable.of_bound ((measurable_one.indicator hS).comp mφ).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun z => by
          rcases I01 (x, (√v * √(normSq (res b (h x)))) • z) with h0 | h1
          · rw [h0]; simp
          · rw [h1]; simp)
    rw [integral_add (integrable_const _) (iI.const_mul _), integral_const_mul,
      integral_indicator_comp (stdGauss (Fin q)) mφ hS]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    change 1 + (exp s - 1) * Q x = 1 - Q x + Q x * exp s
    ring
  -- Jensen for the logarithm
  have ψa : ∀ x, min 1 (exp s) ≤ 1 - Q x + Q x * exp s := by
    intro x
    have h1 := min_le_left 1 (exp s)
    have h2 := min_le_right 1 (exp s)
    nlinarith [Q0 x, Q1 x]
  have ψb : ∀ x, 1 - Q x + Q x * exp s ≤ max 1 (exp s) := by
    intro x
    have h1 := le_max_left 1 (exp s)
    have h2 := le_max_right 1 (exp s)
    nlinarith [Q0 x, Q1 x]
  have mψ : Measurable (fun x => 1 - Q x + Q x * exp s) :=
    (measurable_const.sub mQ).add (mQ.mul_const _)
  have iQ : Integrable Q μ :=
    Integrable.of_bound mQ.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Q0 x)]; exact Q1 x)
  have iψ : Integrable (fun x => 1 - Q x + Q x * exp s) μ :=
    ((integrable_const _).sub iQ).add (iQ.mul_const _)
  have ilog : Integrable (fun x => log (1 - Q x + Q x * exp s)) μ := by
    refine Integrable.of_bound mψ.log.aestronglyMeasurable
      (|log (min 1 (exp s))| + |log (max 1 (exp s))|) (Filter.Eventually.of_forall fun x => ?_)
    have h1 : log (min 1 (exp s)) ≤ log (1 - Q x + Q x * exp s) :=
      Real.log_le_log ha (ψa x)
    have h2 : log (1 - Q x + Q x * exp s) ≤ log (max 1 (exp s)) :=
      Real.log_le_log (lt_of_lt_of_le ha (ψa x)) (ψb x)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le (log (min 1 (exp s)))
      have := abs_nonneg (log (max 1 (exp s)))
      linarith
    · have := le_abs_self (log (max 1 (exp s)))
      have := abs_nonneg (log (min 1 (exp s)))
      linarith
  have hconc : ConcaveOn ℝ (Set.Ici (min 1 (exp s))) log :=
    strictConcaveOn_log_Ioi.concaveOn.subset
      (fun y hy => lt_of_lt_of_le ha hy) (convex_Ici _)
  have hcont : ContinuousOn log (Set.Ici (min 1 (exp s))) :=
    Real.continuousOn_log.mono (fun y hy => ne_of_gt (lt_of_lt_of_le ha hy))
  have hJ : ∫ x, log (1 - Q x + Q x * exp s) ∂μ ≤ log (∫ x, (1 - Q x + Q x * exp s) ∂μ) :=
    hconc.le_map_integral hcont isClosed_Ici (Filter.Eventually.of_forall ψa) iψ ilog
  have eψ : ∫ x, (1 - Q x + Q x * exp s) ∂μ = 1 - ∫ x, Q x ∂μ + (∫ x, Q x ∂μ) * exp s := by
    rw [integral_add (f := fun x => 1 - Q x) (g := fun x => Q x * exp s)
      ((integrable_const _).sub iQ) (iQ.mul_const _),
      integral_sub (f := fun _ => (1 : ℝ)) (g := Q) (integrable_const _) iQ, integral_mul_const]
    simp
  -- the mean of `p`
  have eq0 : ∫ M, p M ∂gaussMat q m v = ∫ x, Q x ∂μ := by
    have h1 := frame_mean μ v hr hS (q := q)
    exact h1.trans (real_prod_eq μ (stdGauss (Fin q)) (mK hS))
  -- assembly
  have hpos : 0 < 1 - ∫ x, Q x ∂μ + (∫ x, Q x ∂μ) * exp s := by
    rw [← eψ]
    obtain ⟨x0⟩ := μ.nonempty_of_neZero
    exact lt_of_lt_of_le ha
      (by
        have := integral_mono (integrable_const (min 1 (exp s))) iψ ψa
        simpa using this)
  change ∫ M, exp (s * p M / L) ∂gaussMat q m v ≤
    (1 - ∫ M, p M ∂gaussMat q m v + (∫ M, p M ∂gaussMat q m v) * exp s) ^ (1 / L)
  rw [hLHS, eq0, Real.rpow_def_of_pos hpos]
  refine key.trans (exp_le_exp.mpr ?_)
  simp_rw [eR]
  rw [mul_comm (log _) (1 / L)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← eψ]
  exact hJ

variable {n : ℕ}

/-- **The conditional classifier theorem for the actual networks, final form of Part 157 (every
`n ≥ 16 384`).** `W`, `A`, `F` are the three independent random ReLU MLPs of `MM.md` at `r = 2`;
`D` is a design; the program draws `10¹²` times and outputs
`U = min 1 (max (1/100) (2.2524763228·R))`. IF
* `GaussGP` holds (the Gaussian Brascamp–Lieb inequality (GP); no network),
* `EVENTS_hyp`: there are measurable retained-data events `H`, `E₁` with
  `Pr(Hᶜ) ≤ 0.001900001`, `E[1_H H̄_W²] ≤ 0.000741853·(0.004)²`,
  `Pr(H ∩ E₁ᶜ) ≤ 0.001104285235085` (`H̄_W = HbarW D` the Hellinger radius),
and on `H ∩ {H̄_W ≤ 0.0024160420} ∩ E₁`:
* `FRAME_W_hyp`: the World frame bound `1.377/n`,
* `FRAME_A_hyp`: the Agent frame bound `1.743/n` under the stand-in input distribution,
* `REPLA_mix_hyp`: `|√Q − √q̃| ≤ 0.006583 + 10⁻²⁰`,
THEN `Pr(p ≤ U ≤ max (10 p) (1/100)) ≥ 99/100`, jointly over the networks and the draws. Every
hypothesis except `GaussGP` is a statement about the retained data of the actual networks. -/
theorem classifier_networks_conditional_gp (hn : 16384 ≤ n) (hGP : GaussGP)
    (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhidL vWL δextraL)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_hell hn (mgf_of_gp hGP) D t hEv hFW hFA hRA

/-- The same at `n = 16 384`. -/
theorem classifier_networks_conditional_gp_16384 (hGP : GaussGP)
    (D : Design 16384) (t : ℝ) {H E₁ : Set (Ret 16384)}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhidL vWL δextraL)
    (hFW : FRAME_W_hyp D.toCentres (cWL / 16384) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cfL / 16384) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 16384).prod (sampMeas (10 ^ 12) 16384)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have e : ((16384 : ℕ) : ℝ) = 16384 := by norm_num
  exact classifier_networks_conditional_gp (n := 16384) le_rfl hGP D t hEv
    (by rw [e]; exact hFW) (by rw [e]; exact hFA) hRA

/-! ## The frame bounds with the constant `1` (for comparison) -/

/-- `FRAME_W_hyp` holds with the constant `1` on every set (the directions are unit vectors).
The hypothesis of the theorem needs the constant `1.377/n`. -/
theorem frame_w_one (hn : 1 ≤ n) (D : Centres n) (E : Set (Ret n)) : FRAME_W_hyp D 1 E := by
  intro c _ w
  have hprob := BstLean.Part29.uniformSphere_isProbability (2 * n) (by omega)
  exact eDir_frame_one (uniformSphere (2 * n)) (D.bW c.1.1)
    (continuous_hid2 c.1.1.1 c.1.1.2).measurable w

/-- `FRAME_A_hyp` holds with the constant `1` on every set. The hypothesis of the theorem needs
the constant `1.743/n`. -/
theorem frame_a_one (D : Design n) (E : Set (Ret n)) : FRAME_A_hyp D 1 E :=
  fun c _ w => eDir_frame_one (stdGauss (Fin n)) (D.bA c.1 c.2.1.1) (measurable_hStand D c) w

end BstLean.Part157

open BstLean.Part157 in
#print axioms gaussMat_scale
open BstLean.Part157 in
#print axioms mgf_of_gp
open BstLean.Part157 in
#print axioms classifier_networks_conditional_gp
open BstLean.Part157 in
#print axioms classifier_networks_conditional_gp_16384
open BstLean.Part157 in
#print axioms frame_w_one
