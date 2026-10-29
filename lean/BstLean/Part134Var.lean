import BstLean.Part134Core

/-!
# Part 134, item 3: the variance bound of the stand-in (`s1_var`)

Role: `delegations/statements/p134-spec.md`, item 3 (paper Theorem S1, part (c)), in the
variance form, for every bounded measurable `φ`, with the constant `λ₁` of the paper as a
hypothesis: `∀ w, E_u ⟨e(u), w⟩² ≤ L·|w|²`, `e(u) = r(u)/|r(u)|` (`eDir`; `0` if `r(u) = 0`).
This hypothesis says that the largest eigenvalue of `Σ_e = E_u e(u) e(u)ᵀ` is at most `L`.

* `s1_var`: `Var(E_{μ_M} φ | c) ≤ L · E_u Var_γ φ(sphPt(λ(u) c + σ(u) γ))`.
* `s1_var_total`: `E_u Var_γ φ(sphPt(λ(u) c + σ(u) γ)) ≤ Var_{ν_c} φ`.
* `s1_var_standIn`: `Var(E_{μ_M} φ | c) ≤ L · Var_{ν_c} φ`.
* `s1_mse`: `E_M (E_{μ_M} φ − E_{ν_{M b}} φ)² ≤ L · E_c Var_{ν_c} φ` (mean and variance together).
* `eDir_frame_one`: the hypothesis holds with `L = 1`.
* `s1_var_mlp`, `s1_mse_mlp`: the World network.

"Given `c`" means: `M` is replaced by `glue b c (M' * projPerp b)`, `M'` a Gaussian matrix; see
`s1_disint`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part134

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM bm_cauchy_schwarz)
open BstLean.Part130

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

/-! ## The unit residual direction -/

/-- `e = r/|r|`, `r = res b h` (and `0` if `r = 0`): the direction of the residual. -/
noncomputable def eDir (b h : Fin m → ℝ) : Fin m → ℝ :=
  (Real.sqrt (normSq (res b h)))⁻¹ • res b h

lemma measurable_eDir (b : Fin m → ℝ) : Measurable (eDir b) := by
  unfold eDir
  exact ((measurable_normSq.comp (measurable_res b)).sqrt.inv).smul (measurable_res b)

lemma eq_zero_of_normSq {r : Fin m → ℝ} (h : normSq r = 0) : r = 0 := by
  by_contra h'
  exact normSq_ne_zero h' h

lemma eDir_unit_or_zero (b h : Fin m → ℝ) : normSq (eDir b h) = 1 ∨ eDir b h = 0 := by
  by_cases h0 : normSq (res b h) = 0
  · right
    unfold eDir
    rw [eq_zero_of_normSq h0, smul_zero]
  · left
    unfold eDir
    have hpos : 0 < normSq (res b h) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
    rw [normSq_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ h0]

lemma res_eq_smul_eDir (b h : Fin m → ℝ) :
    res b h = Real.sqrt (normSq (res b h)) • eDir b h := by
  by_cases h0 : normSq (res b h) = 0
  · unfold eDir
    rw [eq_zero_of_normSq h0]; simp
  · unfold eDir
    have hpos : 0 < normSq (res b h) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
    rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hpos), one_smul]

/-- The residual field in terms of the standard Gaussian entries `ξ`: for
`M' = (√v ξ(i, j))_{i,j}`, `M' r = σ · (G e)`, `G = (ξ(i, j))_{i,j}`. -/
lemma resid_eq (v : ℝ) (b h : Fin m → ℝ) (ξ : Fin n × Fin m → ℝ) :
    (Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin n) (Fin m) ℝ).mulVec (res b h) =
      sig v b h • (rowMat n (eDir b h)).mulVec ξ := by
  have e1 : (Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin n) (Fin m) ℝ) =
      Real.sqrt v • unflat ξ := by
    ext i j; simp [unflat]
  rw [e1, rowMat_mulVec', Matrix.smul_mulVec]
  conv_lhs => rw [res_eq_smul_eDir b h]
  rw [Matrix.mulVec_smul, smul_smul]
  rfl

/-! ## Variances of bounded functions -/

lemma bm_memLp2 {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {X : α → ℝ} (hX : BM X) : MemLp X 2 P := by
  obtain ⟨C, hC⟩ := hX.bdd
  exact MemLp.of_bound hX.meas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa using hC x)

lemma var_bm {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {X : α → ℝ} (hX : BM X) : Var[X; P] = ∫ x, X x ^ 2 ∂P - (∫ x, X x ∂P) ^ 2 := by
  rw [variance_eq_sub (bm_memLp2 P hX)]
  rfl

lemma var_bm' {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {X : α → ℝ} (hX : BM X) : Var[X; P] = ∫ x, (X x - ∫ y, X y ∂P) ^ 2 ∂P :=
  variance_eq_integral hX.meas.aemeasurable

section main

variable (μ : Measure U) [IsProbabilityMeasure μ]

lemma standIn_prob {h : U → Fin m → ℝ} (hh : Measurable h) (v : ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : IsProbabilityMeasure (standIn μ h v b c) := by
  unfold standIn
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_sphPt.comp (measurable_standOut hh v b c)).aemeasurable).2 inferInstance

omit [MeasurableSpace U] in
/-- The stand-in integrand `f_u(γ) = φ(sphPt(λ(u) c + σ(u) γ))`. -/
noncomputable def stF (φ : (Fin n → ℝ) → ℝ) (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (h : U → Fin m → ℝ) : U × (Fin n → ℝ) → ℝ :=
  fun p => φ (sphPt (lam b (h p.1) • c + sig v b (h p.1) • p.2))

omit [IsProbabilityMeasure μ] in
/-- The stand-in integrand is bounded and measurable. -/
lemma bm_stF (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) : BM (stF φ v b c h) :=
  hφ.comp (measurable_sphPt.comp (measurable_standOut hh v b c))

lemma var_stF (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (u : U) :
    Var[fun γ => φ (sphPt (lam b (h u) • c + sig v b (h u) • γ)); stdGauss (Fin n)] =
      ∫ z, (stF φ v b c h (u, z) - ∫ y, stF φ v b c h (u, y) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) :=
  var_bm' (stdGauss (Fin n)) (X := fun z => stF φ v b c h (u, z))
    ((bm_stF v b c hh hφ).comp measurable_prodMk_left)

lemma var_stF' (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (u : U) :
    Var[fun γ => φ (sphPt (lam b (h u) • c + sig v b (h u) • γ)); stdGauss (Fin n)] =
      ∫ z, stF φ v b c h (u, z) ^ 2 ∂stdGauss (Fin n) -
        (∫ y, stF φ v b c h (u, y) ∂stdGauss (Fin n)) ^ 2 :=
  var_bm (stdGauss (Fin n)) (X := fun z => stF φ v b c h (u, z))
    ((bm_stF v b c hh hφ).comp measurable_prodMk_left)

/-- `M' ↦ E_{μ_M} φ`, `M = glue b c (M' P)`, is bounded and measurable. -/
lemma bm_condMean (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun M' : Matrix (Fin n) (Fin m) ℝ => ∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b))) :=
  (bm_muM μ hh hφ).comp ((measurable_glue b).comp
    (measurable_const.prodMk (measurable_mul_right _)))

omit [MeasurableSpace U] in
lemma integral_gaussMat (v : ℝ) {G : Matrix (Fin n) (Fin m) ℝ → ℝ} (hG : Measurable G) :
    ∫ M, G M ∂gaussMat n m v =
      ∫ ξ, G (Matrix.of fun i j => Real.sqrt v * ξ (i, j)) ∂stdGauss (Fin n × Fin m) := by
  unfold gaussMat
  exact integral_map (measurable_ofFlat _).aemeasurable hG.aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
/-- The conditional mean in terms of the standard Gaussian entries. -/
lemma condMean_eq (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (ξ : Fin n × Fin m → ℝ) :
    ∫ x, φ x ∂muM μ h (glue b c
        ((Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin n) (Fin m) ℝ) *
          projPerp b)) = ∫ u, stF φ v b c h (u, (rowMat n (eDir b (h u))).mulVec ξ) ∂μ := by
  rw [integral_muM μ hh hφ.meas]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [stF]
  rw [glue_res, resid_eq]

/-- **Theorem S1 (c), the variance bound.** `μ` a probability measure on the inputs `u`,
`h` measurable, `φ` bounded measurable, `c ∈ ℝⁿ` and `b ∈ ℝ^m` fixed, `L ≥ 0` a bound of the
largest eigenvalue of `Σ_e = E_u e(u) e(u)ᵀ`. Given `c` (the matrix is `glue b c (M' P)`, `M'`
Gaussian with entry variance `v`):
`Var(E_{μ_M} φ) ≤ L · E_u Var_γ φ(sphPt(λ(u) c + σ(u) γ))`. -/
theorem s1_var (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    Var[fun M' => ∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b)); gaussMat n m v] ≤
      L * ∫ u, Var[fun γ => φ (sphPt (lam b (h u) • c + sig v b (h u) • γ));
        stdGauss (Fin n)] ∂μ := by
  have bΦ := bm_condMean μ b c hh hφ
  have core := var_core (n := n) μ ((measurable_eDir b).comp hh)
    (fun u => eDir_unit_or_zero b (h u)) (bm_stF v b c hh hφ) hL0 hL
  have e1 : ∫ M', (∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b))) ^ 2 ∂gaussMat n m v =
      ∫ ξ, (∫ u, stF φ v b c h (u, (rowMat n (eDir b (h u))).mulVec ξ) ∂μ) ^ 2
        ∂stdGauss (Fin n × Fin m) := by
    rw [integral_gaussMat v bΦ.sq.meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [condMean_eq μ v b c hh hφ ξ]
  have e2 : ∫ M', (∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b))) ∂gaussMat n m v =
      ∫ ξ, (∫ u, stF φ v b c h (u, (rowMat n (eDir b (h u))).mulVec ξ) ∂μ)
        ∂stdGauss (Fin n × Fin m) := by
    rw [integral_gaussMat v bΦ.meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [condMean_eq μ v b c hh hφ ξ]
  rw [var_bm (gaussMat n m v) bΦ, e1, e2]
  simp_rw [var_stF v b c hh hφ]
  exact core

/-- **The total variance inequality**: `E_u Var_γ φ(sphPt(λ(u) c + σ(u) γ)) ≤ Var_{ν_c} φ`. -/
theorem s1_var_total (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ u, Var[fun γ => φ (sphPt (lam b (h u) • c + sig v b (h u) • γ)); stdGauss (Fin n)] ∂μ ≤
      Var[φ; standIn μ h v b c] := by
  have := standIn_prob (n := n) μ hh v b c
  have bf : BM (stF φ v b c h) := bm_stF v b c hh hφ
  have bm1 : BM (fun u => ∫ γ, stF φ v b c h (u, γ) ∂stdGauss (Fin n)) := bf.integral_right _
  have bm2 : BM (fun u => ∫ γ, stF φ v b c h (u, γ) ^ 2 ∂stdGauss (Fin n)) :=
    bf.sq.integral_right _
  simp_rw [var_stF' v b c hh hφ]
  rw [integral_sub (bm2.integrable μ) (bm1.sq.integrable μ), var_bm (standIn μ h v b c) hφ,
    integral_standIn μ v b c hh hφ, integral_standIn μ v b c hh hφ.sq]
  have cs := bm_cauchy_schwarz μ bm1 (BM.const 1)
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at cs
  have e1 : (∫ u, ∫ γ, φ (sphPt (lam b (h u) • c + sig v b (h u) • γ)) ∂stdGauss (Fin n) ∂μ) =
      ∫ u, ∫ γ, stF φ v b c h (u, γ) ∂stdGauss (Fin n) ∂μ := rfl
  have e2 : (∫ u, ∫ γ, φ (sphPt (lam b (h u) • c + sig v b (h u) • γ)) ^ 2 ∂stdGauss (Fin n) ∂μ) =
      ∫ u, ∫ γ, stF φ v b c h (u, γ) ^ 2 ∂stdGauss (Fin n) ∂μ := rfl
  rw [e1, e2]
  linarith

/-- **Theorem S1 (c) with the variance of the stand-in distribution**:
`Var(E_{μ_M} φ | c) ≤ L · Var_{ν_c} φ`. -/
theorem s1_var_standIn (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    Var[fun M' => ∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b)); gaussMat n m v] ≤
      L * Var[φ; standIn μ h v b c] :=
  (s1_var μ v b c hh hφ hL0 hL).trans
    (mul_le_mul_of_nonneg_left (s1_var_total μ v b c hh hφ) hL0)

/-- The hypothesis of `s1_var` holds with `L = 1` (`λ₁ ≤ 1`). -/
theorem eDir_frame_one (b : Fin m → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    (w : Fin m → ℝ) :
    ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ 1 * ∑ j, w j ^ 2 := by
  have pt : ∀ u, (∑ j, eDir b (h u) j * w j) ^ 2 ≤ ∑ j, w j ^ 2 := by
    intro u
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => eDir b (h u) j) w
    have h1 : ∑ j, eDir b (h u) j ^ 2 ≤ 1 := by
      rcases eDir_unit_or_zero b (h u) with h1 | h1
      · exact h1.le
      · rw [h1]; simp
    have h0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    nlinarith
  have hm : Measurable (fun u => (∑ j, eDir b (h u) j * w j) ^ 2) :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_eDir b).comp hh)).mul_const _).pow_const 2
  have hi : Integrable (fun u => (∑ j, eDir b (h u) j * w j) ^ 2) μ :=
    Integrable.of_bound hm.aestronglyMeasurable (∑ j, w j ^ 2)
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pt u)
  calc ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ ∫ _u, (∑ j, w j ^ 2) ∂μ :=
        integral_mono hi (integrable_const _) pt
    _ = 1 * ∑ j, w j ^ 2 := by simp

/-- **Theorem S1, (b) and (c) together: the mean squared error of the stand-in.** For `b ≠ 0`:
`E_M (E_{μ_M} φ − E_{ν_{M b}} φ)² ≤ L · E_c Var_{ν_c} φ`, `c ~ N(0, v|b|²·I_n)`. -/
theorem s1_mse (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫ M, ((∫ x, φ x ∂muM μ h M) - ∫ x, φ x ∂standIn μ h v b (M.mulVec b)) ^ 2 ∂gaussMat n m v ≤
      L * ∫ c, Var[φ; standIn μ h v b c] ∂cDist n v b := by
  have bN := bm_standIn (n := n) μ v b hh hφ
  have bN2 := bm_standIn (n := n) μ v b hh hφ.sq
  have bΘ : BM (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      ((∫ x, φ x ∂muM μ h p.2) - ∫ x, φ x ∂standIn μ h v b p.1) ^ 2) :=
    (((bm_muM μ hh hφ).comp measurable_snd).sub (bN.comp measurable_fst)).sq
  have hm1 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  have hm2 : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  have e1 : ∫ M, ((∫ x, φ x ∂muM μ h M) - ∫ x, φ x ∂standIn μ h v b (M.mulVec b)) ^ 2
      ∂gaussMat n m v =
      ∫ p, ((∫ x, φ x ∂muM μ h p.2) - ∫ x, φ x ∂standIn μ h v b p.1) ^ 2
        ∂(gaussMat n m v).map (fun M => (M.mulVec b, M)) :=
    (integral_map hm1.aemeasurable bΘ.meas.aestronglyMeasurable).symm
  rw [e1, s1_disint v hb, integral_map hm2.aemeasurable bΘ.meas.aestronglyMeasurable,
    integral_prod _ ((bΘ.comp hm2).integrable _), ← integral_const_mul]
  have hvar : ∀ c : Fin n → ℝ, Var[φ; standIn μ h v b c] =
      ∫ x, φ x ^ 2 ∂standIn μ h v b c - (∫ x, φ x ∂standIn μ h v b c) ^ 2 := by
    intro c
    have := standIn_prob (n := n) μ hh v b c
    exact var_bm (standIn μ h v b c) hφ
  have bR : BM (fun c : Fin n → ℝ => L * Var[φ; standIn μ h v b c]) := by
    simp_rw [hvar]
    exact (BM.const L).mul (bN2.sub bN.sq)
  refine integral_mono ((bΘ.comp hm2).integral_right _ |>.integrable _) (bR.integrable _)
    fun c => ?_
  simp only []
  have bΦ := bm_condMean μ b c hh hφ
  have hmean := s1_mean_cond μ v b c hh hφ
  have hv := s1_var_standIn μ v b c hh hφ hL0 hL
  rw [var_bm' (gaussMat n m v) bΦ, hmean] at hv
  exact hv

end main

/-! ## The World network -/

/-- **Theorem S1 (c) for the World network** `W = (M₁, M₂, M₃)`: `(M₁, M₂)` and `c` fixed,
`M₃ = glue b c (M' P)` with `M'` Gaussian of variance `2/m`; `h = hid2 M₁ M₂` the last hidden
vector; `u` uniform on the unit sphere of `ℝ^N`. -/
theorem s1_var_mlp {N : ℕ} (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ)
    (M₂ : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (hid2 M₁ M₂ u) j * w j) ^ 2 ∂uniformSphere N ≤
      L * ∑ j, w j ^ 2) :
    Var[fun M' => ∫ x, φ x ∂muWn ((M₁, M₂, glue b c (M' * projPerp b)) : MlpParam N m n);
        gaussMat n m (2 / (m : ℝ))] ≤
      L * Var[φ; standIn (uniformSphere N) (hid2 M₁ M₂) (2 / (m : ℝ)) b c] := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  exact s1_var_standIn (uniformSphere N) (2 / (m : ℝ)) b c (continuous_hid2 M₁ M₂).measurable hφ
    hL0 hL

/-- **Theorem S1 (b) and (c) for the World network**: the mean squared error of the stand-in over
the last matrix `M₃`, with `(M₁, M₂)` fixed and `b ≠ 0`. -/
theorem s1_mse_mlp {N : ℕ} (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ)
    (M₂ : Matrix (Fin m) (Fin m) ℝ) {b : Fin m → ℝ} (hb : b ≠ 0)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (hid2 M₁ M₂ u) j * w j) ^ 2 ∂uniformSphere N ≤
      L * ∑ j, w j ^ 2) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((M₁, M₂, M₃) : MlpParam N m n)) -
        ∫ x, φ x ∂standIn (uniformSphere N) (hid2 M₁ M₂) (2 / (m : ℝ)) b (M₃.mulVec b)) ^ 2
        ∂gaussMat n m (2 / (m : ℝ)) ≤
      L * ∫ c, Var[φ; standIn (uniformSphere N) (hid2 M₁ M₂) (2 / (m : ℝ)) b c]
        ∂cDist n (2 / (m : ℝ)) b := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  exact s1_mse (uniformSphere N) (2 / (m : ℝ)) hb (continuous_hid2 M₁ M₂).measurable hφ hL0 hL

end BstLean.Part134

open BstLean.Part134 in
#print axioms s1_var
open BstLean.Part134 in
#print axioms s1_var_total
open BstLean.Part134 in
#print axioms s1_var_standIn
open BstLean.Part134 in
#print axioms eDir_frame_one
open BstLean.Part134 in
#print axioms s1_mse
open BstLean.Part134 in
#print axioms s1_var_mlp
open BstLean.Part134 in
#print axioms s1_mse_mlp
