import BstLean.Part131Block

/-!
# Part 135: the Gaussian block lemma with a level `t0 ≤ 1` and a tolerance factor `θ`

Generalizes `BstLean.Part131.gauss_block_tail`. `Φ̄(t) = (gaussianReal 0 1).real (Ioi t)`.

* `tail_line_at`: the supporting line of `z ↦ Φ̄(√z)` at `z = t0²`.
* `gauss_block_z`: `yᵀMy ≥ 0`, `0 < t0 ≤ 1`, `tr M < t0²|v|²` ⇒ `Pr(gᵀMg < (g·v)²) > Φ̄(t0)`.
* `gauss_block_theta_z`, `gauss_block_theta`: the same for `θ • M`.
* `tail_lower`, `tail_five_eighths`: a numeric lower bound for `Φ̄`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part135
open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part131

/-- The standard Gaussian density is decreasing on `x ≥ 0`. -/
lemma pdf_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 1 y ≤ gaussianPDFReal 0 1 x := by
  rw [pdf_eq, pdf_eq]
  have h : Real.exp (-(y ^ 2 / 2)) ≤ Real.exp (-(x ^ 2 / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hc : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left h hc

lemma pdf_ge_at {t0 x : ℝ} (ht0 : 0 < t0) (h0 : 0 ≤ x) (h1 : x ≤ t0) :
    gaussianPDFReal 0 1 t0 / t0 * x ≤ gaussianPDFReal 0 1 x := by
  have hp := gaussianPDFReal_nonneg 0 1 t0
  have h2 := pdf_anti h0 h1
  have h3 : gaussianPDFReal 0 1 t0 / t0 * x = gaussianPDFReal 0 1 t0 * (x / t0) := by
    field_simp
  have h4 : x / t0 ≤ 1 := (div_le_one ht0).mpr h1
  rw [h3]
  nlinarith

lemma pdf_le_at {t0 x : ℝ} (ht0 : 0 < t0) (h1 : t0 ≤ x) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 t0 / t0 * x := by
  have hp := gaussianPDFReal_nonneg 0 1 t0
  have h2 := pdf_anti ht0.le h1
  have h3 : gaussianPDFReal 0 1 t0 / t0 * x = gaussianPDFReal 0 1 t0 * (x / t0) := by
    field_simp
  have h4 : 1 ≤ x / t0 := (one_le_div ht0).mpr h1
  rw [h3]
  nlinarith

lemma integral_Ioc_lin_at (k : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioc a b, k * x = k / 2 * (b ^ 2 - a ^ 2) := by
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul, integral_id]
  ring

lemma intOn_lin_at (k a b : ℝ) : IntegrableOn (fun x : ℝ => k * x) (Ioc a b) :=
  (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- supporting line of z ↦ Φ̄(√z) at z = t0² -/
theorem tail_line_at {t0 t : ℝ} (ht0 : 0 < t0) (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) * (t0 ^ 2 - t ^ 2) ≤
      (gaussianReal 0 1).real (Ioi t) := by
  have hint := integrable_gaussianPDFReal 0 1
  set k : ℝ := gaussianPDFReal 0 1 t0 / t0 with hk
  have hk2 : gaussianPDFReal 0 1 t0 / (2 * t0) = k / 2 := by
    rw [hk]; field_simp
  rw [hk2]
  rcases le_total t t0 with h | h
  · have hu : Ioi t = Ioc t t0 ∪ Ioi t0 := (Ioc_union_Ioi_eq_Ioi h).symm
    have hd : Disjoint (Ioc t t0) (Ioi t0) := by
      rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
    rw [hu, measureReal_union hd measurableSet_Ioi, gauss_real_eq (Ioc t t0)]
    have h1 : ∫ x in Ioc t t0, k * x ≤ ∫ x in Ioc t t0, gaussianPDFReal 0 1 x := by
      refine setIntegral_mono_on (intOn_lin_at k t t0) hint.integrableOn measurableSet_Ioc ?_
      intro x hx; exact pdf_ge_at ht0 (ht.trans hx.1.le) hx.2
    rw [integral_Ioc_lin_at k h] at h1
    linarith
  · have hu : Ioi t0 = Ioc t0 t ∪ Ioi t := (Ioc_union_Ioi_eq_Ioi h).symm
    have hd : Disjoint (Ioc t0 t) (Ioi t) := by
      rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
    rw [hu, measureReal_union hd measurableSet_Ioi, gauss_real_eq (Ioc t0 t)]
    have h1 : ∫ x in Ioc t0 t, gaussianPDFReal 0 1 x ≤ ∫ x in Ioc t0 t, k * x := by
      refine setIntegral_mono_on hint.integrableOn (intOn_lin_at k t0 t) measurableSet_Ioc ?_
      intro x hx; exact pdf_le_at ht0 hx.1.le
    rw [integral_Ioc_lin_at k h] at h1
    linarith

variable {ι : Type} [Fintype ι]

/-- block bound with a level t0 ≤ 1 -/
theorem gauss_block_z (v : ι → ℝ) (M : Matrix ι ι ℝ) (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y)
    {t0 : ℝ} (ht0 : 0 < t0) (ht1 : t0 ≤ 1) (hv : M.trace < t0 ^ 2 * (v ⬝ᵥ v)) :
    (gaussianReal 0 1).real (Ioi t0) < (stdGauss ι).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} := by
  classical
  have htr : 0 ≤ M.trace := by
    rw [← qform_integral]; exact integral_nonneg fun h => hM h
  have ht0sq : 0 < t0 ^ 2 := by positivity
  have ht0le : t0 ^ 2 ≤ 1 := by nlinarith
  set D : ℝ := v ⬝ᵥ v with hD
  have hDpos : 0 < D := by
    by_contra hcon
    have : D ≤ 0 := not_lt.mp hcon
    nlinarith
  set s : ℝ := √D with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hDpos
  have hss : s ^ 2 = D := Real.sq_sqrt hDpos.le
  set e : ι → ℝ := s⁻¹ • v with he_def
  have hve : v = s • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
  have he : e ⬝ᵥ e = 1 := by
    rw [he_def, smul_dotProduct, dotProduct_smul, ← hD, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  set P := projMat e with hP
  set a : ℝ := e ⬝ᵥ M *ᵥ e with ha
  have ha0 : 0 ≤ a := hM e
  let q : (ι → ℝ) → ℝ := fun h => (P *ᵥ h) ⬝ᵥ M *ᵥ (P *ᵥ h)
  let β : (ι → ℝ) → ℝ := fun h => e ⬝ᵥ M *ᵥ (P *ᵥ h) + (P *ᵥ h) ⬝ᵥ M *ᵥ e
  have hq0 : ∀ h, 0 ≤ q h := fun h => hM _
  have hqN : ∀ h, q h = h ⬝ᵥ (Pᵀ * M * P) *ᵥ h := by
    intro h
    simp only [q]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec h, vecMul_transpose]
  have hqint : Integrable q (stdGauss ι) := by
    rw [show q = fun h => h ⬝ᵥ (Pᵀ * M * P) *ᵥ h from funext hqN]; exact qform_integrable _
  have hEq : ∫ h, q h ∂stdGauss ι = M.trace - a := by
    rw [show q = fun h => h ⬝ᵥ (Pᵀ * M * P) *ᵥ h from funext hqN]
    rw [qform_integral, trace_mul_cycle, hP, projMat_transpose, projMat_mul_self he, projMat,
      Matrix.sub_mul, Matrix.one_mul, trace_sub, vecMulVec_mul, trace_vecMulVec, ha,
      dotProduct_mulVec, dotProduct_comm]
  have haT : a ≤ M.trace := by
    have : 0 ≤ ∫ h, q h ∂stdGauss ι := integral_nonneg hq0
    linarith
  set δ : ℝ := D - a with hδ
  have hDle : t0 ^ 2 * D ≤ D := by nlinarith
  have hδpos : 0 < δ := by linarith
  -- the event in the coordinates `(x, h)`
  let Φ : ℝ × (ι → ℝ) → ι → ℝ := fun p => p.1 • e + P *ᵥ p.2
  have hΦ : Measurable Φ := by fun_prop
  set S : Set (ι → ℝ) := {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} with hSdef
  have hS : MeasurableSet S := by
    have h1 : Continuous fun g : ι → ℝ => g ⬝ᵥ M *ᵥ g := by fun_prop
    have h2 : Continuous fun g : ι → ℝ => (g ⬝ᵥ v) ^ 2 := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  have hmem : ∀ (x : ℝ) (h : ι → ℝ), Φ (x, h) ∈ S ↔ x ^ 2 * a + x * β h + q h < D * x ^ 2 := by
    intro x h
    have h0 : (P *ᵥ h) ⬝ᵥ e = 0 := projMat_dot he h
    have e1 : Φ (x, h) ⬝ᵥ M *ᵥ Φ (x, h) = x ^ 2 * a + x * β h + q h := by
      simp only [Φ, β, q, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, ha]
      ring
    have e2 : (Φ (x, h) ⬝ᵥ v) ^ 2 = D * x ^ 2 := by
      simp only [Φ]
      rw [hve, dotProduct_smul, add_dotProduct, smul_dotProduct, he, h0, ← hss]
      simp only [smul_eq_mul]; ring
    change Φ (x, h) ⬝ᵥ M *ᵥ Φ (x, h) < (Φ (x, h) ⬝ᵥ v) ^ 2 ↔ _
    rw [e1, e2]
  have hreal : (stdGauss ι).real S =
      ∫ h, (gaussianReal 0 1).real {x | Φ (x, h) ∈ S} ∂stdGauss ι := by
    conv_lhs => rw [← stdGauss_decomp he]
    rw [map_measureReal_apply hΦ hS, Measure.real, Measure.prod_apply_symm (hΦ hS),
      ← integral_toReal (measurable_measure_prodMk_right (hΦ hS)).aemeasurable
        (ae_of_all _ fun h => measure_lt_top _ _)]
    rfl
  set c : ℝ := gaussianPDFReal 0 1 t0 / (2 * t0) with hc
  have hcpos : 0 < c := by
    have : 0 < gaussianPDFReal 0 1 t0 := by rw [pdf_eq]; positivity
    positivity
  set T1 : ℝ := (gaussianReal 0 1).real (Ioi t0) with hT1
  -- the pointwise lower bound
  have hpt : ∀ h, T1 + c * (t0 ^ 2 - q h / δ) ≤
      (gaussianReal 0 1).real {x | Φ (x, h) ∈ S} := by
    intro h
    set t : ℝ := √(q h / δ) with ht
    have htn : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t ^ 2 = q h / δ := Real.sq_sqrt (div_nonneg (hq0 h) hδpos.le)
    have hline := tail_line_at ht0 htn
    rw [htt] at hline
    have hkey : ∀ x : ℝ, t ^ 2 < x ^ 2 → x * β h ≤ 0 → Φ (x, h) ∈ S := by
      intro x hx hxb
      rw [hmem]
      rw [htt, div_lt_iff₀ hδpos] at hx
      rw [hδ] at hx
      nlinarith
    rcases le_or_gt (β h) 0 with hb | hb
    · have hsub : Ioi t ⊆ {x | Φ (x, h) ∈ S} := by
        intro x hx
        have hx' : t < x := hx
        exact hkey x (by nlinarith) (by nlinarith)
      exact hline.trans (measureReal_mono hsub)
    · have hsub : Iio (-t) ⊆ {x | Φ (x, h) ∈ S} := by
        intro x hx
        have hx' : x < -t := hx
        exact hkey x (by nlinarith) (by nlinarith)
      exact (hline.trans (tail_neg t).symm.le).trans (measureReal_mono hsub)
  have i1 : Integrable (fun h => q h / δ) (stdGauss ι) := hqint.div_const _
  have i2 : Integrable (fun h => t0 ^ 2 - q h / δ) (stdGauss ι) := (integrable_const _).sub i1
  have i3 : Integrable (fun h => c * (t0 ^ 2 - q h / δ)) (stdGauss ι) := i2.const_mul c
  have hint1 : Integrable (fun h => T1 + c * (t0 ^ 2 - q h / δ)) (stdGauss ι) :=
    (integrable_const _).add i3
  have hint2 : Integrable (fun h => (gaussianReal 0 1).real {x | Φ (x, h) ∈ S}) (stdGauss ι) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_measure_prodMk_right (hΦ hS)).ennreal_toReal.aestronglyMeasurable ?_
    refine ae_of_all _ fun h => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hmono := integral_mono hint1 hint2 hpt
  rw [← hreal] at hmono
  have hI : ∫ h, T1 + c * (t0 ^ 2 - q h / δ) ∂stdGauss ι =
      T1 + c * (t0 ^ 2 - (M.trace - a) / δ) := by
    have e1 : ∫ h, q h / δ ∂stdGauss ι = (M.trace - a) / δ := by rw [integral_div, hEq]
    have e2 : ∫ h, (t0 ^ 2 - q h / δ) ∂stdGauss ι = t0 ^ 2 - (M.trace - a) / δ := by
      rw [integral_sub (integrable_const _) i1, e1]; simp
    have e3 : ∫ h, c * (t0 ^ 2 - q h / δ) ∂stdGauss ι = c * (t0 ^ 2 - (M.trace - a) / δ) := by
      rw [integral_const_mul, e2]
    rw [integral_add (integrable_const _) i3, e3]; simp
  rw [hI] at hmono
  have h1 : 0 < t0 ^ 2 - (M.trace - a) / δ := by
    rw [sub_pos, div_lt_iff₀ hδpos, hδ]
    have : 0 ≤ a * (1 - t0 ^ 2) := mul_nonneg ha0 (by linarith)
    nlinarith
  have h3 : 0 < c * (t0 ^ 2 - (M.trace - a) / δ) := mul_pos hcpos h1
  linarith

omit [Fintype ι] in
lemma qform_smul [Fintype ι] (θ : ℝ) (M : Matrix ι ι ℝ) (g : ι → ℝ) :
    g ⬝ᵥ (θ • M) *ᵥ g = θ * (g ⬝ᵥ M *ᵥ g) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- block bound with a tolerance factor θ (apply the above to θ • M) -/
theorem gauss_block_theta_z (v : ι → ℝ) (M : Matrix ι ι ℝ) (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y)
    {θ t0 : ℝ} (hθ : 0 ≤ θ) (ht0 : 0 < t0) (ht1 : t0 ≤ 1) (hv : θ * M.trace < t0 ^ 2 * (v ⬝ᵥ v)) :
    (gaussianReal 0 1).real (Ioi t0) <
      (stdGauss ι).real {g | θ * (g ⬝ᵥ M *ᵥ g) < (g ⬝ᵥ v) ^ 2} := by
  have h := gauss_block_z v (θ • M)
    (fun y => by rw [qform_smul]; exact mul_nonneg hθ (hM y)) ht0 ht1
    (by rw [trace_smul, smul_eq_mul]; exact hv)
  simpa only [qform_smul] using h

theorem gauss_block_theta (v : ι → ℝ) (M : Matrix ι ι ℝ) (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y)
    {θ : ℝ} (hθ : 0 ≤ θ) (hv : θ * M.trace < v ⬝ᵥ v) :
    3 / 25 < (stdGauss ι).real {g | θ * (g ⬝ᵥ M *ᵥ g) < (g ⬝ᵥ v) ^ 2} :=
  tail_one_gt.trans
    (gauss_block_theta_z v M hM hθ one_pos le_rfl (by rw [one_pow, one_mul]; exact hv))

/-! ## A numeric lower bound for the tail -/

lemma exp_neg_le_quad {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h1 : 1 + y + y ^ 2 / 2 ≤ Real.exp y := Real.quadratic_le_exp_of_nonneg hy
  have hp : 0 < 1 + y + y ^ 2 / 2 := by positivity
  rw [Real.exp_neg]
  calc (Real.exp y)⁻¹ ≤ (1 + y + y ^ 2 / 2)⁻¹ := inv_anti₀ hp h1
    _ ≤ 1 - y + y ^ 2 / 2 := by
      rw [← one_div, div_le_iff₀ hp]
      have : (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) = 1 + y ^ 4 / 4 := by ring
      rw [this]
      have : 0 ≤ y ^ 4 / 4 := by positivity
      linarith

lemma pdf_le_poly (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (√(2 * Real.pi))⁻¹ * (1 - x ^ 2 / 2 + x ^ 4 / 8) := by
  rw [pdf_eq]
  have h := exp_neg_le_quad (y := x ^ 2 / 2) (by positivity)
  have hc : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (h.trans (le_of_eq ?_)) hc
  ring

lemma integral_poly {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    ∫ x in Ioc 0 t, c * (1 - x ^ 2 / 2 + x ^ 4 / 8) = c * (t - t ^ 3 / 6 + t ^ 5 / 40) := by
  rw [← intervalIntegral.integral_of_le ht]
  have hderiv : ∀ x ∈ uIcc 0 t, HasDerivAt (fun x : ℝ => c * (x - x ^ 3 / 6 + x ^ 5 / 40))
      (c * (1 - x ^ 2 / 2 + x ^ 4 / 8)) x := by
    intro x _
    have h := (((hasDerivAt_id' x).sub (((hasDerivAt_id' x).pow 3).div_const 6)).add
      (((hasDerivAt_id' x).pow 5).div_const 40)).const_mul c
    convert h using 1
    congr 1
    norm_num
    try ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

theorem tail_zero : (gaussianReal 0 1).real (Ioi 0) = 1 / 2 := by
  have h1 : (gaussianReal 0 1).real (Iio 0) = (gaussianReal 0 1).real (Ioi 0) := by
    have := BstLean.Part131.tail_neg 0
    rwa [neg_zero] at this
  have h2 : (gaussianReal 0 1).real (Ici 0) = (gaussianReal 0 1).real (Ioi 0) := by
    rw [gauss_real_eq, gauss_real_eq, integral_Ici_eq_integral_Ioi]
  have hd : Disjoint (Iio (0 : ℝ)) (Ici 0) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact not_lt.mpr (show (0 : ℝ) ≤ x from hx') hx
  have h3 := measureReal_union (μ := gaussianReal 0 1) hd measurableSet_Ici
  rw [Iio_union_Ici] at h3
  have h4 : (gaussianReal 0 1).real univ = 1 := by simp
  linarith

/-- numeric tail bound -/
theorem tail_lower {t : ℝ} (ht : 0 ≤ t) :
    1 / 2 - (√(2 * Real.pi))⁻¹ * (t - t ^ 3 / 6 + t ^ 5 / 40) ≤
      (gaussianReal 0 1).real (Ioi t) := by
  have hint := integrable_gaussianPDFReal 0 1
  have hu : Ioi (0 : ℝ) = Ioc 0 t ∪ Ioi t := (Ioc_union_Ioi_eq_Ioi ht).symm
  have hd : Disjoint (Ioc 0 t) (Ioi t) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
  have h0 := tail_zero
  rw [hu, measureReal_union hd measurableSet_Ioi, gauss_real_eq (Ioc 0 t)] at h0
  have hpoly : IntegrableOn (fun x : ℝ => (√(2 * Real.pi))⁻¹ * (1 - x ^ 2 / 2 + x ^ 4 / 8))
      (Ioc 0 t) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
  have h1 : ∫ x in Ioc 0 t, gaussianPDFReal 0 1 x ≤
      ∫ x in Ioc 0 t, (√(2 * Real.pi))⁻¹ * (1 - x ^ 2 / 2 + x ^ 4 / 8) :=
    setIntegral_mono_on hint.integrableOn hpoly measurableSet_Ioc fun x _ => pdf_le_poly x
  rw [integral_poly ht] at h1
  linarith

theorem tail_five_eighths : 2659 / 10000 < (gaussianReal 0 1).real (Ioi (5 / 8)) := by
  have hpi := Real.pi_gt_d6
  have hsq : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h1 : (2506624 / 1000000 : ℝ) < √(2 * Real.pi) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num at hpi ⊢
    linarith
  have hc : (√(2 * Real.pi))⁻¹ < 398943 / 1000000 := by
    rw [inv_lt_comm₀ hsq (by norm_num)]
    refine lt_of_le_of_lt ?_ h1
    norm_num
  have h := tail_lower (t := 5 / 8) (by norm_num)
  have hP : (0 : ℝ) < 5 / 8 - (5 / 8) ^ 3 / 6 + (5 / 8) ^ 5 / 40 := by norm_num
  have h2 := mul_lt_mul_of_pos_right hc hP
  have hnum : (2659 / 10000 : ℝ) <
      1 / 2 - 398943 / 1000000 * (5 / 8 - (5 / 8) ^ 3 / 6 + (5 / 8) ^ 5 / 40) := by norm_num
  linarith

end BstLean.Part135

open BstLean.Part135 in
#print axioms tail_line_at
open BstLean.Part135 in
#print axioms gauss_block_z
open BstLean.Part135 in
#print axioms gauss_block_theta_z
open BstLean.Part135 in
#print axioms gauss_block_theta
open BstLean.Part135 in
#print axioms tail_lower
open BstLean.Part135 in
#print axioms tail_five_eighths
