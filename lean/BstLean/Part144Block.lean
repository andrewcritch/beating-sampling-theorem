import BstLean.Part135Block

/-!
# Part 144, the Gaussian block lemma with any level `t0 > 0`, and a Mills lower bound

Role: `delegations/statements/p144-spec.md` (tools for item 2, `sampleFails144`).
`Φ̄(t) = (gaussianReal 0 1).real (Ioi t)`.

* `gauss_block_op`: `yᵀMy ≥ 0`, `yᵀMy ≤ a₀|y|²`, `a₀ ≥ 0`, `t0 > 0`,
  `tr M < t0²(|v|² − a₀)` ⇒ `Pr(gᵀMg < (g·v)²) > Φ̄(t0)`. It generalizes
  `BstLean.Part135.gauss_block_z` (which needs `t0 ≤ 1`).
* `mills_lower`: `Φ̄(t) ≥ φ(t)·t/(1 + t²)` for `t > 0`.
* `tail_144`: `Φ̄(√(9/2)) > 161/10000`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144
open MeasureTheory ProbabilityTheory Set Matrix Filter
open scoped Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part131 BstLean.Part135

/-- **The Gaussian block lemma with any level `t0 > 0` and an operator bound `a₀ ≥ 0` of `M`.** -/
theorem gauss_block_op {ι : Type} [Fintype ι] (v : ι → ℝ) (M : Matrix ι ι ℝ)
    (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y) {a₀ t0 : ℝ} (ha₀ : 0 ≤ a₀)
    (hop : ∀ y : ι → ℝ, y ⬝ᵥ M *ᵥ y ≤ a₀ * (y ⬝ᵥ y))
    (ht0 : 0 < t0) (hv : M.trace < t0 ^ 2 * (v ⬝ᵥ v - a₀)) :
    (gaussianReal 0 1).real (Ioi t0) < (stdGauss ι).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} := by
  classical
  have htr : 0 ≤ M.trace := by
    rw [← qform_integral]; exact integral_nonneg fun h => hM h
  have ht0sq : 0 < t0 ^ 2 := by positivity
  set D : ℝ := v ⬝ᵥ v with hD
  have hDa : 0 < D - a₀ := by
    by_contra hcon
    have : D - a₀ ≤ 0 := not_lt.mp hcon
    nlinarith
  have hDpos : 0 < D := by linarith
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
  have haa : a ≤ a₀ := by
    have := hop e
    rw [he, mul_one] at this
    exact this
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
    have h5 : t0 ^ 2 * (D - a₀) ≤ t0 ^ 2 * (D - a) :=
      mul_le_mul_of_nonneg_left (by linarith) ht0sq.le
    linarith
  have h3 : 0 < c * (t0 ^ 2 - (M.trace - a) / δ) := mul_pos hcpos h1
  linarith

/-- The derivative of the standard Gaussian density. -/
lemma pdf_hasDerivAt (x : ℝ) : HasDerivAt (fun x : ℝ => gaussianPDFReal 0 1 x)
    (gaussianPDFReal 0 1 x * (-x)) x := by
  have h2 : HasDerivAt (fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)))
      ((√(2 * Real.pi))⁻¹ * (Real.exp (-(x ^ 2 / 2)) * (-(2 * x ^ 1 * 1 / 2)))) x :=
    (((hasDerivAt_id x).pow 2).div_const 2).neg.exp.const_mul _
  have e : (fun x : ℝ => gaussianPDFReal 0 1 x) =
      fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := funext pdf_eq
  rw [e, pdf_eq]
  convert h2 using 1; ring

/-- **The Mills lower bound**: `Φ̄(t) ≥ φ(t)·t/(1 + t²)` for `t > 0`. -/
theorem mills_lower {t : ℝ} (ht : 0 < t) :
    gaussianPDFReal 0 1 t * (t / (1 + t ^ 2)) ≤ (gaussianReal 0 1).real (Ioi t) := by
  have hint := integrable_gaussianPDFReal 0 1
  rw [gauss_real_eq]
  set K : ℝ := 1 + 1 / t ^ 2 with hK
  have hKpos : 0 < K := by positivity
  let f : ℝ → ℝ := fun x => -(gaussianPDFReal 0 1 x / x)
  let f' : ℝ → ℝ := fun x => gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)
  have hderiv : ∀ x ∈ Ici t, HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ht hx).ne'
    have h3 := ((pdf_hasDerivAt x).div (hasDerivAt_id x) hx0).neg
    have h4 : HasDerivAt f
        (-((gaussianPDFReal 0 1 x * -x * id x - gaussianPDFReal 0 1 x * 1) / id x ^ 2)) x := h3
    have e4 : f' x =
        -((gaussianPDFReal 0 1 x * -x * id x - gaussianPDFReal 0 1 x * 1) / id x ^ 2) := by
      simp only [f', id]
      field_simp
      ring
    rw [e4]; exact h4
  have hbd : ∀ x : ℝ, t < x → 1 + 1 / x ^ 2 ≤ K := by
    intro x hx
    have h1 : t ^ 2 ≤ x ^ 2 := by nlinarith
    have h2 : 1 / x ^ 2 ≤ 1 / t ^ 2 := one_div_le_one_div_of_le (by positivity) h1
    rw [hK]; linarith
  have hf'int : IntegrableOn f' (Ioi t) := by
    refine Integrable.mono' (hint.const_mul K).integrableOn
      ((hint.aestronglyMeasurable.mul (measurable_const.add
        (measurable_const.div (measurable_id.pow_const 2))).aestronglyMeasurable).restrict) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hx1 : t < x := hx
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h2 := hbd x hx1
    have h3 : 0 ≤ 1 / x ^ 2 := by positivity
    simp only [f', Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have htend : Tendsto f atTop (𝓝 0) := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖f x‖ ≤ phi1 * Real.exp (1 / 2) * x⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [f, norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) hx.le), pdf_eq_phi1,
        div_eq_mul_inv]
      have : Real.exp ((1 - x ^ 2) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      have h2 := phi1_pos
      have h3 : 0 < x⁻¹ := inv_pos.mpr hx
      gcongr
    have h0 : Tendsto (fun x : ℝ => phi1 * Real.exp (1 / 2) * x⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (phi1 * Real.exp (1 / 2))
    exact squeeze_zero_norm' hb h0
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hf'int htend
  have hle : ∫ x in Ioi t, f' x ≤ ∫ x in Ioi t, K * gaussianPDFReal 0 1 x := by
    refine setIntegral_mono_on hf'int (hint.const_mul K).integrableOn measurableSet_Ioi ?_
    intro x hx
    have hx1 : t < x := hx
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h2 := hbd x hx1
    simp only [f']
    nlinarith
  rw [integral_const_mul, hI] at hle
  have hft : f t = -(gaussianPDFReal 0 1 t / t) := rfl
  rw [hft, zero_sub, neg_neg] at hle
  have e : gaussianPDFReal 0 1 t * (t / (1 + t ^ 2)) = gaussianPDFReal 0 1 t / t / K := by
    rw [hK]; field_simp; ring
  rw [e, div_le_iff₀ hKpos]
  linarith

/-- **A numeric tail bound at `t0 = √(9/2)`**: `Φ̄(√(9/2)) > 161/10000`. -/
theorem tail_144 : (161 : ℝ) / 10000 < (gaussianReal 0 1).real (Ioi (Real.sqrt (9 / 2))) := by
  set t : ℝ := Real.sqrt (9 / 2) with ht
  have htsq : t ^ 2 = 9 / 2 := Real.sq_sqrt (by norm_num)
  have ht1 : (21213 / 10000 : ℝ) ≤ t := by
    rw [ht]; exact Real.le_sqrt_of_sq_le (by norm_num)
  have htpos : 0 < t := by linarith
  have hm := mills_lower htpos
  rw [htsq, pdf_eq, htsq] at hm
  -- `√(2π) ≤ 2.50664`
  have hpi := Real.pi_lt_d6
  have hsq : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h1 : √(2 * Real.pi) ≤ 250664 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num at hpi ⊢
    linarith
  have hc : (100000 / 250664 : ℝ) ≤ (√(2 * Real.pi))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hsq]
    refine h1.trans (le_of_eq ?_)
    norm_num
  -- `exp(9/4) ≤ 2.7182818286² · 1.2841`
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hq : Real.exp (1 / 4) ≤ 12841 / 10000 := by
    by_contra hcon
    have hlt : (12841 / 10000 : ℝ) < Real.exp (1 / 4) := not_le.mp hcon
    have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h5 : (12841 / 10000 : ℝ) ^ 4 < Real.exp (1 / 4) ^ 4 :=
      pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
    rw [h4] at h5
    norm_num at h5 he
    linarith
  have hE : Real.exp (9 / 4) ≤ 27182818286 / 10000000000 * (27182818286 / 10000000000) *
      (12841 / 10000) := by
    have e : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [e]
    have hp1 := Real.exp_pos 1
    have he' : Real.exp 1 ≤ 27182818286 / 10000000000 := by norm_num at he ⊢; linarith
    have := mul_le_mul he' he' hp1.le (by norm_num)
    exact mul_le_mul this hq (Real.exp_pos _).le (by norm_num)
  have hEn : (1 / (27182818286 / 10000000000 * (27182818286 / 10000000000) *
      (12841 / 10000)) : ℝ) ≤ Real.exp (-(9 / 2 / 2)) := by
    have e : Real.exp (-(9 / 2 / 2)) = (Real.exp (9 / 4))⁻¹ := by
      rw [← Real.exp_neg]; norm_num
    rw [e, one_div]
    exact inv_anti₀ (Real.exp_pos _) hE
  have hprod : (100000 / 250664 : ℝ) * (1 / (27182818286 / 10000000000 *
      (27182818286 / 10000000000) * (12841 / 10000))) ≤
      (√(2 * Real.pi))⁻¹ * Real.exp (-(9 / 2 / 2)) :=
    mul_le_mul hc hEn (by norm_num) (by positivity)
  have hfrac : (21213 / 10000 : ℝ) / (1 + 9 / 2) ≤ t / (1 + 9 / 2) :=
    div_le_div_of_nonneg_right ht1 (by norm_num)
  have hall := mul_le_mul hprod hfrac (by norm_num) (by positivity)
  refine lt_of_lt_of_le ?_ (hall.trans hm)
  norm_num

end BstLean.Part144

open BstLean.Part144 in
#print axioms gauss_block_op
open BstLean.Part144 in
#print axioms mills_lower
open BstLean.Part144 in
#print axioms tail_144
