import BstLean.Part144Block

/-!
# Part 144, the tangent form of the block bound, and two numeric tails

Role: `delegations/statements/p144-spec.md` (tools for the sharper form of item 2).
`Φ̄(t) = (gaussianReal 0 1).real (Ioi t)`, `φ = gaussianPDFReal 0 1`.

* `gauss_block_tangent`: `yᵀMy ≥ 0`, `D = |v|² > 0`, `a = vᵀMv/D < D`, `t0 > 0` ⇒
  `Pr(gᵀMg < (g·v)²) ≥ Φ̄(t0) + (φ(t0)/(2t0))·(t0² − (tr M − a)/(D − a))`.
* `tail_of_mills`: a numeric form of `mills_lower` at `t = √z`.
* `tail_5`: `Φ̄(√5) > 0.01215`; `tail_52`: `Φ̄(√(26/5)) > 0.01085`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144
open MeasureTheory ProbabilityTheory Set Matrix Filter
open scoped Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part131 BstLean.Part135

/-- **The tangent form of the block bound.** With `D = |v|² > 0`, `a = vᵀMv/D` (the Rayleigh
quotient of `M` along `v`), `a < D`, and any level `t0 > 0`:
`Pr(gᵀMg < (g·v)²) ≥ Φ̄(t0) + (φ(t0)/(2t0))·(t0² − (tr M − a)/(D − a))`. -/
theorem gauss_block_tangent {ι : Type} [Fintype ι] (v : ι → ℝ) (M : Matrix ι ι ℝ)
    (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y) {t0 : ℝ} (ht0 : 0 < t0)
    (hD0 : 0 < v ⬝ᵥ v) (hδ0 : v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v) < v ⬝ᵥ v) :
    (gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) *
        (t0 ^ 2 - (M.trace - v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v)) /
          (v ⬝ᵥ v - v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v))) ≤
      (stdGauss ι).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} := by
  classical
  set D : ℝ := v ⬝ᵥ v with hD
  have hDpos : 0 < D := hD0
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
  have haR : a = v ⬝ᵥ M *ᵥ v / D := by
    rw [ha, he_def, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← hss]
    field_simp
  rw [← haR] at hδ0 ⊢
  set δ : ℝ := D - a with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
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
  exact hmono

/-- A numeric form of the Mills bound at `t = √z`: from `tl ≤ √z` (as `tl² ≤ z`) and
`exp(z/2) ≤ E`: `(100000/250664)·(1/E)·(tl/(1 + z)) ≤ Φ̄(√z)`. -/
theorem tail_of_mills {z tl E : ℝ} (hz : 0 < z) (htl0 : 0 ≤ tl) (htl : tl ^ 2 ≤ z)
    (hE0 : 0 < E) (hE : Real.exp (z / 2) ≤ E) :
    (100000 / 250664 : ℝ) * (1 / E) * (tl / (1 + z)) ≤
      (gaussianReal 0 1).real (Ioi (Real.sqrt z)) := by
  set t : ℝ := Real.sqrt z with ht
  have htsq : t ^ 2 = z := Real.sq_sqrt hz.le
  have ht1 : tl ≤ t := by rw [ht]; exact Real.le_sqrt_of_sq_le htl
  have htpos : 0 < t := Real.sqrt_pos.mpr hz
  have hm := mills_lower htpos
  rw [htsq, pdf_eq, htsq] at hm
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
  have hEn : 1 / E ≤ Real.exp (-(z / 2)) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) hE
  have hprod : (100000 / 250664 : ℝ) * (1 / E) ≤ (√(2 * Real.pi))⁻¹ * Real.exp (-(z / 2)) :=
    mul_le_mul hc hEn (by positivity) (by positivity)
  have hfrac : tl / (1 + z) ≤ t / (1 + z) := div_le_div_of_nonneg_right ht1 (by positivity)
  have hall := mul_le_mul hprod hfrac (by positivity) (by positivity)
  exact hall.trans hm

/-- `exp 1 ≤ 2.7182818286`. -/
lemma exp_one_le144 : Real.exp 1 ≤ 27182818286 / 10000000000 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  norm_num at he ⊢; linarith

/-- **`Φ̄(√5) > 0.01215`.** -/
theorem tail_5 : (1215 : ℝ) / 100000 < (gaussianReal 0 1).real (Ioi (Real.sqrt 5)) := by
  have he := exp_one_le144
  have hp1 := Real.exp_pos 1
  have hq : Real.exp (1 / 2) ≤ 164873 / 100000 := by
    by_contra hcon
    have hlt : (164873 / 100000 : ℝ) < Real.exp (1 / 2) := not_le.mp hcon
    have h4 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h5 : (164873 / 100000 : ℝ) ^ 2 < Real.exp (1 / 2) ^ 2 :=
      pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
    rw [h4] at h5
    norm_num at h5 he
    linarith
  have hE : Real.exp (5 / 2) ≤ 27182818286 / 10000000000 * (27182818286 / 10000000000) *
      (164873 / 100000) := by
    have e : Real.exp (5 / 2) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [e]
    have := mul_le_mul he he hp1.le (by norm_num)
    exact mul_le_mul this hq (Real.exp_pos _).le (by norm_num)
  have h := tail_of_mills (z := 5) (tl := 223606 / 100000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hE
  refine lt_of_lt_of_le ?_ h
  norm_num

/-- **`Φ̄(√(26/5)) > 0.01085`.** -/
theorem tail_52 : (1085 : ℝ) / 100000 < (gaussianReal 0 1).real (Ioi (Real.sqrt (26 / 5))) := by
  have he := exp_one_le144
  have hp1 := Real.exp_pos 1
  have hq : Real.exp (3 / 5) ≤ 18222 / 10000 := by
    by_contra hcon
    have hlt : (18222 / 10000 : ℝ) < Real.exp (3 / 5) := not_le.mp hcon
    have h4 : Real.exp (3 / 5) ^ 5 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h5 : (18222 / 10000 : ℝ) ^ 5 < Real.exp (3 / 5) ^ 5 :=
      pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
    rw [h4] at h5
    have h6 : Real.exp 1 ^ 3 ≤ (27182818286 / 10000000000 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hp1.le he 3
    norm_num at h5 h6
    linarith
  have hE : Real.exp (26 / 5 / 2) ≤ 27182818286 / 10000000000 * (27182818286 / 10000000000) *
      (18222 / 10000) := by
    have e : Real.exp (26 / 5 / 2) = Real.exp 1 * Real.exp 1 * Real.exp (3 / 5) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [e]
    have := mul_le_mul he he hp1.le (by norm_num)
    exact mul_le_mul this hq (Real.exp_pos _).le (by norm_num)
  have h := tail_of_mills (z := 26 / 5) (tl := 228035 / 100000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hE
  refine lt_of_lt_of_le ?_ h
  norm_num

end BstLean.Part144

open BstLean.Part144 in
#print axioms gauss_block_tangent
open BstLean.Part144 in
#print axioms tail_5
open BstLean.Part144 in
#print axioms tail_52
