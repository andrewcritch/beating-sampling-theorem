import BstLean.Part202Variance
import BstLean.Part202Coefficient
import BstLean.Part184Core

/-! BE bounds for a Gaussian row with retained plane coordinates. -/
namespace BstLean.Part202
open MeasureTheory ProbabilityTheory Real Filter Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170
open BstLean.Part184 (rowG rowE rowV)
open BstLean.Part162 (gmom gmom_nonneg)

section
variable {V P : Type*} [MeasurableSpace V] [MeasurableSpace P]
variable {μ : Measure V} [IsProbabilityMeasure μ]
variable {ν : Measure P} [IsProbabilityMeasure ν] {d m : ℕ}

/-- Retained coordinates and fresh transverse coordinates reassemble one whole row.
The input distribution is fixed before these coordinates are drawn. -/
structure RowSplit (μ : Measure V) (ν : Measure P) (a : V → Fin d → ℝ)
    (m : ℕ) (ell : ℝ) where
  c : P → V → ℝ
  w : V → Fin m → ℝ
  assemble : P × (Fin m → ℝ) → Fin d → ℝ
  measurable_c : Measurable (Function.uncurry c)
  measurable_w : Measurable w
  bounded_c : ∀ ξ, ∃ Kc, ∀ v, |c ξ v| ≤ Kc
  bounded_w : ∃ Kw, ∀ v, ‖w v‖ ≤ Kw
  mean_w : ∀ i, ∫ v, w v i ∂μ = 0
  covariance_w : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ ell ^ 2 * normSq e
  measurable_assemble : Measurable assemble
  gaussian_assemble : Measure.map assemble (ν.prod (stdGauss (Fin m))) = stdGauss (Fin d)
  row_identity : ∀ ξ η v, c ξ v + η ⬝ᵥ w v = assemble (ξ, η) ⬝ᵥ a v

variable {a : V → Fin d → ℝ} {ell : ℝ}

/-- Only the fresh transverse coordinates are integrated in the conditional mean. -/
noncomputable def rowFluct (S : RowSplit μ ν a m ell) (p : P × (Fin m → ℝ)) : ℝ :=
  rowE μ (S.c p.1) S.w 1 p.2 -
    ∫ η, rowE μ (S.c p.1) S.w 1 η ∂stdGauss (Fin m)

lemma RowSplit.measurable_energy (S : RowSplit μ ν a m ell) :
    Measurable (fun p : P × (Fin m → ℝ) => rowE μ (S.c p.1) S.w 1 p.2) := by
  have h : Measurable (fun q : (P × (Fin m → ℝ)) × V =>
      relu (S.c q.1.1 q.2 + q.1.2 ⬝ᵥ S.w q.2) ^ 2) :=
    (measurable_relu.comp ((S.measurable_c.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).add
        (measurable_dot (measurable_snd.comp measurable_fst)
          (S.measurable_w.comp measurable_snd)))).pow_const 2
  simpa only [rowE, rowG, Real.sqrt_one, one_mul] using
    h.stronglyMeasurable.integral_prod_right'.measurable

lemma RowSplit.measurable_fluct (S : RowSplit μ ν a m ell) : Measurable (rowFluct S) := by
  have hm : Measurable (fun ξ : P =>
      ∫ η, rowE μ (S.c ξ) S.w 1 η ∂stdGauss (Fin m)) :=
    (S.measurable_energy.stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin m))).measurable
  exact S.measurable_energy.sub (hm.comp measurable_fst)

lemma RowSplit.variance_identity (S : RowSplit μ ν a m ell)
    (ξ : P) (η : Fin m → ℝ) :
    rowV μ (S.c ξ) S.w 1 η = wholeVariance μ a (S.assemble (ξ, η)) := by
  unfold wholeVariance
  unfold rowV rowG
  simp only [Real.sqrt_one, one_mul, zero_add, S.row_identity]

/-- Plane integration restores the complete Gaussian distribution for variance powers. -/
lemma RowSplit.variance_integral (S : RowSplit μ ν a m ell) (ha : Measurable a) (p : ℕ) :
    ∫⁻ ξ, ∫⁻ η, ENNReal.ofReal (rowV μ (S.c ξ) S.w 1 η ^ p)
      ∂stdGauss (Fin m) ∂ν =
    ∫⁻ z, ENNReal.ofReal (wholeVariance μ a z ^ p) ∂stdGauss (Fin d) := by
  let f : (Fin d → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (wholeVariance μ a z ^ p)
  have hf : Measurable f := (measurable_wholeVariance ha).pow_const p |>.ennreal_ofReal
  simp_rw [S.variance_identity]
  change (∫⁻ ξ, ∫⁻ η, f (S.assemble (ξ, η)) ∂stdGauss (Fin m) ∂ν) =
    ∫⁻ z, f z ∂stdGauss (Fin d)
  calc _ = ∫⁻ q, f (S.assemble q) ∂ν.prod (stdGauss (Fin m)) :=
        (lintegral_prod _ (hf.comp S.measurable_assemble).aemeasurable).symm
    _ = ∫⁻ z, f z ∂Measure.map S.assemble (ν.prod (stdGauss (Fin m))) :=
        (lintegral_map hf S.measurable_assemble).symm
    _ = _ := by rw [S.gaussian_assemble]

lemma row_conditional_variance (S : RowSplit μ ν a m ell) (ξ : P) :
    ∫⁻ η, ENNReal.ofReal (|rowFluct S (ξ, η)| ^ 2) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (4 * ell ^ 2) *
        ∫⁻ η, ENNReal.ofReal (rowV μ (S.c ξ) S.w 1 η) ∂stdGauss (Fin m) := by
  obtain ⟨Kc, hKc⟩ := S.bounded_c ξ
  obtain ⟨Kw, hKw⟩ := S.bounded_w
  have hc : Measurable (S.c ξ) := S.measurable_c.comp (measurable_const.prodMk measurable_id)
  have ie1 : Integrable (rowE μ (S.c ξ) S.w 1) (stdGauss (Fin m)) := by
    simpa only [pow_one] using BstLean.Part184.rowE_pow_integrable
      hc S.measurable_w hKc hKw S.mean_w (sq_nonneg ell) S.covariance_w (by norm_num) 1
  have ie2 := BstLean.Part184.rowE_pow_integrable
    hc S.measurable_w hKc hKw S.mean_w (sq_nonneg ell) S.covariance_w
      (by norm_num : (0 : ℝ) ≤ 1) 2
  have me : Measurable (rowE μ (S.c ξ) S.w 1) :=
    S.measurable_energy.comp (measurable_const.prodMk measurable_id)
  have if2 := BstLean.Part184.int_dev me (fun η => BstLean.Part184.rowE_nonneg 1 η) ie2
    (∫ η, rowE μ (S.c ξ) S.w 1 η ∂stdGauss (Fin m))
  have mv := BstLean.Part184.measurable_rowV (μ := μ) hc S.measurable_w 1
  have v0 := BstLean.Part184.rowV_nonneg (μ := μ) hc S.measurable_w hKc hKw 1
  have iv : Integrable (rowV μ (S.c ξ) S.w 1) (stdGauss (Fin m)) :=
    ie1.mono' mv.aestronglyMeasurable (Eventually.of_forall fun η => by
      rw [Real.norm_eq_abs, abs_of_nonneg (v0 η)]
      exact BstLean.Part184.rowV_le_rowE 1 η)
  have hs := BstLean.Part184.row_var_sharp hc S.measurable_w hKc hKw
    S.mean_w (sq_nonneg ell) S.covariance_w (by norm_num : (0 : ℝ) ≤ 1)
  simp only [one_mul] at hs
  unfold rowFluct
  rw [← ofReal_integral_eq_lintegral_ofReal if2
    (Eventually.of_forall fun η => pow_nonneg (abs_nonneg _) 2),
    ← ofReal_integral_eq_lintegral_ofReal iv (Eventually.of_forall v0),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [rowFluct, sq_abs] using hs

/-- A complete row has variance at most `2 ell^2 tr H` after plane integration. -/
theorem row_variance (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) :
    ∫⁻ p, ENNReal.ofReal (|rowFluct S p| ^ 2) ∂ν.prod (stdGauss (Fin m)) ≤
      ENNReal.ofReal (2 * ell ^ 2 * covarianceTrace μ a) := by
  rw [lintegral_prod _ (S.measurable_fluct.abs.pow_const 2 |>.ennreal_ofReal).aemeasurable]
  refine (lintegral_mono fun ξ => row_conditional_variance S ξ).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have he := S.variance_integral ha 1
  simp only [pow_one] at he
  rw [he]
  refine (mul_le_mul' le_rfl (wholeVariance_mean ha hK)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma gmom_eq_gaussMom (p : ℕ) : gmom (2 * p) = BstLean.Part29.gaussMom (2 * p) := by
  unfold gmom
  simp_rw [Even.pow_abs (show Even (2 * p) from ⟨p, by omega⟩)]
  exact BstLean.Part29.gaussMom_eq _

/-- Even whole-row moments use the exact squared odd double factorial. -/
theorem row_even_moment (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ q, ENNReal.ofReal (|rowFluct S q| ^ (2 * p)) ∂ν.prod (stdGauss (Fin m)) ≤
      ENNReal.ofReal (evenCoefficient p * (ell ^ 2 * covarianceTrace μ a) ^ p) := by
  rw [lintegral_prod _ (S.measurable_fluct.abs.pow_const _ |>.ennreal_ofReal).aemeasurable]
  have hrow : ∀ ξ, ∫⁻ η, ENNReal.ofReal (|rowFluct S (ξ, η)| ^ (2 * p))
      ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((π / 2) ^ (2 * p) * gmom (2 * p) * (4 * ell ^ 2) ^ p) *
        ∫⁻ η, ENNReal.ofReal (rowV μ (S.c ξ) S.w 1 η ^ p) ∂stdGauss (Fin m) := by
    intro ξ
    obtain ⟨Kc, hKc⟩ := S.bounded_c ξ
    obtain ⟨Kw, hKw⟩ := S.bounded_w
    have hc : Measurable (S.c ξ) :=
      S.measurable_c.comp (measurable_const.prodMk measurable_id (α := V))
    simpa only [rowFluct, one_mul] using BstLean.Part184.row_mom_p hc S.measurable_w
      hKc hKw S.mean_w (sq_nonneg ell) S.covariance_w (by norm_num : (0 : ℝ) ≤ 1) hp
  refine (lintegral_mono hrow).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, S.variance_integral ha p]
  refine (mul_le_mul' le_rfl (wholeVariance_moment ha hK hp)).trans (le_of_eq ?_)
  have hgm := gmom_nonneg (2 * p)
  rw [← ENNReal.ofReal_mul (by positivity), ← gmom_eq_gaussMom p]
  congr 1
  unfold evenCoefficient
  have hpi : (π / 2) ^ (2 * p) * 4 ^ p = π ^ (2 * p) := by
    rw [pow_mul, ← mul_pow, div_pow]
    norm_num
    exact (pow_mul π 2 p).symm
  simp only [mul_pow]
  calc (π / 2) ^ (2 * p) * gmom (2 * p) * (4 ^ p * (ell ^ 2) ^ p) *
      (gmom (2 * p) * covarianceTrace μ a ^ p) =
      ((π / 2) ^ (2 * p) * 4 ^ p) * gmom (2 * p) ^ 2 *
        (ell ^ 2) ^ p * covarianceTrace μ a ^ p := by ring
    _ = _ := by rw [hpi]; ring

end
end BstLean.Part202
