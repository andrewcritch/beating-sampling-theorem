import BstLean.Part130Kappa
import BstLean.Part130Sym
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Part 130, item 3: the row formula

Paper source: `delegations/answers/onW2c-cx.md` §3 (4), `delegations/answers/onW4c-cx.md` §2.
* `core2D`: for a standard Gaussian `ξ` in `ℝ²` and `0 ≤ ψ ≤ π`:
  `2·E[ξ₀⁺ (cos ψ·ξ₀ + sin ψ·ξ₁)⁺] = κ(cos ψ)`.
* `row_formula_std`: for a standard Gaussian vector `w` in `ℝ^k` and fixed `h, h′`:
  `2·E[(w·h)⁺ (w·h′)⁺] = |h||h′|·κ(⟨h, h′⟩/(|h||h′|))`.
* `row_formula`: the same for one row of a Gaussian matrix with variance `v`.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)

variable {k m : ℕ}

/-! ## The angular integral -/

lemma cos_mul_cos_antideriv (ψ θ : ℝ) :
    HasDerivAt (fun θ => (θ * cos ψ + sin (2 * θ - ψ) / 2) / 2) (cos θ * cos (θ - ψ)) θ := by
  have d1 : HasDerivAt (fun θ : ℝ => 2 * θ - ψ) 2 θ := by
    simpa using ((hasDerivAt_id θ).const_mul 2).sub_const ψ
  have d2 := ((hasDerivAt_id θ).mul_const (cos ψ)).add ((d1.sin).div_const 2)
  have d3 := d2.div_const 2
  have d4 : HasDerivAt (fun θ => (θ * cos ψ + sin (2 * θ - ψ) / 2) / 2) _ θ := d3
  convert d4 using 1
  have e1 : cos (2 * θ - ψ) = cos θ * cos (θ - ψ) - sin θ * sin (θ - ψ) := by
    rw [← cos_add]; ring_nf
  have e2 : cos ψ = cos θ * cos (θ - ψ) + sin θ * sin (θ - ψ) := by
    rw [← cos_sub]; ring_nf
  rw [e1, e2]
  ring

lemma angular {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) :
    ∫ θ in Ioo (-π) π, relu (cos θ) * relu (cos (θ - ψ)) =
      (sin ψ + (π - ψ) * cos ψ) / 2 := by
  have hp := pi_pos
  have hcont : Continuous (fun θ : ℝ => relu (cos θ) * relu (cos (θ - ψ))) :=
    (continuous_relu.comp continuous_cos).mul
      (continuous_relu.comp (continuous_cos.comp (continuous_id.sub continuous_const)))
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => relu (cos θ) * relu (cos (θ - ψ)))
      volume a b := fun a b => hcont.intervalIntegrable a b
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-π) (ψ - π / 2)) (hint (ψ - π / 2) π),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (ψ - π / 2) (π / 2)) (hint (π / 2) π)]
  have z1 : ∫ θ in (-π)..(ψ - π / 2), relu (cos θ) * relu (cos (θ - ψ)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      by_cases hc : θ ≤ -(π / 2)
      · have : cos θ ≤ 0 := by
          rw [← cos_neg]
          exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [relu_of_nonpos this]
      · have : cos (θ - ψ) ≤ 0 := by
          rw [← cos_neg]
          exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [relu_of_nonpos this]
  have z3 : ∫ θ in (π / 2)..π, relu (cos θ) * relu (cos (θ - ψ)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      have : cos θ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le ha (by linarith)
      simp [relu_of_nonpos this]
  have z2 : ∫ θ in (ψ - π / 2)..(π / 2), relu (cos θ) * relu (cos (θ - ψ)) =
      (sin ψ + (π - ψ) * cos ψ) / 2 := by
    rw [intervalIntegral.integral_congr (g := fun θ => cos θ * cos (θ - ψ))]
    · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ => cos_mul_cos_antideriv ψ θ)
        ((continuous_cos.mul (continuous_cos.comp
          (continuous_id.sub continuous_const))).intervalIntegrable _ _)]
      rw [show 2 * (π / 2) - ψ = π - ψ by ring, sin_pi_sub,
        show 2 * (ψ - π / 2) - ψ = ψ - π by ring, sin_sub_pi]
      ring
    · intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      have c1 : 0 ≤ cos θ := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hb
      have c2 : 0 ≤ cos (θ - ψ) :=
        cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
      simp only [relu_of_nonneg c1, relu_of_nonneg c2]
  rw [z1, z2, z3]
  ring

/-! ## The radial integral -/

lemma radial : ∫ r in Ioi (0 : ℝ), r ^ 3 * exp (-r ^ 2 / 2) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∫ r in Ioi (0 : ℝ), r ^ 3 * exp (-r ^ 2 / 2) =
      ∫ r in Ioi (0 : ℝ), r ^ (3 : ℝ) * exp (-(1 / 2) * r ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      rpow_natCast, rpow_natCast]
    congr 2
    ring
  rw [e, h]
  rw [show (3 + 1 : ℝ) / 2 = 2 by norm_num, show -(3 + 1 : ℝ) / 2 = -2 by norm_num, Gamma_two,
    rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
  norm_num

/-! ## The two-dimensional integral -/

lemma gauss_density_polar (r θ : ℝ) :
    (gaussianPDF 0 1 (r * cos θ) * gaussianPDF 0 1 (r * sin θ)).toReal =
      (2 * π)⁻¹ * exp (-r ^ 2 / 2) := by
  rw [ENNReal.toReal_mul, gaussianPDF, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hs : (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have he : exp (-(r * cos θ) ^ 2 / 2) * exp (-(r * sin θ) ^ 2 / 2) = exp (-r ^ 2 / 2) := by
    rw [← exp_add]
    congr 1
    have := sin_sq_add_cos_sq θ
    have h2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      calc (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 * (sin θ ^ 2 + cos θ ^ 2) := by ring
        _ = r ^ 2 := by rw [this, mul_one]
    linarith
  calc (Real.sqrt (2 * π))⁻¹ * exp (-(r * cos θ) ^ 2 / 2) *
        ((Real.sqrt (2 * π))⁻¹ * exp (-(r * sin θ) ^ 2 / 2))
      = ((Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹) *
        (exp (-(r * cos θ) ^ 2 / 2) * exp (-(r * sin θ) ^ 2 / 2)) := by ring
    _ = _ := by rw [hs, he]

/-- **The two-dimensional row formula**: for a standard Gaussian `ξ` in `ℝ²` and `0 ≤ ψ ≤ π`,
`E[ξ₀⁺ (cos ψ·ξ₀ + sin ψ·ξ₁)⁺] = κ(cos ψ)/2`. -/
theorem core2D {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) :
    ∫ ξ, relu (ξ 0) * relu (cos ψ * ξ 0 + sin ψ * ξ 1) ∂stdGauss (Fin 2) =
      kappa (cos ψ) / 2 := by
  let G : ℝ × ℝ → ℝ := fun p => relu p.1 * relu (cos ψ * p.1 + sin ψ * p.2)
  have s1 : ∫ ξ, relu (ξ 0) * relu (cos ψ * ξ 0 + sin ψ * ξ 1) ∂stdGauss (Fin 2) =
      ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have := (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' G
    rw [← this]
    rfl
  have hγ : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  have s2 : ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ p : ℝ × ℝ, (gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2).toReal • G p := by
    rw [hγ, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
    rw [← Measure.volume_eq_prod]
    refine integral_withDensity_eq_integral_toReal_smul ?_ ?_ G
    · exact ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
        ((measurable_gaussianPDF 0 1).comp measurable_snd)
    · refine Filter.Eventually.of_forall fun p => ?_
      exact ENNReal.mul_lt_top (by simp [gaussianPDF]) (by simp [gaussianPDF])
  rw [s1, s2, ← integral_comp_polarCoord_symm]
  have s3 : ∫ p in polarCoord.target, p.1 • ((gaussianPDF 0 1 (polarCoord.symm p).1 *
        gaussianPDF 0 1 (polarCoord.symm p).2).toReal • G (polarCoord.symm p)) =
      ∫ p in polarCoord.target, ((2 * π)⁻¹ * (p.1 ^ 3 * exp (-p.1 ^ 2 / 2))) *
        (relu (cos p.2) * relu (cos (p.2 - ψ))) := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    rw [polarCoord_target] at hp
    have hr : 0 ≤ p.1 := le_of_lt hp.1
    simp only [polarCoord_symm_apply, G, smul_eq_mul]
    rw [gauss_density_polar, relu_mul_of_nonneg hr,
      show cos ψ * (p.1 * cos p.2) + sin ψ * (p.1 * sin p.2) = p.1 * cos (p.2 - ψ) by
        rw [cos_sub]; ring,
      relu_mul_of_nonneg hr]
    ring
  rw [s3, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioo (-π) π))
    (fun r : ℝ => (2 * π)⁻¹ * (r ^ 3 * exp (-r ^ 2 / 2)))
    (fun θ : ℝ => relu (cos θ) * relu (cos (θ - ψ)))]
  rw [integral_const_mul, radial, angular h0 h1, kappa_cos h0 h1]
  field_simp

/-! ## The row formula for vectors -/

lemma abs_dot_le (h h' : Fin k → ℝ) :
    |∑ j, h j * h' j| ≤ Real.sqrt (normSq h) * Real.sqrt (normSq h') := by
  rw [← Real.sqrt_mul (normSq_nonneg h), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

lemma normSq_eq_zero {h : Fin k → ℝ} (hz : normSq h = 0) : h = 0 := by
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (h i))).mp hz j (Finset.mem_univ j)
  simpa using this

/-- **The row formula** for a standard Gaussian vector `w` in `ℝ^k` and fixed vectors `h, h′`:
`2·E[(w·h)⁺ (w·h′)⁺] = |h||h′|·κ(⟨h, h′⟩/(|h||h′|))`. (For `h = 0` or `h′ = 0` both sides
are `0`.) -/
theorem row_formula_std (h h' : Fin k → ℝ) :
    2 * ∫ w, relu (∑ j, w j * h j) * relu (∑ j, w j * h' j) ∂stdGauss (Fin k) =
      Real.sqrt (normSq h) * Real.sqrt (normSq h') *
        kappa ((∑ j, h j * h' j) / (Real.sqrt (normSq h) * Real.sqrt (normSq h'))) := by
  classical
  set a := Real.sqrt (normSq h) with ha
  set b := Real.sqrt (normSq h') with hb
  set d := ∑ j, h j * h' j with hd
  set c := d / (a * b) with hc
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have habs : |d| ≤ a * b := abs_dot_le h h'
  have hc1 : -1 ≤ c ∧ c ≤ 1 := by
    rcases eq_or_lt_of_le (mul_nonneg ha0 hb0) with h0 | hpos
    · rw [hc, ← h0]; simp
    · rw [hc, le_div_iff₀ hpos, div_le_iff₀ hpos]
      constructor <;> linarith [abs_le.mp habs]
  have habc : a * b * c = d := by
    rcases eq_or_lt_of_le (mul_nonneg ha0 hb0) with h0 | hpos
    · rw [← h0] at habs
      have : d = 0 := abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
      rw [this, ← h0, zero_mul]
    · rw [hc, mul_comm, div_mul_cancel₀ _ hpos.ne']
  set ψ := Real.arccos c with hψ
  have hψ0 : 0 ≤ ψ := Real.arccos_nonneg c
  have hψ1 : ψ ≤ π := Real.arccos_le_pi c
  have hcos : cos ψ = c := Real.cos_arccos hc1.1 hc1.2
  let A : Matrix (Fin 2) (Fin k) ℝ := Matrix.of ![h, h']
  let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![a, 0], ![b * cos ψ, b * sin ψ]]
  have hAB : A * A.transpose = B * B.transpose := by
    have haa : ∑ j, h j * h j = a * a := by
      rw [ha, Real.mul_self_sqrt (normSq_nonneg h)]
      exact Finset.sum_congr rfl fun j _ => (sq _).symm
    have hbb : ∑ j, h' j * h' j = b * b := by
      rw [hb, Real.mul_self_sqrt (normSq_nonneg h')]
      exact Finset.sum_congr rfl fun j _ => (sq _).symm
    have hd' : ∑ j, h' j * h j = d := Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsc := sin_sq_add_cos_sq ψ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, haa, hbb, hd', ← hd]
    · rw [hcos]; linarith
    · rw [hcos]; linarith
    · nlinarith
  have hmap := BstLean.Part105.gaussLin105 (Fin k) (Fin 2) (Fin 2) A B hAB
  let g : (Fin 2 → ℝ) → ℝ := fun y => relu (y 0) * relu (y 1)
  have hg : Measurable g :=
    (measurable_relu.comp (measurable_pi_apply 0)).mul (measurable_relu.comp (measurable_pi_apply 1))
  have e1 : ∫ w, relu (∑ j, w j * h j) * relu (∑ j, w j * h' j) ∂stdGauss (Fin k) =
      ∫ w, g (A.mulVec w) ∂stdGauss (Fin k) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [g, A, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    congr 2 <;> exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : ∫ w, g (A.mulVec w) ∂stdGauss (Fin k) = ∫ ξ, g (B.mulVec ξ) ∂stdGauss (Fin 2) := by
    rw [← integral_map (measurable_mulVec_left A).aemeasurable hg.aestronglyMeasurable, hmap,
      integral_map (measurable_mulVec_left B).aemeasurable hg.aestronglyMeasurable]
  have e3 : ∀ ξ : Fin 2 → ℝ, g (B.mulVec ξ) =
      (a * b) * (relu (ξ 0) * relu (cos ψ * ξ 0 + sin ψ * ξ 1)) := by
    intro ξ
    simp only [g, B, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero]
    rw [relu_mul_of_nonneg ha0,
      show b * cos ψ * ξ 0 + b * sin ψ * ξ 1 = b * (cos ψ * ξ 0 + sin ψ * ξ 1) by ring,
      relu_mul_of_nonneg hb0]
    ring
  rw [e1, e2]
  simp_rw [e3]
  rw [integral_const_mul, core2D hψ0 hψ1, hcos]
  ring

/-- Row `i` of a matrix, as a vector. -/
def rowOf (i : Fin m) (M : Matrix (Fin m) (Fin k) ℝ) : Fin k → ℝ := fun j => M i j

lemma measurable_rowOf (i : Fin m) : Measurable (rowOf (k := k) i) :=
  measurable_pi_iff.mpr fun j => (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- One row of a Gaussian matrix is `√v` times a standard Gaussian vector. -/
theorem gaussMat_row (v : ℝ) (i : Fin m) :
    (gaussMat m k v).map (rowOf i) = (stdGauss (Fin k)).map (fun ξ => Real.sqrt v • ξ) := by
  classical
  have hinj : Function.Injective (fun j : Fin k => ((i, j) : Fin m × Fin k)) :=
    fun a b hab => (Prod.mk.inj hab).2
  have h := BstLean.Part29.stdGauss_map_restrict (ι := Fin m × Fin k) (fun j : Fin k => (i, j)) hinj
  unfold gaussMat
  have hm : Measurable (fun z : Fin m × Fin k → ℝ => z ∘ fun j : Fin k => (i, j)) :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply _
  rw [Measure.map_map (measurable_rowOf i) (measurable_ofFlat _), ← h,
    Measure.map_map (measurable_const_smul _) hm]
  rfl

/-- **The row formula** for a row of a Gaussian matrix with variance `v ≥ 0`:
`2·E[(M h)_i⁺ (M h′)_i⁺] = v·|h||h′|·κ(⟨h, h′⟩/(|h||h′|))`; with `σ = √v·|h|`, `σ′ = √v·|h′|`
and `τ` the cosine this is `σσ′κ(τ)`. -/
theorem row_formula {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) (i : Fin m) :
    2 * ∫ M, relu ((M.mulVec h) i) * relu ((M.mulVec h') i) ∂gaussMat m k v =
      v * (Real.sqrt (normSq h) * Real.sqrt (normSq h') *
        kappa ((∑ j, h j * h' j) / (Real.sqrt (normSq h) * Real.sqrt (normSq h')))) := by
  let g : (Fin k → ℝ) → ℝ := fun w => relu (∑ j, w j * h j) * relu (∑ j, w j * h' j)
  have hg : Measurable g :=
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).mul_const _)).mul
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _))
  have e1 : ∫ M, relu ((M.mulVec h) i) * relu ((M.mulVec h') i) ∂gaussMat m k v =
      ∫ M, g (rowOf i M) ∂gaussMat m k v := rfl
  have e2 : ∫ M, g (rowOf i M) ∂gaussMat m k v = ∫ ξ, g (Real.sqrt v • ξ) ∂stdGauss (Fin k) := by
    rw [← integral_map (measurable_rowOf i).aemeasurable hg.aestronglyMeasurable, gaussMat_row,
      integral_map (measurable_const_smul _).aemeasurable hg.aestronglyMeasurable]
  have e3 : ∀ ξ : Fin k → ℝ, g (Real.sqrt v • ξ) =
      v * (relu (∑ j, ξ j * h j) * relu (∑ j, ξ j * h' j)) := by
    intro ξ
    simp only [g, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [relu_mul_of_nonneg (Real.sqrt_nonneg v), relu_mul_of_nonneg (Real.sqrt_nonneg v)]
    have := Real.mul_self_sqrt hv
    calc Real.sqrt v * relu (∑ j, ξ j * h j) * (Real.sqrt v * relu (∑ j, ξ j * h' j))
        = (Real.sqrt v * Real.sqrt v) * (relu (∑ j, ξ j * h j) * relu (∑ j, ξ j * h' j)) := by ring
      _ = _ := by rw [this]
  rw [e1, e2]
  simp_rw [e3]
  rw [integral_const_mul, ← row_formula_std h h']
  ring

end BstLean.Part130

open BstLean.Part130 in
#print axioms core2D
open BstLean.Part130 in
#print axioms row_formula_std
open BstLean.Part130 in
#print axioms row_formula
