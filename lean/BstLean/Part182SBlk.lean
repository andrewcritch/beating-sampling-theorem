import BstLean.Part182Kap
import BstLean.Part182Bern
import BstLean.Part112Chaos
import BstLean.Part182MS
import BstLean.Part151J
import BstLean.Part148Tools

/-!
# Part 182 (file `SBlk`): the scalar-block ingredients of Lemma TI

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, proof of Lemma `t7:p04:ti`, from
"For the scalar block, a row-sum inequality used three times" to "This proves the scalar bound".

* `sb_core2D_quad`, `sb_quad_q`: the two-dimensional cone moment of a quadratic,
  `E[1(η₀ > 0)1(qη₀ + ση₁ > 0)(Aη₀² + Bη₀η₁ + Cη₁²)] = (κ̇(q)/2)(A + C) + qσ/(2π)(A − C) +
  B(1 − q²)/(2π)`, `σ = √(1 − q²)`.
* **`sb_polar_quad`** (the polar matrix `H` as a quadratic form): for unit `v, v'`, `q = v·v'`,
  `q² < 1`, every `u`: `E[1(w·v > 0)1(w·v' > 0)(w·u)²] = (κ̇(q)/2)|u|² +
  (2αβ − q(α² + β²))/(2π√(1 − q²))`, `α = u·v`, `β = u·v'` (this equals the paper's
  `(κ̇(q)/2)|u|² + (√(1−q²)/(2π))((v₊·u)² − (v₋·u)²)`); `sb_three` is its reduction to `ℝ³`.
* **`sb_mean_pa`**, **`sb_mean_pp`** (the first-layer means): under `gaussMat m k v`, unit `x, x'`,
  `c = x·x'`, `c² < 1`, `e = eTan x x'`, `e' = eTan x' x`:
  `E Σᵢ mask((Ax)ᵢ)(Ae)ᵢ relu((Ax')ᵢ) = m v V(c)/2`, `V(c) = √(1−c²)κ̇(c)`;
  `E Σᵢ mask((Ax)ᵢ)(Ae)ᵢ · mask((Ax')ᵢ)(Ae')ᵢ = m v M(c)/2`, `M(c) = √(1−c²)/π − cκ̇(c)`.
  For `m = n²`, `v = γ_A = 2/n`: `nV(c)` and `nM(c)`.
* `sb_rows` (row reduction), `sb_dev`, `sb_dev_mean` (the row-sum inequality `bn_rowsum` for a
  first-layer sum with envelope `b(U² + V²)/2`).
* **`sb_tail_pa`**, **`sb_tail_pp`** (the deviation tails): envelopes `3v` and `2v`,
  `Pr(|⟨p, a'⟩ − m v V(c)/2| > 2·3v(√(2mτ) + τ)) ≤ 2e^{−τ}` and
  `Pr(|⟨p, p'⟩ − m v M(c)/2| > 2·2v(√(2mτ) + τ)) ≤ 2e^{−τ}` (the paper's `r₁`, `r_pp`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open Matrix (mulVec)
open scoped Matrix

/-- `∫₀^∞ r³ e^{−r²/2} dr = 2`. -/
lemma sb_radial3 : ∫ r in Ioi (0 : ℝ), r ^ 3 * exp (-r ^ 2 / 2) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∫ r in Ioi (0 : ℝ), r ^ 3 * exp (-r ^ 2 / 2) =
      ∫ r in Ioi (0 : ℝ), r ^ (3 : ℝ) * exp (-(1 / 2) * r ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
    congr 2
    ring
  rw [e, h]
  rw [show (3 + 1 : ℝ) / 2 = 2 by norm_num, Gamma_two]
  norm_num

/-- The antiderivative of the trigonometric quadratic. -/
noncomputable def sb_F (A B C θ : ℝ) : ℝ :=
  A * (θ / 2 + sin (2 * θ) / 4) - B * (cos (2 * θ) / 4) + C * (θ / 2 - sin (2 * θ) / 4)

lemma sb_F_deriv (A B C θ : ℝ) :
    HasDerivAt (sb_F A B C) (A * cos θ ^ 2 + B * (cos θ * sin θ) + C * sin θ ^ 2) θ := by
  have h1 : HasDerivAt (fun θ => sin (2 * θ)) (cos (2 * θ) * 2) θ := by
    have := ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
    simpa using this
  have h2 : HasDerivAt (fun θ => cos (2 * θ)) (-sin (2 * θ) * 2) θ := by
    have := ((hasDerivAt_id θ).const_mul (2 : ℝ)).cos
    simpa using this
  have hF : HasDerivAt (sb_F A B C)
      (A * (1 / 2 + cos (2 * θ) * 2 / 4) - B * (-sin (2 * θ) * 2 / 4) +
        C * (1 / 2 - cos (2 * θ) * 2 / 4)) θ := by
    unfold sb_F
    refine ((((hasDerivAt_id θ).div_const 2).add (h1.div_const 4)).const_mul A |>.sub
      ((h2.div_const 4).const_mul B)).add
      ((((hasDerivAt_id θ).div_const 2).sub (h1.div_const 4)).const_mul C) |>.congr_deriv ?_
    simp
  convert hF using 1
  rw [cos_two_mul, sin_two_mul]
  have := sin_sq_add_cos_sq θ
  linear_combination C * this

/-- The trigonometric quadratic. -/
noncomputable def sb_T (A B C θ : ℝ) : ℝ := A * cos θ ^ 2 + B * (cos θ * sin θ) + C * sin θ ^ 2

lemma sb_T_abs (A B C θ : ℝ) : |sb_T A B C θ| ≤ |A| + |B| + |C| := by
  unfold sb_T
  have hc := abs_cos_le_one θ
  have hs := abs_sin_le_one θ
  have h1 : |cos θ ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
  have h2 : |cos θ * sin θ| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (cos θ), abs_nonneg (sin θ)]
  have h3 : |sin θ ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs
  calc |A * cos θ ^ 2 + B * (cos θ * sin θ) + C * sin θ ^ 2|
      ≤ |A * cos θ ^ 2| + |B * (cos θ * sin θ)| + |C * sin θ ^ 2| := abs_add_three _ _ _
    _ ≤ |A| + |B| + |C| := by
        have g1 : |A * cos θ ^ 2| ≤ |A| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h1
        have g2 : |B * (cos θ * sin θ)| ≤ |B| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h2
        have g3 : |C * sin θ ^ 2| ≤ |C| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h3
        linarith

lemma sb_continuous_T (A B C : ℝ) : Continuous (sb_T A B C) := by
  unfold sb_T; fun_prop

/-- **The angular integral of the trigonometric quadratic over the cone**. -/
lemma sb_angular {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) (A B C : ℝ) :
    ∫ θ in Ioo (-π) π, posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ =
      sb_F A B C (π / 2) - sb_F A B C (ψ - π / 2) := by
  have hp := pi_pos
  have hmeas : Measurable (fun θ : ℝ => posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ) :=
    ((measurable_posI.comp continuous_cos.measurable).mul
      (measurable_posI.comp (continuous_cos.comp (continuous_id.sub continuous_const)).measurable)).mul
      (sb_continuous_T A B C).measurable
  have hbdd : ∀ θ : ℝ, ‖posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ‖ ≤ |A| + |B| + |C| := by
    intro θ
    rw [Real.norm_eq_abs, abs_mul]
    have hT := sb_T_abs A B C θ
    have hI : |posI (cos θ) * posI (cos (θ - ψ))| ≤ 1 := by
      unfold posI; split_ifs <;> simp
    calc |posI (cos θ) * posI (cos (θ - ψ))| * |sb_T A B C θ| ≤ 1 * (|A| + |B| + |C|) :=
          mul_le_mul hI hT (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun θ : ℝ => posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ) volume a b := fun a b =>
    (intervalIntegrable_const (c := |A| + |B| + |C|)).mono_fun hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => by
        have := hbdd θ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |A| + |B| + |C|)]
        exact this)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-π) (ψ - π / 2)) (hint (ψ - π / 2) π),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (ψ - π / 2) (π / 2)) (hint (π / 2) π)]
  have z1 : ∫ θ in (-π)..(ψ - π / 2), posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      by_cases hc : θ ≤ -(π / 2)
      · have : cos θ ≤ 0 := by
          rw [← cos_neg]
          exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [posI_of_nonpos this]
      · have : cos (θ - ψ) ≤ 0 := by
          rw [← cos_neg]
          exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [posI_of_nonpos this]
  have z3 : ∫ θ in (π / 2)..π, posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      have : cos θ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le ha (by linarith)
      simp [posI_of_nonpos this]
  have z2 : ∫ θ in (ψ - π / 2)..(π / 2), posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ =
      sb_F A B C (π / 2) - sb_F A B C (ψ - π / 2) := by
    have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ π / 2 := by
      rw [ae_iff]
      have e : {a : ℝ | ¬ a ≠ π / 2} = {π / 2} := by ext a; simp
      rw [e]; exact measure_singleton _
    rw [intervalIntegral.integral_congr_ae (g := fun θ => sb_T A B C θ)]
    · exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => sb_F_deriv A B C θ)
        ((sb_continuous_T A B C).intervalIntegrable _ _)
    · filter_upwards [hne] with θ hθne hθ
      rw [uIoc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      have hb' : θ < π / 2 := lt_of_le_of_ne hb hθne
      have c1 : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, hb'⟩
      have c2 : 0 < cos (θ - ψ) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      simp [posI_of_pos c1, posI_of_pos c2]
  rw [z1, z2, z3]
  ring

/-- **The two-dimensional cone moment of a quadratic**: for `0 ≤ ψ ≤ π`,
`E[1(ξ₀ > 0)·1(cos ψ ξ₀ + sin ψ ξ₁ > 0)·(Aξ₀² + Bξ₀ξ₁ + Cξ₁²)] = (F(π/2) − F(ψ − π/2))/π`. -/
theorem sb_core2D_quad {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) (A B C : ℝ) :
    ∫ ξ, posI (ξ 0) * posI (cos ψ * ξ 0 + sin ψ * ξ 1) *
      (A * ξ 0 ^ 2 + B * (ξ 0 * ξ 1) + C * ξ 1 ^ 2) ∂stdGauss (Fin 2) =
      (sb_F A B C (π / 2) - sb_F A B C (ψ - π / 2)) / π := by
  let G : ℝ × ℝ → ℝ := fun p => posI p.1 * posI (cos ψ * p.1 + sin ψ * p.2) *
    (A * p.1 ^ 2 + B * (p.1 * p.2) + C * p.2 ^ 2)
  have s1 : ∫ ξ, posI (ξ 0) * posI (cos ψ * ξ 0 + sin ψ * ξ 1) *
      (A * ξ 0 ^ 2 + B * (ξ 0 * ξ 1) + C * ξ 1 ^ 2) ∂stdGauss (Fin 2) =
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
        (posI (cos p.2) * posI (cos (p.2 - ψ)) * sb_T A B C p.2) := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    rw [polarCoord_target] at hp
    have hr : 0 < p.1 := hp.1
    simp only [polarCoord_symm_apply, G, smul_eq_mul]
    rw [gauss_density_polar, posI_mul_of_pos hr,
      show cos ψ * (p.1 * cos p.2) + sin ψ * (p.1 * sin p.2) = p.1 * cos (p.2 - ψ) by
        rw [cos_sub]; ring,
      posI_mul_of_pos hr]
    unfold sb_T
    ring
  rw [s3, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioo (-π) π))
    (fun r : ℝ => (2 * π)⁻¹ * (r ^ 3 * exp (-r ^ 2 / 2)))
    (fun θ : ℝ => posI (cos θ) * posI (cos (θ - ψ)) * sb_T A B C θ)]
  rw [integral_const_mul, sb_radial3, sb_angular h0 h1]
  have hp := pi_pos
  field_simp

/-- The closed form of the angular difference, at `ψ = arccos q`. -/
lemma sb_F_diff {q : ℝ} (hq1 : -1 ≤ q) (hq2 : q ≤ 1) (A B C : ℝ) :
    (sb_F A B C (π / 2) - sb_F A B C (Real.arccos q - π / 2)) / π =
      kdot q / 2 * (A + C) + q * √(1 - q ^ 2) / (2 * π) * (A - C) +
        B * (1 - q ^ 2) / (2 * π) := by
  have hp := pi_pos
  set ψ := Real.arccos q with hψ
  have hc : cos ψ = q := Real.cos_arccos hq1 hq2
  have hs : sin ψ = √(1 - q ^ 2) := Real.sin_arccos q
  have hss : sin ψ ^ 2 = 1 - q ^ 2 := by rw [← hc]; have := sin_sq_add_cos_sq ψ; linarith
  have e1 : sin (2 * (π / 2)) = 0 := by rw [show 2 * (π / 2) = π by ring, sin_pi]
  have e2 : cos (2 * (π / 2)) = -1 := by rw [show 2 * (π / 2) = π by ring, cos_pi]
  have e3 : sin (2 * (ψ - π / 2)) = -(2 * sin ψ * cos ψ) := by
    rw [show 2 * (ψ - π / 2) = 2 * ψ - π by ring, sin_sub_pi, sin_two_mul]
  have e4 : cos (2 * (ψ - π / 2)) = -(1 - 2 * sin ψ ^ 2) := by
    rw [show 2 * (ψ - π / 2) = 2 * ψ - π by ring, cos_sub_pi, cos_two_mul]
    have := sin_sq_add_cos_sq ψ; linarith
  unfold sb_F kdot
  rw [e1, e2, e3, e4, ← hs, hc]
  field_simp
  rw [hss]
  ring

/-- Splitting `ℝ³` as `ℝ² × ℝ` under the standard Gaussian. -/
lemma sb_split3 (h : ℝ → ℝ) (g : (Fin 2 → ℝ) → ℝ) :
    ∫ ξ, h (ξ 2) * g (fun j => ξ ((2 : Fin 3).succAbove j)) ∂stdGauss (Fin 3) =
      (∫ x, h x ∂gaussianReal 0 1) * ∫ η, g η ∂stdGauss (Fin 2) := by
  have hm := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianReal 0 1) 2
  have := hm.integral_comp' (fun p : ℝ × (Fin 2 → ℝ) => h p.1 * g p.2)
  unfold stdGauss
  rw [← integral_prod_mul]
  rw [← this]
  rfl

lemma sb_succAbove (ξ : Fin 3 → ℝ) :
    (fun j : Fin 2 => ξ ((2 : Fin 3).succAbove j)) = ![ξ 0, ξ 1] := by
  funext j
  fin_cases j <;> rfl

lemma sb_int_sq (i : Fin 3) : Integrable (fun ξ : Fin 3 → ℝ => ξ i ^ 2) (stdGauss (Fin 3)) :=
  (BstLean.Part112.memLp_coord i).integrable_sq

lemma sb_posI_le (t : ℝ) : 0 ≤ posI t ∧ posI t ≤ 1 := by
  unfold posI; split_ifs <;> norm_num

/-- The integrand pieces on `ℝ³` are dominated by `ξ₀² + ξ₁² + ξ₂²` (times a constant). -/
lemma sb_int3 {f : (Fin 3 → ℝ) → ℝ} (hf : Measurable f) (K : ℝ)
    (hb : ∀ ξ, |f ξ| ≤ K * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)) : Integrable f (stdGauss (Fin 3)) := by
  refine Integrable.mono' (((sb_int_sq 0).add (sb_int_sq 1)).add (sb_int_sq 2) |>.const_mul K)
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  simpa using hb ξ

/-- **The three-dimensional reduction of the polar second moment**, with free real parameters:
for `q² < 1`, `σ = √(1 − q²)`, and any `α, b, ρ`,
`E[1(ξ₀ > 0)·1(qξ₀ + σξ₁ > 0)·(αξ₀ + bξ₁ + ρξ₂)²] = (κ̇(q)/2)(α² + b² + ρ²) +
qσ/(2π)·(α² − b²) + 2αb(1 − q²)/(2π)`. -/
theorem sb_three {q α b ρ : ℝ} (hq : q ^ 2 < 1) :
    ∫ ξ, posI (ξ 0) * posI (q * ξ 0 + √(1 - q ^ 2) * ξ 1) *
      (α * ξ 0 + b * ξ 1 + ρ * ξ 2) ^ 2 ∂stdGauss (Fin 3) =
      kdot q / 2 * (α ^ 2 + b ^ 2 + ρ ^ 2) + q * √(1 - q ^ 2) / (2 * π) * (α ^ 2 - b ^ 2) +
        (2 * α * b) * (1 - q ^ 2) / (2 * π) := by
  have hp := pi_pos
  have hq1 : -1 ≤ q ∧ q ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (q + 1), sq_nonneg (q - 1)]
  set σ := √(1 - q ^ 2) with hσd
  clear_value σ
  let g : (Fin 3 → ℝ) → ℝ := fun ξ => posI (ξ 0) * posI (q * ξ 0 + σ * ξ 1) *
      (α * ξ 0 + b * ξ 1 + ρ * ξ 2) ^ 2
  let I2 : (Fin 2 → ℝ) → ℝ := fun η => posI (η 0) * posI (q * η 0 + σ * η 1)
  let L2 : (Fin 2 → ℝ) → ℝ := fun η => α * η 0 + b * η 1
  have hI2 : Measurable I2 := (measurable_posI.comp (measurable_pi_apply 0)).mul
    (measurable_posI.comp (by fun_prop : Measurable fun η : Fin 2 → ℝ => q * η 0 + σ * η 1))
  have hL2 : Measurable L2 := by
    show Measurable fun η : Fin 2 → ℝ => α * η 0 + b * η 1
    fun_prop
  have e3 : ∀ ξ : Fin 3 → ℝ, g ξ =
      (fun _ : ℝ => (1 : ℝ)) (ξ 2) * (fun η => I2 η * L2 η ^ 2) ![ξ 0, ξ 1] +
      (fun x : ℝ => 2 * ρ * x) (ξ 2) * (fun η => I2 η * L2 η) ![ξ 0, ξ 1] +
      (fun x : ℝ => ρ ^ 2 * x ^ 2) (ξ 2) * I2 ![ξ 0, ξ 1] := by
    intro ξ
    simp only [g, I2, L2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hb1 : ∀ ξ : Fin 3 → ℝ, |I2 ![ξ 0, ξ 1]| ≤ 1 := by
    intro ξ
    have h1 := sb_posI_le (ξ 0)
    have h2 := sb_posI_le (q * ξ 0 + σ * ξ 1)
    simp only [I2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]
    nlinarith
  have hmeas2 : Measurable (fun ξ : Fin 3 → ℝ => (![ξ 0, ξ 1] : Fin 2 → ℝ)) := by
    refine measurable_pi_iff.mpr fun j => ?_
    fin_cases j
    · exact measurable_pi_apply 0
    · exact measurable_pi_apply 1
  have hxy : ∀ x y : ℝ, |x * y| ≤ x ^ 2 + y ^ 2 := by
    intro x y
    rw [abs_mul]
    nlinarith [sq_abs x, sq_abs y, sq_nonneg (|x| - |y|), abs_nonneg x, abs_nonneg y]
  have i1 : Integrable (fun ξ : Fin 3 → ℝ => (fun _ : ℝ => (1 : ℝ)) (ξ 2) *
      (fun η => I2 η * L2 η ^ 2) ![ξ 0, ξ 1]) (stdGauss (Fin 3)) := by
    refine sb_int3 (measurable_const.mul ((hI2.mul (hL2.pow_const 2)).comp hmeas2))
      (4 * (α ^ 2 + b ^ 2)) fun ξ => ?_
    have h := hb1 ξ
    have hL : L2 ![ξ 0, ξ 1] = α * ξ 0 + b * ξ 1 := by simp [L2]
    show |1 * (I2 ![ξ 0, ξ 1] * L2 ![ξ 0, ξ 1] ^ 2)| ≤ _
    rw [hL, one_mul, abs_mul, abs_of_nonneg (sq_nonneg (α * ξ 0 + b * ξ 1))]
    have hsq : (α * ξ 0 + b * ξ 1) ^ 2 ≤ 4 * (α ^ 2 + b ^ 2) * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) := by
      have t : (α * ξ 0 + b * ξ 1) ^ 2 ≤ 2 * (α ^ 2 * ξ 0 ^ 2) + 2 * (b ^ 2 * ξ 1 ^ 2) := by
        nlinarith [sq_nonneg (α * ξ 0 - b * ξ 1)]
      have t1 : α ^ 2 * ξ 0 ^ 2 ≤ (α ^ 2 + b ^ 2) * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) :=
        mul_le_mul (by nlinarith [sq_nonneg b]) (by nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2)])
          (sq_nonneg _) (by positivity)
      have t2 : b ^ 2 * ξ 1 ^ 2 ≤ (α ^ 2 + b ^ 2) * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) :=
        mul_le_mul (by nlinarith [sq_nonneg α]) (by nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 2)])
          (sq_nonneg _) (by positivity)
      linarith
    calc |I2 ![ξ 0, ξ 1]| * (α * ξ 0 + b * ξ 1) ^ 2 ≤ 1 * (4 * (α ^ 2 + b ^ 2) *
          (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)) := mul_le_mul h hsq (sq_nonneg _) zero_le_one
      _ = _ := one_mul _
  have i2 : Integrable (fun ξ : Fin 3 → ℝ => (fun x : ℝ => 2 * ρ * x) (ξ 2) *
      (fun η => I2 η * L2 η) ![ξ 0, ξ 1]) (stdGauss (Fin 3)) := by
    refine sb_int3 (((measurable_pi_apply 2).const_mul (2 * ρ)).mul ((hI2.mul hL2).comp hmeas2))
      (2 * |ρ| * (|α| + |b|)) fun ξ => ?_
    have h := hb1 ξ
    have hρ0 : 0 ≤ |ρ| := abs_nonneg ρ
    have hL : L2 ![ξ 0, ξ 1] = α * ξ 0 + b * ξ 1 := by simp [L2]
    show |2 * ρ * ξ 2 * (I2 ![ξ 0, ξ 1] * L2 ![ξ 0, ξ 1])| ≤ _
    rw [hL]
    have e : 2 * ρ * ξ 2 * (I2 ![ξ 0, ξ 1] * (α * ξ 0 + b * ξ 1)) =
        (2 * ρ) * I2 ![ξ 0, ξ 1] * (α * (ξ 0 * ξ 2) + b * (ξ 1 * ξ 2)) := by ring
    rw [e, abs_mul, abs_mul, abs_mul, abs_two]
    have hx : |α * (ξ 0 * ξ 2) + b * (ξ 1 * ξ 2)| ≤ (|α| + |b|) * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) := by
      have t := abs_add_le (α * (ξ 0 * ξ 2)) (b * (ξ 1 * ξ 2))
      rw [abs_mul α, abs_mul b] at t
      have u1 := hxy (ξ 0) (ξ 2)
      have u2 := hxy (ξ 1) (ξ 2)
      have hA := abs_nonneg α
      have hB := abs_nonneg b
      have v1 : |α| * |ξ 0 * ξ 2| ≤ |α| * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (ξ 1)]) hA
      have v2 : |b| * |ξ 1 * ξ 2| ≤ |b| * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (ξ 0)]) hB
      linarith
    calc 2 * |ρ| * |I2 ![ξ 0, ξ 1]| * |α * (ξ 0 * ξ 2) + b * (ξ 1 * ξ 2)|
        ≤ 2 * |ρ| * 1 * ((|α| + |b|) * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h (by positivity)) hx (abs_nonneg _)
            (by positivity)
      _ = _ := by ring
  have i3 : Integrable (fun ξ : Fin 3 → ℝ => (fun x : ℝ => ρ ^ 2 * x ^ 2) (ξ 2) *
      I2 ![ξ 0, ξ 1]) (stdGauss (Fin 3)) := by
    refine sb_int3 ((((measurable_pi_apply 2).pow_const 2).const_mul (ρ ^ 2)).mul
      (hI2.comp hmeas2)) (ρ ^ 2) fun ξ => ?_
    have h := hb1 ξ
    show |ρ ^ 2 * ξ 2 ^ 2 * I2 ![ξ 0, ξ 1]| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ ^ 2 * ξ 2 ^ 2)]
    have hS : ρ ^ 2 * ξ 2 ^ 2 ≤ ρ ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1)]) (sq_nonneg _)
    calc ρ ^ 2 * ξ 2 ^ 2 * |I2 ![ξ 0, ξ 1]| ≤ ρ ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) * 1 :=
          mul_le_mul hS h (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  -- the three integrals
  show ∫ ξ, g ξ ∂stdGauss (Fin 3) = _
  have hsplit : ∫ ξ, g ξ ∂stdGauss (Fin 3) =
      (∫ ξ, (fun _ : ℝ => (1 : ℝ)) (ξ 2) * (fun η => I2 η * L2 η ^ 2) ![ξ 0, ξ 1] ∂stdGauss (Fin 3)) +
      (∫ ξ, (fun x : ℝ => 2 * ρ * x) (ξ 2) * (fun η => I2 η * L2 η) ![ξ 0, ξ 1] ∂stdGauss (Fin 3)) +
      (∫ ξ, (fun x : ℝ => ρ ^ 2 * x ^ 2) (ξ 2) * I2 ![ξ 0, ξ 1] ∂stdGauss (Fin 3)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall e3)]
    have A1 := integral_add (i1.add i2) i3
    have A2 := integral_add i1 i2
    simp only [Pi.add_apply] at A1 A2
    rw [A1, A2]
  have s1 := sb_split3 (fun _ : ℝ => (1 : ℝ)) (fun η => I2 η * L2 η ^ 2)
  have s2 := sb_split3 (fun x : ℝ => 2 * ρ * x) (fun η => I2 η * L2 η)
  have s3 := sb_split3 (fun x : ℝ => ρ ^ 2 * x ^ 2) I2
  rw [hsplit]
  simp only [sb_succAbove] at s1 s2 s3
  rw [s1, s2, s3]
  have g1 : ∫ x, (1 : ℝ) ∂gaussianReal 0 1 = 1 := by simp
  have g2 : ∫ x, 2 * ρ * x ∂gaussianReal 0 1 = 0 := by
    rw [integral_const_mul, integral_id_gaussianReal]; ring
  have g3 : ∫ x, ρ ^ 2 * x ^ 2 ∂gaussianReal 0 1 = ρ ^ 2 := by
    rw [integral_const_mul, bn_gauss_sq, mul_one]
  rw [g1, g2, g3]
  -- the two-dimensional integrals
  have hψ0 := Real.arccos_nonneg q
  have hψ1 := Real.arccos_le_pi q
  have hcos : cos (Real.arccos q) = q := Real.cos_arccos hq1.1 hq1.2
  have hsin : sin (Real.arccos q) = σ := by rw [hσd]; exact Real.sin_arccos q
  have q1 : ∫ η, I2 η * L2 η ^ 2 ∂stdGauss (Fin 2) =
      kdot q / 2 * (α ^ 2 + b ^ 2) + q * σ / (2 * π) * (α ^ 2 - b ^ 2) +
        (2 * α * b) * (1 - q ^ 2) / (2 * π) := by
    have h := sb_core2D_quad hψ0 hψ1 (α ^ 2) (2 * α * b) (b ^ 2)
    rw [hcos, hsin, sb_F_diff hq1.1 hq1.2, ← hσd] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [I2, L2]
    ring
  have q2 : ∫ η, I2 η ∂stdGauss (Fin 2) = kdot q / 2 := by
    have h := core2D_pos hψ0 hψ1
    rw [hcos, hsin] at h
    simp only [I2]
    rw [h, kdot]
    field_simp
  rw [q1, q2]
  ring

/-- **The polar second moment (paper: the matrix `H` of Lemma TI), quadratic form.** For unit
`v, v' ∈ ℝ^k` with `q = v·v'`, `q² < 1`, and every `u`:
`E[1(w·v > 0)·1(w·v' > 0)·(w·u)²] = (κ̇(q)/2)|u|² + (2αβ − q(α² + β²))/(2π√(1 − q²))`,
`α = u·v`, `β = u·v'`. (Equivalently `(κ̇(q)/2)|u|² + (√(1−q²)/(2π))((v₊·u)² − (v₋·u)²)`.) -/
theorem sb_polar_quad {k : ℕ} {v v' u : Fin k → ℝ} (hv : normSq v = 1) (hv' : normSq v' = 1)
    (hq : (v ⬝ᵥ v') ^ 2 < 1) :
    ∫ w, posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * (w ⬝ᵥ u) ^ 2 ∂stdGauss (Fin k) =
      kdot (v ⬝ᵥ v') / 2 * normSq u +
        (2 * (u ⬝ᵥ v) * (u ⬝ᵥ v') - (v ⬝ᵥ v') * ((u ⬝ᵥ v) ^ 2 + (u ⬝ᵥ v') ^ 2)) /
          (2 * π * √(1 - (v ⬝ᵥ v') ^ 2)) := by
  classical
  have hp := pi_pos
  set q := v ⬝ᵥ v' with hqd
  set α := u ⬝ᵥ v with hα
  set β := u ⬝ᵥ v' with hβ
  have hσ2 : 0 < 1 - q ^ 2 := by linarith
  set σ := √(1 - q ^ 2) with hσd
  have hσ : 0 < σ := Real.sqrt_pos.2 hσ2
  have hσsq : σ ^ 2 = 1 - q ^ 2 := Real.sq_sqrt hσ2.le
  have hq1 : -1 ≤ q ∧ q ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (q + 1), sq_nonneg (q - 1)]
  set b := (β - q * α) / σ with hb
  -- Bessel: `α² + b² ≤ |u|²`
  have hvv : v ⬝ᵥ v = 1 := by rw [← hv]; simp [normSq, dotProduct, sq]
  have hv'v' : v' ⬝ᵥ v' = 1 := by rw [← hv']; simp [normSq, dotProduct, sq]
  have huu : u ⬝ᵥ u = normSq u := by simp [normSq, dotProduct, sq]
  set f := σ⁻¹ • (v' - q • v) with hf
  have hfv : f ⬝ᵥ v = 0 := by
    rw [hf, smul_dotProduct, sub_dotProduct, smul_dotProduct, hvv, dotProduct_comm v' v, ← hqd]
    simp
  have hff : f ⬝ᵥ f = 1 := by
    rw [hf, smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hvv, hv'v',
      dotProduct_comm v' v, ← hqd]
    simp only [smul_eq_mul]
    field_simp
    rw [hσsq]; ring
  have huf : u ⬝ᵥ f = b := by
    rw [hf, dotProduct_smul, dotProduct_sub, dotProduct_smul, ← hα, ← hβ, hb]
    simp only [smul_eq_mul]
    field_simp
  have hbes : 0 ≤ normSq u - α ^ 2 - b ^ 2 := by
    have h0 : 0 ≤ (u - α • v - b • f) ⬝ᵥ (u - α • v - b • f) := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have e : (u - α • v - b • f) ⬝ᵥ (u - α • v - b • f) = normSq u - α ^ 2 - b ^ 2 := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [huu, hvv, hff, ← hα, huf, dotProduct_comm v u, ← hα, dotProduct_comm f u, huf,
        dotProduct_comm v f, hfv]
      ring
    linarith
  set ρ := √(normSq u - α ^ 2 - b ^ 2) with hρd
  have hρsq : ρ ^ 2 = normSq u - α ^ 2 - b ^ 2 := Real.sq_sqrt hbes
  -- the Gaussian linear map
  let A : Matrix (Fin 3) (Fin k) ℝ := Matrix.of ![v, v', u]
  let B : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![![1, 0, 0], ![q, σ, 0], ![α, b, ρ]]
  have hAB : A * A.transpose = B * B.transpose := by
    have h1 : ∑ j, v j * v j = 1 := by simpa [dotProduct] using hvv
    have h2 : ∑ j, v' j * v' j = 1 := by simpa [dotProduct] using hv'v'
    have h3 : ∑ j, u j * u j = normSq u := by simpa [dotProduct] using huu
    have h12 : ∑ j, v j * v' j = q := by simp [hqd, dotProduct]
    have h21 : ∑ j, v' j * v j = q := by rw [← h12]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h31 : ∑ j, u j * v j = α := by simp [hα, dotProduct]
    have h13 : ∑ j, v j * u j = α := by rw [← h31]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h32 : ∑ j, u j * v' j = β := by simp [hβ, dotProduct]
    have h23 : ∑ j, v' j * u j = β := by rw [← h32]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hbσ : q * α + σ * b = β := by rw [hb]; field_simp; ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, Matrix.mul_apply, Fin.sum_univ_three, h1, h2, h3, h12, h21, h31, h13, h32, h23]
    · linear_combination (-1 : ℝ) * hσsq
    · linear_combination (-1 : ℝ) * hbσ
    · linear_combination (-1 : ℝ) * hbσ
    · linear_combination (-1 : ℝ) * hρsq
  have hmap := BstLean.Part105.gaussLin105 (Fin k) (Fin 3) (Fin 3) A B hAB
  let g : (Fin 3 → ℝ) → ℝ := fun y => posI (y 0) * posI (y 1) * y 2 ^ 2
  have hg : Measurable g :=
    ((measurable_posI.comp (measurable_pi_apply 0)).mul
      (measurable_posI.comp (measurable_pi_apply 1))).mul ((measurable_pi_apply 2).pow_const 2)
  have e1 : ∫ w, posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * (w ⬝ᵥ u) ^ 2 ∂stdGauss (Fin k) =
      ∫ w, g (A.mulVec w) ∂stdGauss (Fin k) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [g, A, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [dotProduct_comm v w, dotProduct_comm v' w, dotProduct_comm u w]
  have e2 : ∫ w, g (A.mulVec w) ∂stdGauss (Fin k) = ∫ ξ, g (B.mulVec ξ) ∂stdGauss (Fin 3) := by
    rw [← integral_map (measurable_mulVec_left A).aemeasurable hg.aestronglyMeasurable, hmap,
      integral_map (measurable_mulVec_left B).aemeasurable hg.aestronglyMeasurable]
  rw [e1, e2]
  have e3 : ∀ ξ : Fin 3 → ℝ, g (B.mulVec ξ) = posI (ξ 0) * posI (q * ξ 0 + σ * ξ 1) *
      (α * ξ 0 + b * ξ 1 + ρ * ξ 2) ^ 2 := by
    intro ξ
    simp [g, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp_rw [e3]
  rw [hσd, sb_three (by linarith : q ^ 2 < 1), ← hσd]
  -- algebra
  have hbσ : σ * b = β - q * α := by rw [hb]; field_simp
  rw [show normSq u = α ^ 2 + b ^ 2 + ρ ^ 2 by linarith [hρsq]]
  field_simp
  linear_combination (q * α ^ 2) * hσsq + (-q * (σ * b + β - q * α) + 2 * α * (1 - q ^ 2)) * hbσ

/-! ## The first-layer means -/

lemma sb_mask_eq (t : ℝ) : BstLean.Part151.mask t = posI t := rfl

lemma sb_relu_eq (t : ℝ) : relu t = posI t * t := by
  unfold relu posI
  split_ifs with h
  · rw [max_eq_right h.le, one_mul]
  · rw [max_eq_left (not_lt.mp h), zero_mul]

lemma sb_int2_sq (i : Fin 2) : Integrable (fun η : Fin 2 → ℝ => η i ^ 2) (stdGauss (Fin 2)) :=
  (BstLean.Part112.memLp_coord i).integrable_sq

lemma sb_int2 {f : (Fin 2 → ℝ) → ℝ} (hf : Measurable f) (K : ℝ)
    (hb : ∀ η, |f η| ≤ K * (η 0 ^ 2 + η 1 ^ 2)) : Integrable f (stdGauss (Fin 2)) := by
  refine Integrable.mono' (((sb_int2_sq 0).add (sb_int2_sq 1)).const_mul K)
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs]
  simpa using hb η

/-- The push-forward of `stdGauss (Fin k)` by `ξ ↦ (ξ·x, ξ·e)` for orthonormal `x, e` is
`stdGauss (Fin 2)`. -/
lemma sb_map_two {k : ℕ} {x e : Fin k → ℝ} (hxx : x ⬝ᵥ x = 1) (hee : e ⬝ᵥ e = 1)
    (hxe : x ⬝ᵥ e = 0) :
    (stdGauss (Fin k)).map (fun ξ => (Matrix.of ![x, e]).mulVec ξ) = stdGauss (Fin 2) := by
  have hAB : Matrix.of ![x, e] * (Matrix.of ![x, e]).transpose =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ).transpose := by
    have h1 : ∑ j, x j * x j = 1 := by simpa [dotProduct] using hxx
    have h2 : ∑ j, e j * e j = 1 := by simpa [dotProduct] using hee
    have h3 : ∑ j, x j * e j = 0 := by simpa [dotProduct] using hxe
    have h4 : ∑ j, e j * x j = 0 := by rw [← h3]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, h1, h2, h3, h4]
  have h := BstLean.Part105.gaussLin105 (Fin k) (Fin 2) (Fin 2) _ _ hAB
  rw [h]
  simp only [Matrix.one_mulVec]
  exact Measure.map_id' 

/-- **Row reduction**: for orthonormal `x, e`, a measurable `H` with `η ↦ H(√v η₀, √v η₁)`
integrable, `E Σᵢ H((A x)ᵢ, (A e)ᵢ) = m·E H(√v η₀, √v η₁)` under `gaussMat m k v`. -/
lemma sb_rows {m k : ℕ} {v : ℝ} (hv : 0 ≤ v) {x e : Fin k → ℝ} (hxx : x ⬝ᵥ x = 1)
    (hee : e ⬝ᵥ e = 1) (hxe : x ⬝ᵥ e = 0) {H : ℝ → ℝ → ℝ} (hH : Measurable (Function.uncurry H))
    (hint : Integrable (fun η : Fin 2 → ℝ => H (√v * η 0) (√v * η 1)) (stdGauss (Fin 2))) :
    ∫ A, ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) ∂gaussMat m k v =
      m * ∫ η, H (√v * η 0) (√v * η 1) ∂stdGauss (Fin 2) := by
  set K : (Fin 2 → ℝ) → ℝ := fun η => H (√v * η 0) (√v * η 1) with hK
  have hKm : Measurable K := by
    have e : K = Function.uncurry H ∘ (fun η : Fin 2 → ℝ => (√v * η 0, √v * η 1)) := rfl
    rw [e]; exact hH.comp (by fun_prop)
  set Φ : (Fin k → ℝ) → ℝ := fun r => H (r ⬝ᵥ x) (r ⬝ᵥ e) with hΦ
  have hΦm : Measurable Φ := by
    have e : Φ = Function.uncurry H ∘ (fun r : Fin k → ℝ => (r ⬝ᵥ x, r ⬝ᵥ e)) := rfl
    rw [e]
    refine hH.comp (Measurable.prodMk ?_ ?_)
    · simp only [dotProduct]; fun_prop
    · simp only [dotProduct]; fun_prop
  have hAm : Measurable (fun ξ : Fin k → ℝ => (Matrix.of ![x, e]).mulVec ξ) :=
    measurable_mulVec_left _
  have hmap := sb_map_two hxx hee hxe
  have hKA : ∀ ξ : Fin k → ℝ, Φ (√v • ξ) = K ((Matrix.of ![x, e]).mulVec ξ) := by
    intro ξ
    simp only [hΦ, hK, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [smul_dotProduct, smul_dotProduct, dotProduct_comm x ξ, dotProduct_comm e ξ]
    rfl
  have hint_k : Integrable (fun ξ => Φ (√v • ξ)) (stdGauss (Fin k)) := by
    simp_rw [hKA]
    have := (integrable_map_measure hKm.aestronglyMeasurable hAm.aemeasurable).1
      (by rw [hmap]; exact hint)
    exact this
  have hrow : ∀ i : Fin m, (fun A : Matrix (Fin m) (Fin k) ℝ => H ((A *ᵥ x) i) ((A *ᵥ e) i)) =
      fun A => Φ (rowOf i A) := by
    intro i; funext A; rfl
  have hint_i : ∀ i : Fin m, Integrable (fun A : Matrix (Fin m) (Fin k) ℝ =>
      H ((A *ᵥ x) i) ((A *ᵥ e) i)) (gaussMat m k v) := by
    intro i
    rw [hrow]
    refine (integrable_map_measure hΦm.aestronglyMeasurable (measurable_rowOf i).aemeasurable).1 ?_
    rw [gaussMat_row]
    exact (integrable_map_measure hΦm.aestronglyMeasurable
      (measurable_const_smul _).aemeasurable).2 hint_k
  rw [integral_finset_sum _ fun i _ => hint_i i]
  have hval : ∀ i : Fin m, ∫ A, H ((A *ᵥ x) i) ((A *ᵥ e) i) ∂gaussMat m k v = ∫ η, K η ∂stdGauss (Fin 2) := by
    intro i
    rw [hrow, ← integral_map (measurable_rowOf i).aemeasurable hΦm.aestronglyMeasurable,
      gaussMat_row, integral_map (measurable_const_smul _).aemeasurable hΦm.aestronglyMeasurable]
    simp_rw [hKA]
    rw [← integral_map hAm.aemeasurable hKm.aestronglyMeasurable, hmap]
  simp_rw [hval]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The cone moment of a quadratic at `ψ = arccos q`. -/
lemma sb_quad_q {q : ℝ} (hq : q ^ 2 < 1) (A B C : ℝ) :
    ∫ η, posI (η 0) * posI (q * η 0 + √(1 - q ^ 2) * η 1) *
      (A * η 0 ^ 2 + B * (η 0 * η 1) + C * η 1 ^ 2) ∂stdGauss (Fin 2) =
      kdot q / 2 * (A + C) + q * √(1 - q ^ 2) / (2 * π) * (A - C) + B * (1 - q ^ 2) / (2 * π) := by
  have hq1 : -1 ≤ q ∧ q ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (q + 1), sq_nonneg (q - 1)]
  have h := sb_core2D_quad (Real.arccos_nonneg q) (Real.arccos_le_pi q) A B C
  rw [Real.cos_arccos hq1.1 hq1.2, Real.sin_arccos, sb_F_diff hq1.1 hq1.2] at h
  exact h

section means
variable {m k : ℕ} {v : ℝ} {x x' : Fin k → ℝ}

lemma sb_frame (hx : normSq x = 1) (hx' : normSq x' = 1) (hc : (x ⬝ᵥ x') ^ 2 < 1) :
    x ⬝ᵥ x = 1 ∧ eTan x x' ⬝ᵥ eTan x x' = 1 ∧ x ⬝ᵥ eTan x x' = 0 ∧
      x' = (x ⬝ᵥ x') • x + √(1 - (x ⬝ᵥ x') ^ 2) • eTan x x' ∧
      eTan x' x = √(1 - (x ⬝ᵥ x') ^ 2) • x - (x ⬝ᵥ x') • eTan x x' := by
  have hxx : x ⬝ᵥ x = 1 := by rw [ms_dot_self, hx]
  have h1 : 0 < 1 - (x ⬝ᵥ x') ^ 2 := by linarith
  have hσ := Real.sqrt_pos.mpr h1
  have hs := Real.sq_sqrt h1.le
  refine ⟨hxx, eTan_dot_self hx hx' hc, by rw [dotProduct_comm]; exact eTan_dot_x hx hx' hc, ?_, ?_⟩
  · unfold eTan
    rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
    abel
  · unfold eTan
    rw [dotProduct_comm x' x]
    ext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    have hσ2 : √(1 - (x ⬝ᵥ x') ^ 2) ^ 2 = 1 - (x ⬝ᵥ x') ^ 2 := hs
    linear_combination (-x j) * hσ2

/-- **The first-layer cross mean** (Lemma TI): `E⟨p, a'⟩ = m·v·V(c)/2` with
`p = D₁(A₁e)`, `a' = ReLU(A₁x')`, `V(c) = √(1−c²)·κ̇(c)`; for `m = n²`, `v = 2/n` it is `n·V(c)`. -/
theorem sb_mean_pa (hv : 0 ≤ v) (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) :
    ∫ A, ∑ i, BstLean.Part151.mask ((A *ᵥ x) i) * (A *ᵥ eTan x x') i * relu ((A *ᵥ x') i)
      ∂gaussMat m k v =
      m * v * (√(1 - (x ⬝ᵥ x') ^ 2) * kdot (x ⬝ᵥ x')) / 2 := by
  obtain ⟨hxx, hee, hxe, hx'e, -⟩ := sb_frame hx hx' hc
  set c := x ⬝ᵥ x' with hcd
  set σ := √(1 - c ^ 2) with hσd
  set e := eTan x x' with hed
  have hlin : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∀ i, (A *ᵥ x') i = c * (A *ᵥ x) i + σ * (A *ᵥ e) i := by
    intro A i
    rw [hx'e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  let H : ℝ → ℝ → ℝ := fun s t => posI s * t * relu (c * s + σ * t)
  have hH : Measurable (Function.uncurry H) := by
    have : Function.uncurry H = fun p : ℝ × ℝ => posI p.1 * p.2 * relu (c * p.1 + σ * p.2) := rfl
    rw [this]
    exact ((measurable_posI.comp measurable_fst).mul measurable_snd).mul
      (measurable_relu.comp (by fun_prop))
  have hHs : ∀ η : Fin 2 → ℝ, H (√v * η 0) (√v * η 1) =
      v * (posI (η 0) * posI (c * η 0 + σ * η 1) *
        (0 * η 0 ^ 2 + c * (η 0 * η 1) + σ * η 1 ^ 2)) := by
    intro η
    have hsv := Real.sqrt_nonneg v
    have hvv := Real.mul_self_sqrt hv
    by_cases h0 : v = 0
    · subst h0; simp [H]
    have hpos : 0 < √v := Real.sqrt_pos.mpr (lt_of_le_of_ne hv (Ne.symm h0))
    simp only [H]
    rw [posI_mul_of_pos hpos, show c * (√v * η 0) + σ * (√v * η 1) = √v * (c * η 0 + σ * η 1) by ring,
      relu_mul_of_nonneg hsv, sb_relu_eq]
    linear_combination (posI (η 0) * η 1 * posI (c * η 0 + σ * η 1) * (c * η 0 + σ * η 1)) * hvv
  have hint : Integrable (fun η : Fin 2 → ℝ => H (√v * η 0) (√v * η 1)) (stdGauss (Fin 2)) := by
    simp_rw [hHs]
    refine Integrable.const_mul ?_ v
    refine sb_int2 ?_ (|c| + σ + 1) fun η => ?_
    · exact ((measurable_posI.comp (measurable_pi_apply 0)).mul
        (measurable_posI.comp (by fun_prop))).mul (by fun_prop)
    · have h1 := sb_posI_le (η 0)
      have h2 := sb_posI_le (c * η 0 + σ * η 1)
      have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
      have hI : |posI (η 0) * posI (c * η 0 + σ * η 1)| ≤ 1 := by
        rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]; nlinarith
      have hQ : |0 * η 0 ^ 2 + c * (η 0 * η 1) + σ * η 1 ^ 2| ≤ (|c| + σ + 1) * (η 0 ^ 2 + η 1 ^ 2) := by
        have t1 : |c * (η 0 * η 1)| ≤ |c| * (η 0 ^ 2 + η 1 ^ 2) := by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_mul]
          nlinarith [sq_abs (η 0), sq_abs (η 1), sq_nonneg (|η 0| - |η 1|)]
        have t2 : |σ * η 1 ^ 2| ≤ σ * (η 0 ^ 2 + η 1 ^ 2) := by
          rw [abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (η 0)]) hσ0
        have t3 := abs_add_le (c * (η 0 * η 1)) (σ * η 1 ^ 2)
        rw [zero_mul, zero_add]
        nlinarith [sq_nonneg (η 0), sq_nonneg (η 1)]
      rw [abs_mul]
      calc |posI (η 0) * posI (c * η 0 + σ * η 1)| * |0 * η 0 ^ 2 + c * (η 0 * η 1) + σ * η 1 ^ 2|
          ≤ 1 * ((|c| + σ + 1) * (η 0 ^ 2 + η 1 ^ 2)) := mul_le_mul hI hQ (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hsum : (fun A : Matrix (Fin m) (Fin k) ℝ => ∑ i, BstLean.Part151.mask ((A *ᵥ x) i) *
      (A *ᵥ e) i * relu ((A *ᵥ x') i)) = fun A => ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) := by
    funext A
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H, sb_mask_eq, hlin A i]
  rw [hsum, sb_rows hv hxx hee hxe hH hint]
  simp_rw [hHs]
  rw [integral_const_mul, hσd, sb_quad_q hc]
  rw [← hσd]
  have hσsq : σ ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by linarith)
  field_simp
  linear_combination (-(m : ℝ) * v * c) * hσsq

/-- **The first-layer tangent mean** (Lemma TI): `E⟨p, p'⟩ = m·v·M(c)/2` with
`p = D₁(A₁e)`, `p' = D₁'(A₁e')`, `M(c) = √(1−c²)/π − c·κ̇(c)`; for `m = n²`, `v = 2/n` it is
`n·M(c)`. -/
theorem sb_mean_pp (hv : 0 ≤ v) (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) :
    ∫ A, ∑ i, (BstLean.Part151.mask ((A *ᵥ x) i) * (A *ᵥ eTan x x') i) *
      (BstLean.Part151.mask ((A *ᵥ x') i) * (A *ᵥ eTan x' x) i) ∂gaussMat m k v =
      m * v * (√(1 - (x ⬝ᵥ x') ^ 2) / π - (x ⬝ᵥ x') * kdot (x ⬝ᵥ x')) / 2 := by
  obtain ⟨hxx, hee, hxe, hx'e, he'⟩ := sb_frame hx hx' hc
  set c := x ⬝ᵥ x' with hcd
  set σ := √(1 - c ^ 2) with hσd
  set e := eTan x x' with hed
  have hlin : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∀ i, (A *ᵥ x') i = c * (A *ᵥ x) i + σ * (A *ᵥ e) i := by
    intro A i
    rw [hx'e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  have hlin' : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∀ i, (A *ᵥ eTan x' x) i =
      σ * (A *ᵥ x) i - c * (A *ᵥ e) i := by
    intro A i
    rw [he', Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  let H : ℝ → ℝ → ℝ := fun s t => posI s * t * (posI (c * s + σ * t) * (σ * s - c * t))
  have hH : Measurable (Function.uncurry H) := by
    have : Function.uncurry H = fun p : ℝ × ℝ =>
        posI p.1 * p.2 * (posI (c * p.1 + σ * p.2) * (σ * p.1 - c * p.2)) := rfl
    rw [this]
    exact ((measurable_posI.comp measurable_fst).mul measurable_snd).mul
      ((measurable_posI.comp (by fun_prop)).mul (by fun_prop))
  have hHs : ∀ η : Fin 2 → ℝ, H (√v * η 0) (√v * η 1) =
      v * (posI (η 0) * posI (c * η 0 + σ * η 1) *
        (0 * η 0 ^ 2 + σ * (η 0 * η 1) + (-c) * η 1 ^ 2)) := by
    intro η
    have hsv := Real.sqrt_nonneg v
    have hvv := Real.mul_self_sqrt hv
    by_cases h0 : v = 0
    · subst h0; simp [H]
    have hpos : 0 < √v := Real.sqrt_pos.mpr (lt_of_le_of_ne hv (Ne.symm h0))
    simp only [H]
    rw [posI_mul_of_pos hpos, show c * (√v * η 0) + σ * (√v * η 1) = √v * (c * η 0 + σ * η 1) by ring,
      posI_mul_of_pos hpos]
    linear_combination (posI (η 0) * η 1 * posI (c * η 0 + σ * η 1) * (σ * η 0 - c * η 1)) * hvv
  have hint : Integrable (fun η : Fin 2 → ℝ => H (√v * η 0) (√v * η 1)) (stdGauss (Fin 2)) := by
    simp_rw [hHs]
    refine Integrable.const_mul ?_ v
    refine sb_int2 ?_ (|c| + σ + 1) fun η => ?_
    · exact ((measurable_posI.comp (measurable_pi_apply 0)).mul
        (measurable_posI.comp (by fun_prop))).mul (by fun_prop)
    · have h1 := sb_posI_le (η 0)
      have hc0 : 0 ≤ |c| := abs_nonneg c
      have h2 := sb_posI_le (c * η 0 + σ * η 1)
      have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
      have hI : |posI (η 0) * posI (c * η 0 + σ * η 1)| ≤ 1 := by
        rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]; nlinarith
      have hQ : |0 * η 0 ^ 2 + σ * (η 0 * η 1) + (-c) * η 1 ^ 2| ≤
          (|c| + σ + 1) * (η 0 ^ 2 + η 1 ^ 2) := by
        have t1 : |σ * (η 0 * η 1)| ≤ σ * (η 0 ^ 2 + η 1 ^ 2) := by
          rw [abs_mul, abs_of_nonneg hσ0]
          refine mul_le_mul_of_nonneg_left ?_ hσ0
          rw [abs_mul]
          nlinarith [sq_abs (η 0), sq_abs (η 1), sq_nonneg (|η 0| - |η 1|)]
        have t2 : |(-c) * η 1 ^ 2| ≤ |c| * (η 0 ^ 2 + η 1 ^ 2) := by
          rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (η 1))]
          exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (η 0)]) hc0
        have t3 := abs_add_le (σ * (η 0 * η 1)) ((-c) * η 1 ^ 2)
        rw [zero_mul, zero_add]
        nlinarith [sq_nonneg (η 0), sq_nonneg (η 1)]
      rw [abs_mul]
      calc |posI (η 0) * posI (c * η 0 + σ * η 1)| * |0 * η 0 ^ 2 + σ * (η 0 * η 1) + (-c) * η 1 ^ 2|
          ≤ 1 * ((|c| + σ + 1) * (η 0 ^ 2 + η 1 ^ 2)) := mul_le_mul hI hQ (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hsum : (fun A : Matrix (Fin m) (Fin k) ℝ => ∑ i, (BstLean.Part151.mask ((A *ᵥ x) i) *
      (A *ᵥ e) i) * (BstLean.Part151.mask ((A *ᵥ x') i) * (A *ᵥ eTan x' x) i)) =
      fun A => ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) := by
    funext A
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H, sb_mask_eq, hlin A i, hlin' A i]
  rw [hsum, sb_rows hv hxx hee hxe hH hint]
  simp_rw [hHs]
  rw [integral_const_mul, hσd, sb_quad_q hc]
  rw [← hσd]
  have hp := pi_pos
  field_simp
  ring

end means

/-! ## The row-sum deviation tails -/

/-- `stdGauss (Fin k)` pushed by `ξ ↦ ξ·x` (unit `x`) is `N(0, 1)`. -/
lemma sb_map_dot {k : ℕ} {x e : Fin k → ℝ} (hxx : x ⬝ᵥ x = 1) (hee : e ⬝ᵥ e = 1)
    (hxe : x ⬝ᵥ e = 0) (j : Fin 2) :
    (stdGauss (Fin k)).map (fun ξ => (Matrix.of ![x, e]).mulVec ξ j) = gaussianReal 0 1 := by
  have hA : Measurable (fun ξ : Fin k → ℝ => (Matrix.of ![x, e]).mulVec ξ) :=
    measurable_mulVec_left _
  have e1 : (fun ξ : Fin k → ℝ => (Matrix.of ![x, e]).mulVec ξ j) =
      Function.eval j ∘ (fun ξ => (Matrix.of ![x, e]).mulVec ξ) := rfl
  rw [e1, ← Measure.map_map (measurable_pi_apply j) hA, sb_map_two hxx hee hxe]
  exact (measurePreserving_eval (μ := fun _ : Fin 2 => gaussianReal 0 1) j).map_eq

/-- **The row-sum deviation tail** (paper: the row-sum inequality applied to a first-layer sum):
for orthonormal `x, e`, `v > 0` and a measurable `H` with
`|H(√v s, √v t)| ≤ b(s² + t²)/2` (`b > 0`), under `gaussMat m k v`:
`Pr(|Σᵢ H((A x)ᵢ, (A e)ᵢ) − m·E H(√v η₀, √v η₁)| > 2b(√(2mτ) + τ)) ≤ 2e^{−τ}`. -/
theorem sb_dev {m k : ℕ} {v : ℝ} (hv : 0 < v) {x e : Fin k → ℝ} (hxx : x ⬝ᵥ x = 1)
    (hee : e ⬝ᵥ e = 1) (hxe : x ⬝ᵥ e = 0) {H : ℝ → ℝ → ℝ} (hH : Measurable (Function.uncurry H))
    {b τ : ℝ} (hb : 0 < b) (hdom : ∀ s t, |H (√v * s) (√v * t)| ≤ b * (s ^ 2 + t ^ 2) / 2)
    (hm : 0 < m) (hτ : 0 ≤ τ) :
    (gaussMat m k v).real {A | 2 * b * (√(2 * m * τ) + τ) <
      |∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) - m * ∫ η, H (√v * η 0) (√v * η 1) ∂stdGauss (Fin 2)|} ≤
      2 * exp (-τ) := by
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  set ρ : Measure (Fin k → ℝ) := (stdGauss (Fin k)).map (fun ξ => √v • ξ) with hρ
  have hρp : IsProbabilityMeasure ρ := by
    rw [hρ]; exact (Measure.isProbabilityMeasure_map_iff (measurable_const_smul _).aemeasurable).2
      inferInstance
  set P : Measure (Fin m → Fin k → ℝ) := Measure.pi fun _ : Fin m => ρ with hP
  have hPp : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hrows : Measurable (fun G : Matrix (Fin m) (Fin k) ℝ => fun i => rowOf i G) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  have hmap : (gaussMat m k v).map (fun G i => rowOf i G) = P := by
    rw [hP, hρ]; exact BstLean.Part148.gaussMat_rows_map m k v
  set Φ : (Fin k → ℝ) → ℝ := fun r => H (r ⬝ᵥ x) (r ⬝ᵥ e) with hΦ
  have hΦm : Measurable Φ := by
    have e' : Φ = Function.uncurry H ∘ (fun r : Fin k → ℝ => (r ⬝ᵥ x, r ⬝ᵥ e)) := rfl
    rw [e']
    refine hH.comp (Measurable.prodMk ?_ ?_)
    · simp only [dotProduct]; fun_prop
    · simp only [dotProduct]; fun_prop
  set K : (Fin 2 → ℝ) → ℝ := fun η => H (√v * η 0) (√v * η 1) with hK
  have hKm : Measurable K := by
    have e' : K = Function.uncurry H ∘ (fun η : Fin 2 → ℝ => (√v * η 0, √v * η 1)) := rfl
    rw [e']; exact hH.comp (by fun_prop)
  have hAm : Measurable (fun ξ : Fin k → ℝ => (Matrix.of ![x, e]).mulVec ξ) :=
    measurable_mulVec_left _
  have hKA : ∀ ξ : Fin k → ℝ, Φ (√v • ξ) = K ((Matrix.of ![x, e]).mulVec ξ) := by
    intro ξ
    simp only [hΦ, hK, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [smul_dotProduct, smul_dotProduct, dotProduct_comm x ξ, dotProduct_comm e ξ]
    rfl
  -- the mean of one row
  have hmean : ∫ r, Φ r ∂ρ = ∫ η, K η ∂stdGauss (Fin 2) := by
    rw [hρ, integral_map (measurable_const_smul _).aemeasurable hΦm.aestronglyMeasurable]
    simp_rw [hKA]
    rw [← integral_map hAm.aemeasurable hKm.aestronglyMeasurable, sb_map_two hxx hee hxe]
  -- the event
  have hS : MeasurableSet {ω : Fin m → Fin k → ℝ | 2 * b * (√(2 * m * τ) + τ) <
      |∑ i, Φ (ω i) - m * ∫ η, K η ∂stdGauss (Fin 2)|} :=
    measurableSet_lt measurable_const
      (((Finset.measurable_sum _ fun i _ => hΦm.comp (measurable_pi_apply i)).sub_const _).abs)
  have e1 : {A : Matrix (Fin m) (Fin k) ℝ | 2 * b * (√(2 * m * τ) + τ) <
      |∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) - m * ∫ η, H (√v * η 0) (√v * η 1) ∂stdGauss (Fin 2)|} =
      (fun G i => rowOf i G) ⁻¹' {ω | 2 * b * (√(2 * m * τ) + τ) <
        |∑ i, Φ (ω i) - m * ∫ η, K η ∂stdGauss (Fin 2)|} := rfl
  rw [e1, ← map_measureReal_apply hrows hS, hmap]
  -- the row sum under `P`
  set X : Fin m → (Fin m → Fin k → ℝ) → ℝ := fun j ω => Φ (ω j) with hX
  set U : Fin m → (Fin m → Fin k → ℝ) → ℝ := fun j ω => (ω j ⬝ᵥ x) / √v with hU
  set V : Fin m → (Fin m → Fin k → ℝ) → ℝ := fun j ω => (ω j ⬝ᵥ e) / √v with hV
  have hind : iIndepFun X P := by
    rw [hP]
    exact iIndepFun_pi (μ := fun _ : Fin m => ρ) (X := fun _ r => Φ r)
      (fun _ => hΦm.aemeasurable)
  have hXm : ∀ j, Measurable (X j) := fun j => hΦm.comp (measurable_pi_apply j)
  have hdotm : ∀ (w : Fin k → ℝ) (j : Fin m), Measurable
      (fun ω : Fin m → Fin k → ℝ => (ω j ⬝ᵥ w) / √v) := by
    intro w j
    refine Measurable.div_const ?_ _
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp (measurable_pi_apply j)).mul_const _
  have hmapUV : ∀ (j : Fin m) (i : Fin 2), P.map (fun ω => ((Matrix.of ![x, e]).mulVec (ω j)) i / √v) =
      gaussianReal 0 1 := by
    intro j i
    have hev : P.map (Function.eval j) = ρ := by
      rw [hP]; exact (measurePreserving_eval (μ := fun _ : Fin m => ρ) j).map_eq
    have hg : Measurable (fun r : Fin k → ℝ => ((Matrix.of ![x, e]).mulVec r) i / √v) :=
      ((measurable_pi_apply i).comp (measurable_mulVec_left _)).div_const _
    have e2 : (fun ω : Fin m → Fin k → ℝ => ((Matrix.of ![x, e]).mulVec (ω j)) i / √v) =
        (fun r : Fin k → ℝ => ((Matrix.of ![x, e]).mulVec r) i / √v) ∘ Function.eval j := rfl
    rw [e2, ← Measure.map_map hg (measurable_pi_apply j), hev, hρ,
      Measure.map_map hg (measurable_const_smul _)]
    have e3 : ((fun r : Fin k → ℝ => ((Matrix.of ![x, e]).mulVec r) i / √v) ∘ fun ξ => √v • ξ) =
        fun ξ => (Matrix.of ![x, e]).mulVec ξ i := by
      funext ξ
      simp only [Function.comp, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [e3, sb_map_dot hxx hee hxe i]
  have hUeq : ∀ j, U j = fun ω => ((Matrix.of ![x, e]).mulVec (ω j)) 0 / √v := by
    intro j; funext ω
    simp [hU, Matrix.mulVec, dotProduct_comm]
  have hVeq : ∀ j, V j = fun ω => ((Matrix.of ![x, e]).mulVec (ω j)) 1 / √v := by
    intro j; funext ω
    simp [hV, Matrix.mulVec, dotProduct_comm]
  have hUd : ∀ j, P.map (U j) = gaussianReal 0 1 := fun j => by rw [hUeq]; exact hmapUV j 0
  have hVd : ∀ j, P.map (V j) = gaussianReal 0 1 := fun j => by rw [hVeq]; exact hmapUV j 1
  have hdom' : ∀ j ω, |X j ω| ≤ b * (U j ω ^ 2 + V j ω ^ 2) / 2 := by
    intro j ω
    have h := hdom (U j ω) (V j ω)
    have e4 : √v * U j ω = ω j ⬝ᵥ x := by simp only [hU]; field_simp
    have e5 : √v * V j ω = ω j ⬝ᵥ e := by simp only [hV]; field_simp
    rw [e4, e5] at h
    exact h
  have hbr := bn_rowsum hind hXm (fun j => hdotm x j) (fun j => hdotm e j) hUd hVd hb hdom' hm hτ
  have hEX : ∀ j, ∫ ω, X j ω ∂P = ∫ η, K η ∂stdGauss (Fin 2) := by
    intro j
    rw [hP, integral_comp_eval (μ := fun _ : Fin m => ρ) (i := j) hΦm.aestronglyMeasurable, hmean]
  refine le_trans (measureReal_mono (fun ω hω => ?_)) hbr
  simp only [Set.mem_setOf_eq] at hω ⊢
  simp_rw [hEX]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact hω

/-- `sb_dev` with the mean given as `E Σᵢ H`. -/
theorem sb_dev_mean {m k : ℕ} {v : ℝ} (hv : 0 < v) {x e : Fin k → ℝ} (hxx : x ⬝ᵥ x = 1)
    (hee : e ⬝ᵥ e = 1) (hxe : x ⬝ᵥ e = 0) {H : ℝ → ℝ → ℝ} (hH : Measurable (Function.uncurry H))
    {b τ Mv : ℝ} (hb : 0 < b) (hdom : ∀ s t, |H (√v * s) (√v * t)| ≤ b * (s ^ 2 + t ^ 2) / 2)
    (hm : 0 < m) (hτ : 0 ≤ τ)
    (hmean : ∫ A, ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) ∂gaussMat m k v = Mv) :
    (gaussMat m k v).real {A | 2 * b * (√(2 * m * τ) + τ) <
      |∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) - Mv|} ≤ 2 * exp (-τ) := by
  have hKm : Measurable (fun η : Fin 2 → ℝ => H (√v * η 0) (√v * η 1)) := by
    have e' : (fun η : Fin 2 → ℝ => H (√v * η 0) (√v * η 1)) =
        Function.uncurry H ∘ (fun η : Fin 2 → ℝ => (√v * η 0, √v * η 1)) := rfl
    rw [e']; exact hH.comp (by fun_prop)
  have hint : Integrable (fun η : Fin 2 → ℝ => H (√v * η 0) (√v * η 1)) (stdGauss (Fin 2)) :=
    sb_int2 hKm (b / 2) fun η => by
      have := hdom (η 0) (η 1); linarith
  have hr := sb_rows hv.le hxx hee hxe hH hint (m := m)
  rw [hmean] at hr
  rw [hr]
  exact sb_dev hv hxx hee hxe hH hb hdom hm hτ

section tails
variable {m k : ℕ} {v : ℝ} {x x' : Fin k → ℝ}

/-- **The cross-sum deviation tail** (Lemma TI, the first cross sum): with envelope `3v`,
`Pr(|⟨p, a'⟩ − m·v·V(c)/2| > 2·3v(√(2mτ) + τ)) ≤ 2e^{−τ}`; for `m = n²`, `v = γ = 2/n` this is
`Pr(|⟨p, a'⟩ − nV(c)| > r₁) ≤ 2e^{−τ}`, `r₁ = 2·3γ(√(2mτ) + τ)`. -/
theorem sb_tail_pa (hv : 0 < v) (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (hm : 0 < m) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m k v).real {A | 2 * (3 * v) * (√(2 * m * τ) + τ) <
      |∑ i, BstLean.Part151.mask ((A *ᵥ x) i) * (A *ᵥ eTan x x') i * relu ((A *ᵥ x') i) -
        m * v * (√(1 - (x ⬝ᵥ x') ^ 2) * kdot (x ⬝ᵥ x')) / 2|} ≤ 2 * exp (-τ) := by
  obtain ⟨hxx, hee, hxe, hx'e, -⟩ := sb_frame hx hx' hc
  set c := x ⬝ᵥ x' with hcd
  have hc1 : |c| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (c + 1), sq_nonneg (c - 1)]
  set σ := √(1 - c ^ 2) with hσd
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ1 : σ ≤ 1 := by
    rw [hσd, Real.sqrt_le_one]; nlinarith [sq_nonneg c]
  set e := eTan x x' with hed
  have hlin : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∀ i, (A *ᵥ x') i = c * (A *ᵥ x) i + σ * (A *ᵥ e) i := by
    intro A i
    rw [hx'e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  let H : ℝ → ℝ → ℝ := fun s t => posI s * t * relu (c * s + σ * t)
  have hH : Measurable (Function.uncurry H) := by
    have : Function.uncurry H = fun p : ℝ × ℝ => posI p.1 * p.2 * relu (c * p.1 + σ * p.2) := rfl
    rw [this]
    exact ((measurable_posI.comp measurable_fst).mul measurable_snd).mul
      (measurable_relu.comp (by fun_prop))
  have hsum : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∑ i, BstLean.Part151.mask ((A *ᵥ x) i) *
      (A *ᵥ e) i * relu ((A *ᵥ x') i) = ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) := by
    intro A
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H, sb_mask_eq, hlin A i]
  have hdom : ∀ s t, |H (√v * s) (√v * t)| ≤ (3 * v) * (s ^ 2 + t ^ 2) / 2 := by
    intro s t
    have hsv := Real.sqrt_nonneg v
    have hvv := Real.mul_self_sqrt hv.le
    have hp := Real.sqrt_pos.mpr hv
    simp only [H]
    rw [posI_mul_of_pos hp, show c * (√v * s) + σ * (√v * t) = √v * (c * s + σ * t) by ring,
      relu_mul_of_nonneg hsv]
    have h1 := sb_posI_le s
    have hr0 : 0 ≤ relu (c * s + σ * t) := le_max_left _ _
    have hr1 : relu (c * s + σ * t) ≤ |s| + |t| := by
      unfold relu
      refine max_le (by positivity) ?_
      have := abs_le.mp (abs_add_le (c * s) (σ * t))
      have t1 : |c * s| ≤ |s| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hc1
      have t2 : |σ * t| ≤ |t| := by
        rw [abs_mul, abs_of_nonneg hσ0]; exact mul_le_of_le_one_left (abs_nonneg _) hσ1
      linarith [le_abs_self (c * s + σ * t), abs_add_le (c * s) (σ * t)]
    have e' : posI s * (√v * t) * (√v * relu (c * s + σ * t)) =
        v * (posI s * t * relu (c * s + σ * t)) := by
      linear_combination (posI s * t * relu (c * s + σ * t)) * hvv
    rw [e', abs_mul, abs_of_pos hv]
    have hb2 : |posI s * t * relu (c * s + σ * t)| ≤ |t| * (|s| + |t|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg h1.1]
      have := abs_nonneg t
      calc posI s * |t| * relu (c * s + σ * t) ≤ 1 * |t| * (|s| + |t|) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h1.2 this) hr1 hr0 (by positivity)
        _ = _ := by ring
    have hq : |t| * (|s| + |t|) ≤ 3 * (s ^ 2 + t ^ 2) / 2 := by
      nlinarith [sq_abs s, sq_abs t, sq_nonneg (|s| - |t|), abs_nonneg s, abs_nonneg t]
    nlinarith
  have hmean : ∫ A, ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) ∂gaussMat m k v =
      m * v * (σ * kdot c) / 2 := by
    have := sb_mean_pa (m := m) hv.le hx hx' hc
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun A => (hsum A).symm)
  have h := sb_dev_mean hv hxx hee hxe hH (by positivity) hdom hm hτ hmean
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext A
  simp only [Set.mem_setOf_eq, hsum A]

/-- **The tangent-sum deviation tail** (Lemma TI, the tangent sum): with envelope `2v`,
`Pr(|⟨p, p'⟩ − m·v·M(c)/2| > 2·2v(√(2mτ) + τ)) ≤ 2e^{−τ}` (the quadratic form `V(σU − cV)` has
eigenvalues `(−c ± 1)/2`, of absolute value at most one). -/
theorem sb_tail_pp (hv : 0 < v) (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (hm : 0 < m) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m k v).real {A | 2 * (2 * v) * (√(2 * m * τ) + τ) <
      |∑ i, (BstLean.Part151.mask ((A *ᵥ x) i) * (A *ᵥ eTan x x') i) *
          (BstLean.Part151.mask ((A *ᵥ x') i) * (A *ᵥ eTan x' x) i) -
        m * v * (√(1 - (x ⬝ᵥ x') ^ 2) / π - (x ⬝ᵥ x') * kdot (x ⬝ᵥ x')) / 2|} ≤
      2 * exp (-τ) := by
  obtain ⟨hxx, hee, hxe, hx'e, he'⟩ := sb_frame hx hx' hc
  set c := x ⬝ᵥ x' with hcd
  have hc1 : -1 ≤ c ∧ c ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (c + 1), sq_nonneg (c - 1)]
  set σ := √(1 - c ^ 2) with hσd
  have hσsq : σ ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by linarith)
  set e := eTan x x' with hed
  have hlin : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∀ i, (A *ᵥ x') i = c * (A *ᵥ x) i + σ * (A *ᵥ e) i := by
    intro A i
    rw [hx'e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  have hlin' : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∀ i, (A *ᵥ eTan x' x) i =
      σ * (A *ᵥ x) i - c * (A *ᵥ e) i := by
    intro A i
    rw [he', Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  let H : ℝ → ℝ → ℝ := fun s t => posI s * t * (posI (c * s + σ * t) * (σ * s - c * t))
  have hH : Measurable (Function.uncurry H) := by
    have : Function.uncurry H = fun p : ℝ × ℝ =>
        posI p.1 * p.2 * (posI (c * p.1 + σ * p.2) * (σ * p.1 - c * p.2)) := rfl
    rw [this]
    exact ((measurable_posI.comp measurable_fst).mul measurable_snd).mul
      ((measurable_posI.comp (by fun_prop)).mul (by fun_prop))
  have hsum : ∀ A : Matrix (Fin m) (Fin k) ℝ, ∑ i, (BstLean.Part151.mask ((A *ᵥ x) i) *
      (A *ᵥ e) i) * (BstLean.Part151.mask ((A *ᵥ x') i) * (A *ᵥ eTan x' x) i) =
      ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) := by
    intro A
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H, sb_mask_eq, hlin A i, hlin' A i]
  have hdom : ∀ s t, |H (√v * s) (√v * t)| ≤ (2 * v) * (s ^ 2 + t ^ 2) / 2 := by
    intro s t
    have hvv := Real.mul_self_sqrt hv.le
    have hp := Real.sqrt_pos.mpr hv
    simp only [H]
    rw [posI_mul_of_pos hp, show c * (√v * s) + σ * (√v * t) = √v * (c * s + σ * t) by ring,
      posI_mul_of_pos hp]
    have h1 := sb_posI_le s
    have h2 := sb_posI_le (c * s + σ * t)
    have e' : posI s * (√v * t) * (posI (c * s + σ * t) * (σ * (√v * s) - c * (√v * t))) =
        v * (posI s * posI (c * s + σ * t) * (σ * s * t - c * t ^ 2)) := by
      linear_combination (posI s * posI (c * s + σ * t) * (σ * s * t - c * t ^ 2)) * hvv
    rw [e', abs_mul, abs_of_pos hv, abs_mul, abs_of_nonneg (mul_nonneg h1.1 h2.1)]
    have hQ : |σ * s * t - c * t ^ 2| ≤ s ^ 2 + t ^ 2 := by
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg (s + σ * t / 2), hσsq, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c)
          (by linarith : (0:ℝ) ≤ 3 - c), sq_nonneg t]
      · nlinarith [sq_nonneg (s - σ * t / 2), hσsq, mul_nonneg (by linarith : (0:ℝ) ≤ 1 + c)
          (by linarith : (0:ℝ) ≤ 3 + c), sq_nonneg t]
    have hI : posI s * posI (c * s + σ * t) ≤ 1 := by nlinarith
    have hI0 : 0 ≤ posI s * posI (c * s + σ * t) := mul_nonneg h1.1 h2.1
    calc v * (posI s * posI (c * s + σ * t) * |σ * s * t - c * t ^ 2|)
        ≤ v * (1 * (s ^ 2 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hI hQ (abs_nonneg _) zero_le_one) hv.le
      _ = _ := by ring
  have hmean : ∫ A, ∑ i, H ((A *ᵥ x) i) ((A *ᵥ e) i) ∂gaussMat m k v =
      m * v * (σ / π - c * kdot c) / 2 := by
    have := sb_mean_pp (m := m) hv.le hx hx' hc
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun A => (hsum A).symm)
  have h := sb_dev_mean hv hxx hee hxe hH (by positivity) hdom hm hτ hmean
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext A
  simp only [Set.mem_setOf_eq, hsum A]

end tails

end BstLean.Part182

open BstLean.Part182 in
#print axioms sb_polar_quad
open BstLean.Part182 in
#print axioms sb_core2D_quad
open BstLean.Part182 in
#print axioms sb_mean_pa
open BstLean.Part182 in
#print axioms sb_mean_pp
open BstLean.Part182 in
#print axioms sb_dev
open BstLean.Part182 in
#print axioms sb_tail_pa
open BstLean.Part182 in
#print axioms sb_tail_pp
