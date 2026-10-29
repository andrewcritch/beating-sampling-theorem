import BstLean.Part202Row

/-! Odd interpolation and factorial whole-row moments for BE. -/
namespace BstLean.Part202
open MeasureTheory Real Filter Set
open scoped ENNReal

lemma pow_rpow_ratio {x : ℝ} (hx : 0 ≤ x) (k j : ℕ) (hj : j ≠ 0) :
    (x ^ j) ^ ((k : ℝ) / j) = x ^ k := by
  rw [← Real.rpow_natCast_mul hx j,
    show (j : ℝ) * ((k : ℝ) / j) = k by
      have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      field_simp,
    Real.rpow_natCast]

/-- Lyapunov interpolation uses the complete probability distribution. -/
lemma moment_interpolation {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    [IsProbabilityMeasure ρ] {f : X → ℝ} (hf : Measurable f)
    {k j : ℕ} (hj : j ≠ 0) (hkj : k ≤ j)
    (ij : Integrable (fun x => |f x| ^ j) ρ) :
    (∫ x, |f x| ^ k ∂ρ) ≤ (∫ x, |f x| ^ j ∂ρ) ^ ((k : ℝ) / j) := by
  have hr0 : 0 ≤ (k : ℝ) / j := by positivity
  have hr1 : (k : ℝ) / j ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hj)]
    exact_mod_cast hkj
  have hpt : ∀ x, |f x| ^ k ≤ 1 + |f x| ^ j := by
    intro x
    by_cases h : |f x| ≤ 1
    · have h1 := pow_le_pow_left₀ (abs_nonneg (f x)) h k
      simp only [one_pow] at h1
      linarith [pow_nonneg (abs_nonneg (f x)) j]
    · have h1 := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hkj
      linarith
  have ik : Integrable (fun x => |f x| ^ k) ρ :=
    ((integrable_const (1 : ℝ)).add ij).mono'
      (hf.abs.pow_const k).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) k)]
        exact hpt x)
  have he : (fun x => (|f x| ^ j) ^ ((k : ℝ) / j)) = fun x => |f x| ^ k := by
    funext x
    exact pow_rpow_ratio (abs_nonneg _) k j hj
  have h := (Real.concaveOn_rpow hr0 hr1).le_map_integral
    (Real.continuous_rpow_const hr0).continuousOn isClosed_Ici
    (Eventually.of_forall fun x => Set.mem_Ici.mpr (pow_nonneg (abs_nonneg _) j)) ij
    (by simpa only [Function.comp_def, he] using ik)
  simpa only [he] using h

section
variable {V P : Type*} [MeasurableSpace V] [MeasurableSpace P]
variable {μ : Measure V} [IsProbabilityMeasure μ]
variable {ν : Measure P} [IsProbabilityMeasure ν] {d m : ℕ}
variable {a : V → Fin d → ℝ} {ell : ℝ}
open BstLean.Part29 (stdGauss)

/-- This scale includes the zero-trace and zero-gradient cases. -/
noncomputable def rowScale (μ : Measure V) (a : V → Fin d → ℝ) (ell : ℝ) : ℝ :=
  |ell| * √(covarianceTrace μ a)

lemma rowScale_nonneg : 0 ≤ rowScale μ a ell := by unfold rowScale; positivity

lemma rowScale_sq : rowScale μ a ell ^ 2 = ell ^ 2 * covarianceTrace μ a := by
  rw [rowScale, mul_pow, sq_abs, Real.sq_sqrt covarianceTrace_nonneg]

lemma row_even_scale (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ q, ENNReal.ofReal (|rowFluct S q| ^ (2 * p)) ∂ν.prod (stdGauss (Fin m)) ≤
      ENNReal.ofReal (evenCoefficient p * rowScale μ a ell ^ (2 * p)) := by
  rw [pow_mul, rowScale_sq]
  exact row_even_moment S ha hK hp

/-- Odd row orders follow from the next even order, after plane integration. -/
theorem row_odd_moment (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (p : ℕ) :
    ∫⁻ q, ENNReal.ofReal (|rowFluct S q| ^ (2 * p + 1)) ∂ν.prod (stdGauss (Fin m)) ≤
      ENNReal.ofReal (oddCoefficient p * rowScale μ a ell ^ (2 * p + 1)) := by
  let ρ := ν.prod (stdGauss (Fin m))
  let f := rowFluct S
  let k := 2 * p + 1
  let j := 2 * (p + 1)
  let r : ℝ := (k : ℝ) / j
  have hj : j ≠ 0 := by dsimp [j]; omega
  have hk : k ≤ j := by dsimp [k, j]; omega
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have heven := row_even_scale S ha hK (show 1 ≤ p + 1 by omega)
  have ij : Integrable (fun q => |f q| ^ j) ρ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (S.measurable_fluct.abs.pow_const j).aestronglyMeasurable
        (Eventually.of_forall fun q => pow_nonneg (abs_nonneg _) _)).mp
      (ne_of_lt (lt_of_le_of_lt heven ENNReal.ofReal_lt_top))
  have hreal : ∫ q, |f q| ^ j ∂ρ ≤ evenCoefficient (p + 1) * rowScale μ a ell ^ j := by
    rw [← ofReal_integral_eq_lintegral_ofReal ij
      (Eventually.of_forall fun q => pow_nonneg (abs_nonneg _) _)] at heven
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
      (by unfold evenCoefficient; positivity) (pow_nonneg rowScale_nonneg _))).mp heven
  have hinterp := moment_interpolation S.measurable_fluct hj hk ij
  have hbound : ∫ q, |f q| ^ k ∂ρ ≤
      (evenCoefficient (p + 1) * rowScale μ a ell ^ j) ^ r :=
    hinterp.trans (Real.rpow_le_rpow
      (integral_nonneg fun q => pow_nonneg (abs_nonneg _) _) hreal hr)
  have hcoef : (evenCoefficient (p + 1)) ^ r = oddCoefficient p := by
    unfold evenCoefficient oddCoefficient
    rw [Real.mul_rpow (by positivity) (by positivity),
      pow_rpow_ratio Real.pi_pos.le k j hj,
      ← Real.rpow_natCast_mul (BstLean.Part162.gmom_nonneg _) 2]
    dsimp [r, k, j]
    push_cast
    congr 2
    ring
  have hs : (evenCoefficient (p + 1) * rowScale μ a ell ^ j) ^ r =
      oddCoefficient p * rowScale μ a ell ^ k := by
    rw [Real.mul_rpow (by unfold evenCoefficient; positivity)
      (pow_nonneg rowScale_nonneg _), hcoef,
      pow_rpow_ratio rowScale_nonneg k j hj]
  have ik : Integrable (fun q => |f q| ^ k) ρ := by
    have hdom : ∀ q, |f q| ^ k ≤ 1 + |f q| ^ j := by
      intro q
      by_cases h : |f q| ≤ 1
      · have hh := pow_le_pow_left₀ (abs_nonneg _) h k
        simp only [one_pow] at hh
        linarith [pow_nonneg (abs_nonneg (f q)) j]
      · have hh := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hk
        linarith
    exact ((integrable_const (1 : ℝ)).add ij).mono'
      (S.measurable_fluct.abs.pow_const k).aestronglyMeasurable
        (Eventually.of_forall fun q => by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
          exact hdom q)
  rw [← ofReal_integral_eq_lintegral_ofReal ik
    (Eventually.of_forall fun q => pow_nonneg (abs_nonneg _) _)]
  exact ENNReal.ofReal_le_ofReal (hs ▸ hbound)

/-- Every whole-row moment at order at least three has the BE factorial majorant. -/
theorem row_factorial_moment (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (k : ℕ) (hk : 3 ≤ k) :
    ∫⁻ q, ENNReal.ofReal (|rowFluct S q| ^ k) ∂ν.prod (stdGauss (Fin m)) ≤
      ENNReal.ofReal ((k.factorial : ℝ) * beta ^ (k - 2) * rowScale μ a ell ^ k) := by
  have hraw : ∫⁻ q, ENNReal.ofReal (|rowFluct S q| ^ k) ∂ν.prod (stdGauss (Fin m)) ≤
      ENNReal.ofReal (coefficient k * rowScale μ a ell ^ k) := by
    by_cases he : Even k
    · have hmod := Nat.even_iff.mp he
      have heq : 2 * (k / 2) = k := by omega
      simpa only [coefficient, if_pos he, heq] using
        row_even_scale S ha hK (show 1 ≤ k / 2 by omega)
    · have hmod : k % 2 = 1 := by
        have := Nat.mod_lt k (by omega : 0 < 2)
        have hn := mt Nat.even_iff.mpr he
        omega
      have heq : 2 * (k / 2) + 1 = k := by omega
      simpa only [coefficient, if_neg he, heq] using row_odd_moment S ha hK (k / 2)
  exact hraw.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (coefficient_factorial k hk) (pow_nonneg rowScale_nonneg k)))

end
end BstLean.Part202
