import BstLean.Part151JF4
import BstLean.Part138Hell
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Elementary Gaussian moments for the HQ cubic price. -/
namespace BstLean.Part207
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

lemma abs_four (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]

section general
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma mem_four {f : α → ℝ} (mf : Measurable f)
    (hi : Integrable (fun x => f x ^ 4) μ) : MemLp f 4 μ := by
  apply (memLp_norm_rpow_iff (p := 4) (q := 4) mf.aestronglyMeasurable
    (by norm_num) (by norm_num)).mp
  norm_num only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_ofNat]
  rw [ENNReal.div_self (by norm_num) (by norm_num)]
  apply memLp_one_iff_integrable.mpr
  simpa only [abs_four] using hi

lemma norm_four_pow {f : α → ℝ} (mf : Measurable f) :
    lpNorm f 4 μ ^ 4 = ∫ x, f x ^ 4 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    mf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  have he : (fun x => ‖f x‖ ^ 4) = fun x => f x ^ 4 := by
    funext x; rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  rw [he, ← Real.rpow_mul_natCast (integral_nonneg fun x => by positivity)]
  norm_num

lemma norm_two_sq {f : α → ℝ} (mf : Measurable f) :
    lpNorm f 2 μ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    mf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Real.rpow_mul_natCast (integral_nonneg fun x => sq_nonneg _)]
  norm_num

lemma norm_four_le {f : α → ℝ} (mf : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hi : (∫ x, f x ^ 4 ∂μ) ≤ b ^ 4) : lpNorm f 4 μ ≤ b := by
  have h := norm_four_pow (μ := μ) mf
  have hs : lpNorm f 4 μ ^ 4 ≤ b ^ 4 := by rw [h]; exact hi
  exact le_of_pow_le_pow_left₀ (by norm_num) hb hs

lemma norm_two_le {f : α → ℝ} (mf : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (hi : (∫ x, f x ^ 2 ∂μ) ≤ b ^ 2) : lpNorm f 2 μ ≤ b := by
  have h := norm_two_sq (μ := μ) mf
  nlinarith [lpNorm_nonneg (f := f) (p := 2) (μ := μ)]

/-- Second and fourth moment bounds imply a cubic moment bound. -/
theorem cube_of_two_four [IsFiniteMeasure μ] {f : α → ℝ} (mf : Measurable f)
    (i4 : Integrable (fun x => f x ^ 4) μ) {b : ℝ} (hb : 0 ≤ b)
    (h2 : ∫ x, f x ^ 2 ∂μ ≤ b ^ 2)
    (h4 : ∫ x, f x ^ 4 ∂μ ≤ 16 * b ^ 4) :
    Integrable (fun x => |f x| ^ 3) μ ∧ ∫ x, |f x| ^ 3 ∂μ ≤ 4 * b ^ 3 := by
  have i2 := BstLean.Part151.int_pow_of_four mf i4 2 (by norm_num)
  have ia4 : Integrable (fun x => |f x| ^ 4) μ := by
    simpa only [abs_four] using i4
  have i3 := BstLean.Part151.int_pow_of_four mf.abs ia4 3 (by norm_num)
  have hcs := BstLean.Part138.cs_sq μ (f := fun x => |f x|) (g := fun x => f x ^ 2)
    (by simpa using i2) (by simpa only [← pow_mul] using i4)
    (by convert i3 using 1; funext x; rw [← sq_abs]; ring)
  have ec : (fun x => |f x| * f x ^ 2) = fun x => |f x| ^ 3 := by
    funext x; rw [← sq_abs]; ring
  simp only [ec, sq_abs, ← pow_mul] at hcs
  have h0 : 0 ≤ ∫ x, f x ^ 4 ∂μ := integral_nonneg fun x => by positivity
  have hcs' : (∫ x, |f x| ^ 3 ∂μ) ^ 2 ≤ 16 * b ^ 6 := by
    calc _ ≤ _ := hcs
      _ ≤ b ^ 2 * (16 * b ^ 4) := mul_le_mul h2 h4 h0 (sq_nonneg _)
      _ = _ := by ring
  refine ⟨i3, ?_⟩
  have hc0 : 0 ≤ ∫ x, |f x| ^ 3 ∂μ := integral_nonneg fun x => by positivity
  nlinarith [pow_nonneg hb 3, sq_nonneg ((∫ x, |f x| ^ 3 ∂μ) - 4 * b ^ 3)]
end general

/-- The centred radial quadratic has fourth moment at most sixteen times its squared variance. -/
lemma radial_four_le (n : ℕ) :
    ∫ z : Fin n → ℝ, (normSq z - n) ^ 4 ∂stdGauss (Fin n) ≤ 16 * (2 * (n : ℝ)) ^ 2 := by
  rw [(BstLean.Part151.chi_centred n).2.2.2]
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    nlinarith

end BstLean.Part207
