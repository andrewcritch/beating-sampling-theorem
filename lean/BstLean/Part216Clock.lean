import BstLean.Part216ExponentialMoment
import BstLean.Part213Norm

/-! Integrate the square-root-plus-linear Bernstein tail without splitting its charge. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal

noncomputable def tailRoot (A b y : ℝ) : ℝ := (sqrt (A ^ 2 + 4 * b * |y|) - A) / (2 * b)

lemma tailRoot_nonneg {A b y : ℝ} (hA : 0 ≤ A) (hb : 0 < b) : 0 ≤ tailRoot A b y := by
  have h : A ≤ sqrt (A ^ 2 + 4 * b * |y|) := by
    calc A = sqrt (A ^ 2) := (sqrt_sq hA).symm
      _ ≤ sqrt (A ^ 2 + 4 * b * |y|) := sqrt_le_sqrt (by nlinarith [abs_nonneg y])
  exact div_nonneg (sub_nonneg.mpr h) (by positivity)

lemma tailRoot_identity {A b y : ℝ} (hA : 0 ≤ A) (hb : 0 < b) :
    A * tailRoot A b y + b * tailRoot A b y ^ 2 = |y| := by
  have hs : sqrt (A ^ 2 + 4 * b * |y|) ^ 2 = A ^ 2 + 4 * b * |y| :=
    sq_sqrt (by positivity)
  unfold tailRoot
  field_simp
  nlinarith [hs]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The same tail clock supplies the square-root moment and the linear moment. -/
theorem sqrt_linear_tail_even {Y : Ω → ℝ} (hY : Measurable Y)
    {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {x | A * sqrt u + b * u < |Y x|} ≤ 2 * exp (-u))
    (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (|Y x| ^ (2 * p)) ∂μ ≤
      ENNReal.ofReal ((A * (2 * (p.factorial : ℝ)) ^ (((2 * p : ℕ) : ℝ)⁻¹) +
        b * (2 * ((2 * p).factorial : ℝ)) ^ (((2 * p : ℕ) : ℝ)⁻¹)) ^ (2 * p)) := by
  let U : Ω → ℝ := fun x => tailRoot A b (Y x)
  let T : Ω → ℝ := fun x => U x ^ 2
  have hU : Measurable U := by
    unfold U tailRoot
    exact (((measurable_const.add (hY.abs.const_mul (4 * b))).sqrt).sub_const A).div_const _
  have hT : Measurable T := hU.pow_const 2
  have hU0 : ∀ x, 0 ≤ U x := fun x => tailRoot_nonneg hA hb
  have hT0 : ∀ x, 0 ≤ T x := fun x => sq_nonneg _
  have he : ∀ x, A * U x + b * T x = |Y x| := fun x => tailRoot_identity hA hb
  have ht : ∀ u : ℝ, 0 < u → μ.real {x | u < T x} ≤ 2 * exp (-u) := by
    intro u hu
    refine (measureReal_mono (fun x hx => ?_)).trans (htail u hu.le)
    change u < T x at hx
    change A * sqrt u + b * u < |Y x|
    rw [← he x]
    have hus : sqrt u < U x := by
      rw [← sqrt_sq (hU0 x)]
      exact sqrt_lt_sqrt hu.le hx
    exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hus.le hA)
      (mul_lt_mul_of_pos_left hx hb)
  have hMp := exponential_tail_moment hT hT0 (by norm_num : (0 : ℝ) ≤ 2) ht p hp
  have hMq := exponential_tail_moment hT hT0 (by norm_num : (0 : ℝ) ≤ 2) ht (2 * p) (by omega)
  let q := 2 * p
  let R := (2 * (p.factorial : ℝ)) ^ ((q : ℝ)⁻¹)
  let S := (2 * (q.factorial : ℝ)) ^ ((q : ℝ)⁻¹)
  have hR0 : 0 ≤ R := rpow_nonneg (by positivity) _
  have hS0 : 0 ≤ S := rpow_nonneg (by positivity) _
  have hRp : R ^ q = 2 * (p.factorial : ℝ) := rpow_inv_natCast_pow (by positivity) (by dsimp [q]; omega)
  have hSp : S ^ q = 2 * (q.factorial : ℝ) := rpow_inv_natCast_pow (by positivity) (by dsimp [q]; omega)
  have hF : ∫⁻ x, ENNReal.ofReal (|A * U x| ^ q) ∂μ ≤ ENNReal.ofReal ((A * R) ^ q) := by
    have hex : ∀ x, |A * U x| ^ q = A ^ q * T x ^ p := by
      intro x; rw [abs_mul, abs_of_nonneg hA, abs_of_nonneg (hU0 x), mul_pow]
      simp only [T, q, pow_mul]
    simp_rw [hex, ENNReal.ofReal_mul (pow_nonneg hA q)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_pow, hRp,
      ENNReal.ofReal_mul (pow_nonneg hA q)]
    exact mul_le_mul' le_rfl hMp
  have hG : ∫⁻ x, ENNReal.ofReal (|b * T x| ^ q) ∂μ ≤ ENNReal.ofReal ((b * S) ^ q) := by
    have hex : ∀ x, |b * T x| ^ q = b ^ q * T x ^ q := by
      intro x; rw [abs_mul, abs_of_pos hb, abs_of_nonneg (hT0 x), mul_pow]
    simp_rw [hex, ENNReal.ofReal_mul (pow_nonneg hb.le q)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_pow, hSp,
      ENNReal.ofReal_mul (pow_nonneg hb.le q)]
    exact mul_le_mul' le_rfl hMq
  have hM := BstLean.Part213.moment_minkowski (hU.const_mul A) (hT.const_mul b)
    (by dsimp [q]; omega : 1 ≤ q) (mul_nonneg hA hR0) (mul_nonneg hb.le hS0) hF hG
  have hid : ∀ x, |A * U x + b * T x| ^ q = |Y x| ^ q := by
    intro x; rw [he x, abs_abs]
  simpa only [hid] using hM

/-- This is the requested order18 analytic-tail moment. -/
theorem sqrt_linear_tail_order18 {Y : Ω → ℝ} (hY : Measurable Y)
    {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {x | A * sqrt u + b * u < |Y x|} ≤ 2 * exp (-u)) :
    ∫⁻ x, ENNReal.ofReal (|Y x| ^ 18) ∂μ ≤
      ENNReal.ofReal ((A * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
        b * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹)) ^ 18) :=
  sqrt_linear_tail_even hY hA hb htail 9 (by norm_num)

#print axioms tailRoot_identity
#print axioms sqrt_linear_tail_even
#print axioms sqrt_linear_tail_order18
end BstLean.Part216
