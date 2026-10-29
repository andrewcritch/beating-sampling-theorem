import BstLean.Part171Row
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Collect the common latitude powers before endpoint evaluation.
The latitude parameter is `q = 1 - s²`. The bulk guard is `0 < q`. -/
namespace BstLean.Part213
open Real
open BstLean.Part171 (TF TW)
open BstLean.Part153 (phiG)

/-- The variance term keeps its common latitude factor. -/
lemma collected_variance (q h v : ℝ) : q * v + (q * h) ^ 2 = q * (v + q * h ^ 2) := by
  ring

/-- Collect the latitude power in the order-eight bad-variance mass. -/
theorem collected_bad_mass {q gap e : ℝ} (hq : 0 < q) (hg : 0 < gap) :
    (√q * e / (q * gap)) ^ 8 = (e / gap) ^ 8 / q ^ 4 := by
  have hs : √q ^ 2 = q := sq_sqrt hq.le
  have he : √q ^ 8 = q ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, hs]
  rw [div_pow, mul_pow, he, mul_pow, div_pow]
  field_simp
  <;> ring

/-- Choose the upper endpoint for a nonnegative real exponent. -/
theorem latitude_power_upper {q lo hi a : ℝ} (hlo : 0 < lo)
    (hql : lo ≤ q) (hqh : q ≤ hi) (ha : 0 ≤ a) : q ^ a ≤ hi ^ a :=
  rpow_le_rpow (hlo.le.trans hql) hqh ha

/-- Choose the lower endpoint for a nonpositive real exponent. -/
theorem latitude_power_lower {q lo hi a : ℝ} (hlo : 0 < lo)
    (hql : lo ≤ q) (_hqh : q ≤ hi) (ha : a ≤ 0) : q ^ a ≤ lo ^ a :=
  rpow_le_rpow_of_nonpos hlo hql ha

/-- A nonnegative coefficient preserves each collected endpoint bound. -/
theorem latitude_monomial_bound {q lo hi a c : ℝ} (hlo : 0 < lo)
    (hql : lo ≤ q) (hqh : q ≤ hi) (hc : 0 ≤ c) :
    c * q ^ a ≤ c * (if 0 ≤ a then hi ^ a else lo ^ a) := by
  split_ifs with ha
  · exact mul_le_mul_of_nonneg_left (latitude_power_upper hlo hql hqh ha) hc
  · exact mul_le_mul_of_nonneg_left
      (latitude_power_lower hlo hql hqh (le_of_lt (lt_of_not_ge ha))) hc

/-- The collected location formula uses the same five terms as `TF`. -/
noncomputable def collectedTF (q σ Δ Γ d h v p0 : ℝ) : ℝ :=
  √q * (phiG 0 / (2 * σ) * h + phiG 0 / (√2 * σ) * d) +
    phiG 1 / σ ^ 2 * (√d * √(v + q * h ^ 2)) +
    phiG 0 / (2 * √2 * σ ^ 3) * ((v + q * h ^ 2) / √q) +
    p0 / q ^ 4 * (2 * Δ + 3 / 2 * phiG 0 / σ * Γ / √q)

/-- The collected energy formula keeps the same variance sum inside its root. -/
noncomputable def collectedTW (q a σ Δ Γ d h v p0 : ℝ) : ℝ :=
  q * (h + d) + √q * (√2 * phiG 0 / σ * (√d * √(v + q * h ^ 2))) +
    phiG 1 / (2 * σ ^ 2) * (v + q * h ^ 2) +
    p0 / q ^ 4 * ((|a| + Δ) ^ 2 + a ^ 2 +
      2 * (|a| + √q * σ) * Δ + 4 * Γ)

/-- Collect latitude powers before any interval bounds in the location formula. -/
theorem TF_collect {q σ Δ Γ d h v p0 : ℝ} (hq : 0 < q) (hσ : 0 < σ) :
    TF (√q * σ) Δ Γ (q * d) (q * h) (q * v + (q * h) ^ 2) (p0 / q ^ 4) =
      collectedTF q σ Δ Γ d h v p0 := by
  have hs : √q ^ 2 = q := sq_sqrt hq.le
  have hsn : √q ≠ 0 := (sqrt_pos.mpr hq).ne'
  unfold TF collectedTF
  rw [collected_variance, sqrt_mul hq.le, sqrt_mul hq.le]
  generalize √q = r at *
  simp only [← hs]
  field_simp
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt]
  <;> ring

/-- Collect latitude powers before any interval bounds in the energy formula. -/
theorem TW_collect {q a σ Δ Γ d h v p0 : ℝ} (hq : 0 < q) (hσ : 0 < σ) :
    TW a (√q * σ) Δ Γ (q * d) (q * h) (q * v + (q * h) ^ 2) (p0 / q ^ 4) =
      collectedTW q a σ Δ Γ d h v p0 := by
  have hs : √q ^ 2 = q := sq_sqrt hq.le
  have hsn : √q ≠ 0 := (sqrt_pos.mpr hq).ne'
  unfold TW collectedTW
  rw [collected_variance, sqrt_mul hq.le, sqrt_mul hq.le]
  generalize √q = r at *
  simp only [← hs]
  field_simp
  <;> ring

#print axioms collected_bad_mass
#print axioms latitude_monomial_bound
#print axioms TF_collect
#print axioms TW_collect
end BstLean.Part213
