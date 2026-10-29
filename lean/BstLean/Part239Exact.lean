import BstLean.Part239Partition
import BstLean.Part239Rows

/-! The falling-factorial formula is the exact coefficient of the centred row envelope. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real
open BstLean.Part213

lemma partitionPolynomial_order_zero (m : ℕ) : partitionPolynomial 0 m = 1 := by
  simp [partitionPolynomial, noSingleton]

lemma partitionPolynomial_order_one (m : ℕ) : partitionPolynomial 1 m = 0 := by
  simp [partitionPolynomial, noSingleton]

lemma partitionPolynomial_zero_rows (p : ℕ) : partitionPolynomial (p + 1) 0 = 0 := by
  unfold partitionPolynomial
  apply Finset.sum_eq_zero
  intro k _
  cases k with
  | zero => rw [noSingleton_zero_column]; simp
  | succ k => simp

theorem seriesRowCount_eq_partitionPolynomial (p m : ℕ) :
    seriesRowCount m p = partitionPolynomial p m := by
  induction p using Nat.strong_induction_on generalizing m with
  | h p ih =>
    rcases p with _ | _ | p
    · rw [seriesRowCount_order_zero, partitionPolynomial_order_zero]
    · rw [seriesRowCount_order_one, partitionPolynomial_order_one]
    · cases m with
      | zero => rw [seriesRowCount_zero, partitionPolynomial_zero_rows]; simp
      | succ m =>
        rw [seriesRowCount_recurrence, partitionPolynomial_recurrence,
          ih (p + 1) (by omega) (m + 1), ih (p + 1) (by omega) m, ih p (by omega) m]

/-- This identity supplies the exact finite-width row correction. -/
theorem rowEnvelope_exact (p m : ℕ) :
    rowEnvelope (fun _ => 1) m p =
      ∑ k ∈ Finset.range (p + 1), (noSingleton p k : ℝ) * (m.descFactorial k : ℝ) := by
  rw [← seriesRowCount_eq_rowEnvelope, seriesRowCount_eq_partitionPolynomial]
  rfl

def partitionTotal (p : ℕ) : ℕ := ∑ k ∈ Finset.range (p + 1), noSingleton p k

lemma partitionPolynomial_nonneg (p m : ℕ) : 0 ≤ partitionPolynomial p m := by
  unfold partitionPolynomial
  positivity

/-- The exact formula is below the general singleton-free partition bound. -/
theorem partitionPolynomial_upper (p m : ℕ) (hm : 1 ≤ m) :
    partitionPolynomial p m ≤ (partitionTotal p : ℝ) * (m : ℝ) ^ (p / 2) := by
  unfold partitionPolynomial partitionTotal
  rw [Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : 2 * k ≤ p
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hdf : (m.descFactorial k : ℝ) ≤ (m : ℝ) ^ k := by
      exact_mod_cast Nat.descFactorial_le_pow m k
    exact hdf.trans (pow_le_pow_right₀ (by exact_mod_cast hm) (by omega))
  · rw [noSingleton_support p k (by omega)]
    simp

/-- The exact coefficient bounds arbitrary even orders of nonnegative independent rows. -/
theorem nonnegative_rows_exact {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (f : Fin m → X → ℝ) (hm : ∀ j, Measurable (f j))
    (h0 : ∀ j x, 0 ≤ f j x) (hf : ∀ j, Integrable (f j) ρ)
    (hi : ∀ j k, k ≤ 2 * p → Integrable (fun x => f j x ^ k) ρ)
    (hc : ∀ j k, k ≤ 2 * p →
      Integrable (fun x => (f j x - ∫ y, f j y ∂ρ) ^ k) ρ)
    (hM : ∀ j k, 2 ≤ k → k ≤ 2 * p → ∫ x, f j x ^ k ∂ρ ≤ B ^ k) :
    ∫⁻ y, ENNReal.ofReal ((∑ j, (f j (y j) - ∫ x, f j x ∂ρ)) ^ (2 * p))
      ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (partitionPolynomial (2 * p) m * B ^ (2 * p)) := by
  have h := nonnegative_rows_even ρ hB f hm h0 hf hi hc hM
  rwa [rowAssignmentCount_cast, ← seriesRowCount_eq_rowEnvelope,
    seriesRowCount_eq_partitionPolynomial] at h

/-- The general even bound also applies to centred rows of either sign. -/
theorem centred_rows_partition {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ}
    (hm : 1 ≤ m) {B : ℝ} (hB : 0 ≤ B)
    (f : Fin m → X → ℝ) (hf : ∀ j, Measurable (f j))
    (hi : ∀ j k, k ≤ 2 * p → Integrable (fun x => f j x ^ k) ρ)
    (h0 : ∀ j, ∫ x, f j x ∂ρ = 0)
    (hM : ∀ j k, 2 ≤ k → k ≤ 2 * p → ∫ x, |f j x| ^ k ∂ρ ≤ B ^ k) :
    ∫⁻ y, ENNReal.ofReal ((∑ j, f j (y j)) ^ (2 * p))
      ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal ((partitionTotal (2 * p) : ℝ) * (m : ℝ) ^ p * B ^ (2 * p)) := by
  have h := centred_rows_even ρ (fun k => pow_nonneg hB k) f hf hi h0 hM
  rw [rowEnvelope_scale hB, ← seriesRowCount_eq_rowEnvelope,
    seriesRowCount_eq_partitionPolynomial] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hu := partitionPolynomial_upper (2 * p) m hm
  rw [show 2 * p / 2 = p by omega] at hu
  nlinarith [mul_le_mul_of_nonneg_left hu (pow_nonneg hB (2 * p))]

#print axioms rowEnvelope_exact
#print axioms partitionPolynomial_upper
#print axioms nonnegative_rows_exact
#print axioms centred_rows_partition
end BstLean.Part239
