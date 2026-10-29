import BstLean.Part239Generating

/-! Singleton-free coefficients and their falling-factorial polynomial. -/
namespace BstLean.Part239

/-- The recurrence retains both inadmissible boundary rows. -/
def noSingleton : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, _ => 0
  | p + 2, k => k * noSingleton (p + 1) k +
      (p + 1) * (if k = 0 then 0 else noSingleton p (k - 1))
termination_by p _ => p

theorem noSingleton_recurrence (p k : ℕ) :
    noSingleton (p + 2) (k + 1) = (k + 1) * noSingleton (p + 1) (k + 1) +
      (p + 1) * noSingleton p k := by
  simp only [noSingleton, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel]

lemma noSingleton_zero_column (p : ℕ) :
    noSingleton (p + 1) 0 = 0 := by
  cases p <;> simp [noSingleton]

/-- A nonzero coefficient has no more than half as many blocks as positions. -/
theorem noSingleton_support (p k : ℕ) (h : p < 2 * k) : noSingleton p k = 0 := by
  induction p using Nat.strong_induction_on generalizing k with
  | h p ih =>
    rcases p with _ | _ | p
    · have hk : k ≠ 0 := by omega
      simp [noSingleton, hk]
    · simp [noSingleton]
    · rw [noSingleton]
      have h1 := ih (p + 1) (by omega) k (by omega)
      rw [h1, mul_zero, zero_add]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, ih p (by omega) (k - 1) (by omega), mul_zero]

noncomputable def partitionPolynomial (p m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1), (noSingleton p k : ℝ) * (m.descFactorial k : ℝ)

lemma partitionPolynomial_half_sum (p m : ℕ) :
    partitionPolynomial p m =
      ∑ k ∈ Finset.range (p / 2 + 1), (noSingleton p k : ℝ) * (m.descFactorial k : ℝ) := by
  unfold partitionPolynomial
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k _ hk
  have hpk : p < 2 * k := by
    have : ¬ k < p / 2 + 1 := by simpa using hk
    omega
  rw [noSingleton_support p k hpk]
  simp

lemma partitionPolynomial_extend (p m K : ℕ) (hK : p + 1 ≤ K) :
    (∑ k ∈ Finset.range K, (noSingleton p k : ℝ) * (m.descFactorial k : ℝ)) =
      partitionPolynomial p m := by
  unfold partitionPolynomial
  symm
  apply Finset.sum_subset (Finset.range_mono hK)
  intro k _ hk
  have hpk : p < 2 * k := by
    have : ¬ k < p + 1 := by simpa using hk
    omega
  rw [noSingleton_support p k hpk]
  simp

lemma fallingFactorial_difference (m k : ℕ) :
    (m + 1 : ℝ) * (( (m + 1).descFactorial k : ℝ) - (m.descFactorial k : ℝ)) =
      k * ((m + 1).descFactorial k : ℝ) := by
  by_cases hk : k ≤ m + 1
  · have h := Nat.succ_descFactorial m k
    have hr : ((m + 1 : ℝ) - k) * ((m + 1).descFactorial k : ℝ) =
        (m + 1 : ℝ) * (m.descFactorial k : ℝ) := by
      have hc := congrArg (fun a : ℕ => (a : ℝ)) h
      simpa only [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_add, Nat.cast_one] using hc
    nlinarith [hr]
  · have h1 : (m + 1).descFactorial k = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    have h0 : m.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h1, h0]

/-- The polynomial obeys the same order recurrence as the generating series. -/
theorem partitionPolynomial_recurrence (p m : ℕ) :
    partitionPolynomial (p + 2) (m + 1) = (m + 1 : ℝ) *
      (partitionPolynomial (p + 1) (m + 1) - partitionPolynomial (p + 1) m +
        (p + 1 : ℝ) * partitionPolynomial p m) := by
  have hfirst :
      (∑ k ∈ Finset.range (p + 3), (k : ℝ) * (noSingleton (p + 1) k : ℝ) *
        ((m + 1).descFactorial k : ℝ)) =
      (m + 1 : ℝ) * (partitionPolynomial (p + 1) (m + 1) -
        partitionPolynomial (p + 1) m) := by
    rw [← partitionPolynomial_extend (p + 1) (m + 1) (p + 3) (by omega),
      ← partitionPolynomial_extend (p + 1) m (p + 3) (by omega),
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have h := congrArg (fun x : ℝ => (noSingleton (p + 1) k : ℝ) * x)
      (fallingFactorial_difference m k)
    nlinarith [h]
  have hsecond :
      (∑ k ∈ Finset.range (p + 3),
        ((if k = 0 then 0 else noSingleton p (k - 1) : ℕ) : ℝ) *
          ((m + 1).descFactorial k : ℝ)) =
      (m + 1 : ℝ) * partitionPolynomial p m := by
    rw [show p + 3 = (p + 2) + 1 by omega, Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      if_false, if_true, Nat.cast_zero, zero_mul, add_zero, zero_add]
    rw [← partitionPolynomial_extend p m (p + 2) (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  conv_lhs => unfold partitionPolynomial
  simp only [noSingleton, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  calc
    _ = (∑ k ∈ Finset.range (p + 3), (k : ℝ) * (noSingleton (p + 1) k : ℝ) *
        ((m + 1).descFactorial k : ℝ)) + (p + 1 : ℝ) *
        (∑ k ∈ Finset.range (p + 3),
          ((if k = 0 then 0 else noSingleton p (k - 1) : ℕ) : ℝ) *
            ((m + 1).descFactorial k : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hfirst, hsecond]; ring

#print axioms noSingleton_support
#print axioms noSingleton_recurrence
#print axioms partitionPolynomial_half_sum
#print axioms partitionPolynomial_recurrence
end BstLean.Part239
