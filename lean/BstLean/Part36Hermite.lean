import BstLean.Part36Defs

/-!
# Part 36, wave 1: the one-variable Gaussian–Fischer identity (medium)

For `g ∼ N(0,1)`: `E g^{a+b} = Σ_c c! · [t^c] e^{∂²/2} t^a · [t^c] e^{∂²/2} t^b`, that is
`gaussMom (a + b) = Σ_{c ≤ K} c! · lap1 a c · lap1 b c` for every `K ≥ min a b`.
Both sides vanish when `a + b` is odd. Suggested route: induction on `b` with the recurrences
`gaussMom (k+2) = (k+1) gaussMom k` and `t · e^{∂²/2}t^a`-type recurrences for `lap1`, or a direct
double-factorial/binomial computation (the sum is `Σ_σ a! b! / (c! 2^{σ+τ} σ! τ!)`).
The supervisor checked the identity exactly for `a, b ≤ 5` (as the `n = 1` case of the multiset identity).

Depends on `Part36Defs` only. Provers must not use `native_decide`.
-/

namespace BstLean.Part36

open BstLean.Part29 (gaussMom)

theorem lap1_self (a : ℕ) : lap1 a a = 1 := by
  simp [lap1, Nat.factorial_ne_zero]

theorem lap1_zero (a : ℕ) : lap1 a 0 = gaussMom a := by
  unfold lap1 gaussMom
  simp only [Nat.zero_le, Nat.sub_zero, true_and, Nat.factorial_zero, Nat.cast_one,
    one_mul]
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    have ha : a = 2 * k := by omega
    subst a
    have hf : (2 * k).factorial = (2 * k - 1).doubleFactorial *
        (2 ^ k * k.factorial) := by
      cases k with
      | zero => simp [Nat.doubleFactorial]
      | succ k =>
        have he : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
        rw [he, Nat.factorial_eq_mul_doubleFactorial]
        rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]
        rw [mul_comm, ← Nat.doubleFactorial_two_mul]
        congr 1
    rw [← two_mul k, Nat.mul_div_cancel_left _ (by decide : 0 < 2), hf]
    push_cast
    have hn : (2 : ℝ) ^ k * (k.factorial : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_right₀ _ hn
  · rfl

theorem lap1_eq_zero {a c : ℕ} (h : a < c ∨ ¬ Even (a - c)) : lap1 a c = 0 := by
  unfold lap1
  apply ite_eq_right
  rcases h with h | h
  · exact fun hc => (Nat.not_le_of_lt h) hc.1
  · exact fun hc => h hc.2

private lemma lap1_explicit (c s : ℕ) : lap1 (c + 2 * s) c =
    ((c + 2 * s).factorial : ℝ) /
      ((c.factorial : ℝ) * 2 ^ s * (s.factorial : ℝ)) := by
  simp [lap1]

private lemma lap1_lower (b c : ℕ) :
    (c + 1 : ℝ) * lap1 (b + 1) (c + 1) = (b + 1 : ℝ) * lap1 b c := by
  unfold lap1
  simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]
  split_ifs with h
  · rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hc : (c.factorial : ℝ) ≠ 0 := by positivity
    have hs : (((b - c) / 2).factorial : ℝ) ≠ 0 := by positivity
    have hp : (2 : ℝ) ^ ((b - c) / 2) ≠ 0 := by positivity
    have hc1 : (c + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  · simp

private lemma mom_rec (a : ℕ) : gaussMom (a + 2) = (a + 1 : ℝ) * gaussMom a := by
  unfold gaussMom
  have he : Even (a + 2) ↔ Even a := by simp [Nat.even_add]
  simp only [he]
  split_ifs with h
  · rw [show a + 2 - 1 = a + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl
  · ring

private lemma lap1_raise (a c : ℕ) :
    lap1 (a + 2) (c + 1) = (a + 1 : ℝ) * lap1 a (c + 1) + lap1 (a + 1) c := by
  by_cases hc : a + 1 < c
  · rw [lap1_eq_zero (Or.inl (by omega)), lap1_eq_zero (Or.inl (by omega)),
      lap1_eq_zero (Or.inl hc)]
    ring
  by_cases he : Even (a + 1 - c)
  · obtain ⟨k, hk⟩ := he
    cases k with
    | zero =>
      have ha : c = a + 1 := by omega
      subst c
      rw [lap1_self, lap1_self, lap1_eq_zero (Or.inl (by omega))]
      ring
    | succ s =>
      have ha : a = c + 1 + 2 * s := by omega
      subst a
      rw [show c + 1 + 2 * s + 2 = (c + 1) + 2 * (s + 1) by omega,
        lap1_explicit, lap1_explicit,
        show c + 1 + 2 * s + 1 = c + 2 * (s + 1) by omega, lap1_explicit]
      rw [show c + 1 + 2 * (s + 1) = (c + 2 * (s + 1)) + 1 by omega,
        Nat.factorial_succ,
        show c + 2 * (s + 1) = (c + 1 + 2 * s) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ c, Nat.factorial_succ s, pow_succ]
      push_cast
      have hc0 : (c.factorial : ℝ) ≠ 0 := by positivity
      have hs0 : (s.factorial : ℝ) ≠ 0 := by positivity
      have hp0 : (2 : ℝ) ^ s ≠ 0 := by positivity
      have hc1 : (c + 1 : ℝ) ≠ 0 := by positivity
      have hs1 : (s + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  · have he' : ¬ Even (a + 2 - (c + 1)) := by
      simpa [show a + 2 - (c + 1) = a + 1 - c by omega] using he
    have he'' : a < c + 1 ∨ ¬ Even (a - (c + 1)) := by
      by_cases hh : a < c + 1
      · exact Or.inl hh
      · right
        intro hn
        apply he
        have hh' : a + 1 - c = (a - (c + 1)) + 2 := by omega
        rw [hh']
        exact hn.add (by decide : Even 2)
    rw [lap1_eq_zero (Or.inr he'), lap1_eq_zero he'', lap1_eq_zero (Or.inr he)]
    ring

private lemma sum_zero_right (a K : ℕ) :
    ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lap1 a c * lap1 0 c =
      gaussMom a := by
  rw [Finset.sum_eq_single 0]
  · simp [lap1_self, lap1_zero]
  · intro c hc hc0
    rw [lap1_eq_zero (a := 0) (c := c) (Or.inl (by omega))]
    ring
  · simp

private lemma sum_one_left (b K : ℕ) (hK : 1 ≤ K) :
    ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lap1 1 c * lap1 b c =
      gaussMom (1 + b) := by
  rw [Finset.sum_eq_single 1]
  · cases b with
    | zero => simp [lap1, gaussMom]
    | succ b =>
      have hl := lap1_lower b 0
      simp only [Nat.cast_zero, zero_add, one_mul, lap1_zero] at hl
      simp only [Nat.factorial_one, Nat.cast_one, lap1_self, one_mul]
      rw [hl]
      convert (mom_rec b).symm using 1
      congr 1
      omega
  · intro c hc hc1
    by_cases hc0 : c = 0
    · subst c
      norm_num [lap1, gaussMom]
    · rw [lap1_eq_zero (Or.inl (by omega))]
      ring
  · simp [Finset.mem_range, show 1 < K + 1 by omega]

private lemma sum_raise (a b L : ℕ) :
    (∑ c ∈ Finset.range (L + 2), (c.factorial : ℝ) * lap1 (a + 2) c * lap1 (b + 1) c) =
      (a + 1 : ℝ) *
        (∑ c ∈ Finset.range (L + 2), (c.factorial : ℝ) * lap1 a c * lap1 (b + 1) c) +
      (b + 1 : ℝ) *
        (∑ c ∈ Finset.range (L + 1), (c.factorial : ℝ) * lap1 (a + 1) c * lap1 b c) := by
  rw [show L + 2 = (L + 1) + 1 by omega]
  rw [Finset.sum_range_succ' (fun c => (c.factorial : ℝ) * lap1 (a + 2) c * lap1 (b + 1) c),
    Finset.sum_range_succ' (fun c => (c.factorial : ℝ) * lap1 a c * lap1 (b + 1) c)]
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, lap1_zero, mom_rec]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hs : (∑ k ∈ Finset.range (L + 1),
      ((k + 1).factorial : ℝ) * lap1 (a + 2) (k + 1) * lap1 (b + 1) (k + 1)) =
      ∑ k ∈ Finset.range (L + 1),
        ((a + 1 : ℝ) * ((k + 1).factorial : ℝ) * lap1 a (k + 1) * lap1 (b + 1) (k + 1) +
          (b + 1 : ℝ) * (k.factorial : ℝ) * lap1 (a + 1) k * lap1 b k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [lap1_raise, Nat.factorial_succ]
    push_cast
    have hl := lap1_lower b k
    calc
      _ = (a + 1 : ℝ) * ((k + 1) * (k.factorial : ℝ)) * lap1 a (k + 1) *
          lap1 (b + 1) (k + 1) +
          (k.factorial : ℝ) * lap1 (a + 1) k * ((k + 1) * lap1 (b + 1) (k + 1)) := by ring
      _ = _ := by rw [hl]; ring
  rw [hs]
  simp only [Finset.sum_add_distrib, mul_assoc]
  ring

private lemma hermite1_of_left_le (a b K : ℕ) (hK : a ≤ K) :
    ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lap1 a c * lap1 b c =
      gaussMom (a + b) := by
  induction a using Nat.twoStepInduction generalizing b K with
  | zero =>
    have hs := sum_zero_right b K
    simpa only [zero_add, mul_right_comm] using hs
  | one => exact sum_one_left b K hK
  | more a ih ih' =>
    cases b with
    | zero => simpa using sum_zero_right (a + 2) K
    | succ b =>
      cases K with
      | zero => omega
      | succ L =>
        rw [show L + 1 + 1 = L + 2 by omega, sum_raise,
          ih (b + 1) (L + 1) (by omega), ih' b L (by omega)]
        rw [show a + (b + 1) = a + 1 + b by omega]
        rw [show a + 2 + (b + 1) = (a + 1 + b) + 2 by omega, mom_rec]
        push_cast
        ring

theorem hermite1 (a b K : ℕ) (hK : min a b ≤ K) :
    ∑ c ∈ Finset.range (K + 1), (c.factorial : ℝ) * lap1 a c * lap1 b c = gaussMom (a + b) := by
  by_cases ha : a ≤ K
  · exact hermite1_of_left_le a b K ha
  · have hb : b ≤ K := by omega
    have hs := hermite1_of_left_le b a K hb
    simpa only [Nat.add_comm, mul_right_comm] using hs

end BstLean.Part36

#print axioms BstLean.Part36.lap1_self
#print axioms BstLean.Part36.lap1_zero
#print axioms BstLean.Part36.lap1_eq_zero
#print axioms BstLean.Part36.hermite1
