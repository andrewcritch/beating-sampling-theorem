import BstLean.Part189Defs

/-!
Part 189: the odd rule has finite series lengths at most the dimension.
The integer tests are those of Part 01. Constants and loop bounds are free.
-/

namespace BstLean.Part189

lemma series_exists (b target : ℕ) (hb : 1 < b) :
    ∃ T : ℕ, 1 ≤ T ∧ target ≤ b ^ T := by
  obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt target hb
  refine ⟨T + 1, by omega, ?_⟩
  exact le_trans hT.le (pow_le_pow_right₀ (by omega : 1 ≤ b) (by omega))

def seriesLength (b target : ℕ) (hb : 1 < b) : ℕ := Nat.find (series_exists b target hb)

theorem seriesLength_spec (b target : ℕ) (hb : 1 < b) :
    1 ≤ seriesLength b target hb ∧ target ≤ b ^ seriesLength b target hb :=
  Nat.find_spec (series_exists b target hb)

def oddAsinLength (n : ℕ) : ℕ := seriesLength 4 (10 ^ 110 * n ^ 20) (by norm_num)
def oddPiLength (n : ℕ) : ℕ := seriesLength 25 (10 ^ 110 * n ^ 20) (by norm_num)

lemma odd_test_real {n : ℕ} (hn : 8000 ≤ n) :
    (10 : ℝ) ^ 110 * (n : ℝ) ^ 20 ≤ (4 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h : (10 : ℝ) ^ 110 * 8000 ^ 20 ≤ (4 : ℝ) ^ (400 : ℕ) := by
      rw [show (400 : ℕ) = 100 * 4 by norm_num, pow_mul]
      norm_num
    exact le_trans h (pow_le_pow_right₀ (by norm_num) (by norm_num))
  | succ n hn ih =>
    have hx : (100 : ℝ) ≤ n := by exact_mod_cast (by omega : 100 ≤ n)
    have hscale : (n : ℝ) + 1 ≤ (101 / 100 : ℝ) * n := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hscale 20
    calc (10 : ℝ) ^ 110 * ((n + 1 : ℕ) : ℝ) ^ 20
        ≤ (10 : ℝ) ^ 110 * ((101 / 100 : ℝ) * n) ^ 20 := by
          push_cast
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (101 / 100 : ℝ) ^ 20 * ((10 : ℝ) ^ 110 * (n : ℝ) ^ 20) := by ring
      _ ≤ 4 * ((10 : ℝ) ^ 110 * (n : ℝ) ^ 20) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 4 * (4 : ℝ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (4 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem odd_test {n : ℕ} (hn : 8000 ≤ n) : 10 ^ 110 * n ^ 20 ≤ 4 ^ n := by
  exact_mod_cast odd_test_real hn

theorem oddAsinLength_le {n : ℕ} (hn : 8000 ≤ n) : oddAsinLength n ≤ n := by
  exact Nat.find_min' (series_exists 4 (10 ^ 110 * n ^ 20) (by norm_num))
    ⟨by omega, odd_test hn⟩

theorem oddPiLength_le {n : ℕ} (hn : 8000 ≤ n) : oddPiLength n ≤ n := by
  apply Nat.find_min' (series_exists 25 (10 ^ 110 * n ^ 20) (by norm_num))
  exact ⟨by omega, le_trans (odd_test hn) (pow_le_pow_left₀ (by norm_num) (by norm_num) n)⟩

end BstLean.Part189
