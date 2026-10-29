import BstLean.Part189Series

namespace BstLean.Part189

def worldPiLength (n : ℕ) : ℕ :=
  seriesLength 25 (4 * 10 ^ 23 * n ^ 2) (by norm_num)

lemma worldKappa_exists (n : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ 35500 * n ^ 2 * 1014 ^ T ≤ 10000 ^ T := by
  obtain ⟨T, hT1, hT⟩ := series_exists 4 (35500 * n ^ 2) (by norm_num)
  refine ⟨T, hT1, ?_⟩
  calc 35500 * n ^ 2 * 1014 ^ T ≤ 4 ^ T * 1014 ^ T := Nat.mul_le_mul_right _ hT
    _ = (4 * 1014) ^ T := by rw [mul_pow]
    _ ≤ 10000 ^ T := pow_le_pow_left₀ (by norm_num) (by norm_num) T

def worldKappaLength (n : ℕ) : ℕ := Nat.find (worldKappa_exists n)

theorem worldPiLength_spec (n : ℕ) :
    1 ≤ worldPiLength n ∧ 10 ^ 23 * (2 * n) ^ 2 ≤ 25 ^ worldPiLength n := by
  have h := seriesLength_spec 25 (4 * 10 ^ 23 * n ^ 2) (by norm_num)
  unfold worldPiLength
  have he : 10 ^ 23 * (2 * n) ^ 2 = 4 * 10 ^ 23 * n ^ 2 := by ring
  rw [he]
  exact h

theorem worldKappaLength_spec (n : ℕ) :
    1 ≤ worldKappaLength n ∧ 35500 * n ^ 2 * 1014 ^ worldKappaLength n ≤ 10000 ^ worldKappaLength n :=
  Nat.find_spec (worldKappa_exists n)

lemma world_block_test {k : ℕ} (hk : 400 ≤ k) :
    4 * 10 ^ 23 * (20 * (k + 1)) ^ 2 ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h : 4 * 10 ^ 23 * (20 * (400 + 1)) ^ 2 ≤ (4 : ℕ) ^ 100 := by norm_num
    exact le_trans h (pow_le_pow_right₀ (by norm_num) (by norm_num))
  | succ k hk ih =>
    have h : (20 * (k + 1 + 1)) ^ 2 ≤ 4 * (20 * (k + 1)) ^ 2 := by nlinarith
    calc 4 * 10 ^ 23 * (20 * (k + 1 + 1)) ^ 2
        ≤ 4 * 10 ^ 23 * (4 * (20 * (k + 1)) ^ 2) := Nat.mul_le_mul_left _ h
      _ = 4 * (4 * 10 ^ 23 * (20 * (k + 1)) ^ 2) := by ring
      _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left _ ih
      _ = 4 ^ (k + 1) := by rw [pow_succ]; ring

lemma world_length_test {n : ℕ} (hn : 8000 ≤ n) : 4 * 10 ^ 23 * n ^ 2 ≤ 4 ^ (n / 20) := by
  have hk : 400 ≤ n / 20 := by omega
  have hb : n ≤ 20 * (n / 20 + 1) := by omega
  exact le_trans (Nat.mul_le_mul_left _ (pow_le_pow_left₀ (Nat.zero_le n) hb 2)) (world_block_test hk)

theorem worldPiLength_le {n : ℕ} (hn : 8000 ≤ n) : worldPiLength n ≤ n / 20 := by
  apply Nat.find_min' (series_exists 25 (4 * 10 ^ 23 * n ^ 2) (by norm_num))
  exact ⟨by omega, le_trans (world_length_test hn) (pow_le_pow_left₀ (by norm_num) (by norm_num) _)⟩

theorem worldKappaLength_le {n : ℕ} (hn : 8000 ≤ n) : worldKappaLength n ≤ n / 20 := by
  apply Nat.find_min' (worldKappa_exists n)
  refine ⟨by omega, ?_⟩
  have hsmall : 35500 * n ^ 2 ≤ 4 * 10 ^ 23 * n ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
  have h := le_trans hsmall (world_length_test hn)
  calc 35500 * n ^ 2 * 1014 ^ (n / 20) ≤ 4 ^ (n / 20) * 1014 ^ (n / 20) := Nat.mul_le_mul_right _ h
    _ = (4 * 1014) ^ (n / 20) := by rw [mul_pow]
    _ ≤ 10000 ^ (n / 20) := pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Count the product, both Machin sums, the inverse-sine sum, and 20 scalar operations. -/
def worldConstantCount (n : ℕ) : ℕ :=
  (n - 1) + 6 * worldPiLength n + 4 * worldKappaLength n + 20

theorem worldConstantCount_le {n : ℕ} (hn : 8000 ≤ n) : worldConstantCount n ≤ 2 * n := by
  have hpi := worldPiLength_le hn
  have hk := worldKappaLength_le hn
  unfold worldConstantCount
  omega

end BstLean.Part189
