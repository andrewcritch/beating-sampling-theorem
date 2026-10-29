import BstLean.Part189WorldConstants

/-! Part 189: the arithmetic allowance for latitude generation and binary search. -/

namespace BstLean.Part189

def searchIterations (n : ℕ) : ℕ := Nat.clog 2 (gridNodes n)
def searchPrice (n : ℕ) : ℕ := 10 * searchIterations n + 10

theorem searchIterations_le {n : ℕ} (hn : 8000 ≤ n) : searchIterations n ≤ n / 20 := by
  have h := world_length_test hn
  have hsmall : (512 * n) ^ 2 ≤ 4 * 10 ^ 23 * n ^ 2 := by nlinarith
  have he : (4 : ℕ) ^ (n / 20) = (2 ^ (n / 20)) ^ 2 := by
    rw [← pow_mul, mul_comm (n / 20) 2, pow_mul]
    norm_num
  have hsq : (512 * n) ^ 2 ≤ (2 ^ (n / 20)) ^ 2 := by
    rw [← he]
    exact le_trans hsmall h
  have hroot : 512 * n ≤ 2 ^ (n / 20) :=
    (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr hroot

theorem searchPrice_le {n : ℕ} (hn : 8000 ≤ n) : searchPrice n ≤ 5 * n + 70 := by
  have h := searchIterations_le hn
  unfold searchPrice
  omega

/-- Square and sum n-1 transverse coordinates, then form and clip the latitude. -/
def latitudeCount (n : ℕ) : ℕ := (n - 1) + (n - 2) + 9
/-- Form the mixture scalars and the three-operation affine value in each coordinate. -/
def conversionCount (n : ℕ) : ℕ := 3 * n + 12
def drawExtraCount (n : ℕ) : ℕ := latitudeCount n + searchPrice n + conversionCount n

theorem latitudeCount_le (n : ℕ) : latitudeCount n ≤ 2 * n + 10 := by
  unfold latitudeCount
  omega
theorem conversionCount_le (n : ℕ) : conversionCount n ≤ 3 * n + 20 := by
  unfold conversionCount
  omega
theorem drawExtraCount_le {n : ℕ} (hn : 8000 ≤ n) : drawExtraCount n ≤ 10 * n + 100 := by
  have hL := latitudeCount_le n
  have hS := searchPrice_le hn
  have hC := conversionCount_le n
  unfold drawExtraCount
  omega

end BstLean.Part189
