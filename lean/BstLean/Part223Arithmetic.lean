import BstLean.Part223Log

/-! Exact integer certificates for the order256 tail coefficient. -/
namespace BstLean.Part223

lemma gaussian_factorial_lower : (8 : ℕ) ^ 256 ≤ 2 ^ 128 * (128 : ℕ).factorial := by
  norm_num [Nat.factorial]

lemma factorial256_lower : (64 : ℕ) ^ 256 ≤ (256 : ℕ).factorial := by
  norm_num [Nat.factorial]

#print axioms gaussian_factorial_lower
#print axioms factorial256_lower
end BstLean.Part223
