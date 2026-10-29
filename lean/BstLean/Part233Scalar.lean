import BstLean.Part233Concentration

/-! The cancellation exponent has the paper normalization. -/
namespace BstLean.Part233
open Real

theorem cancellation_variance_bound {Q H m N b ε : ℝ}
    (hQ : 0 ≤ Q) (hH : 0 ≤ H) (hm : 0 < m) (hN : 0 < N)
    (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (henergy : Q ≤ (1 + ε) * m / N) (hcentre : H ^ 2 ≤ b * Q) :
    ((√Q + H) / m) ^ 2 ≤ (1 + √b) ^ 2 * (1 + ε) / (m * N) := by
  have hHle : H ≤ √b * √Q := by
    have hs : (√b * √Q) ^ 2 = b * Q := by
      rw [mul_pow, Real.sq_sqrt hb, Real.sq_sqrt hQ]
    nlinarith [hs, mul_nonneg (sqrt_nonneg b) (sqrt_nonneg Q)]
  have hs : (√Q + H) ^ 2 ≤ ((1 + √b) * √Q) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  rw [mul_pow, Real.sq_sqrt hQ] at hs
  have he := mul_le_mul_of_nonneg_left henergy (sq_nonneg (1 + √b))
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
  calc (√Q + H) ^ 2 ≤ (1 + √b) ^ 2 * Q := hs
    _ ≤ (1 + √b) ^ 2 * ((1 + ε) * m / N) := he
    _ = (1 + √b) ^ 2 * (1 + ε) / (m * N) * m ^ 2 := by field_simp

theorem cancellation_exponent {m N K ε X μ : ℝ}
    (hN : 0 < N) (hX : 0 ≤ X) (hμ : 0 ≤ μ) :
    -((√2 * √X / N) - (√2 * √μ / N)) ^ 2 /
        (2 * (K * (1 + ε) / (m * N))) =
      -(m * (√X - √μ) ^ 2 / (K * (1 + ε) * N)) := by
  have htwo : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : √2 * √X / N - √2 * √μ / N = √2 * (√X - √μ) / N := by ring
  rw [he, div_pow, mul_pow, htwo]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hK : K = 0
  · simp [hK]
  by_cases hε : 1 + ε = 0
  · simp [hε]
  field_simp

end BstLean.Part233
#print axioms BstLean.Part233.cancellation_variance_bound
#print axioms BstLean.Part233.cancellation_exponent
