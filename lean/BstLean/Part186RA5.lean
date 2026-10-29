import BstLean.Part186RA4

/-!
# Part 186 (file `RA5`): the scaling inequalities of the row-averaged bias moments

No proof is left open; no `native_decide` or `axiom` is used.

With `y = 1/√n ≤ 1/128`, `N y² = 1` (`N = n`), `M y⁴ = 1` (`M = m = n²`):

* **`finalF`**: if `0 ≤ K ≤ K̄y¹⁰`, `0 ≤ μ ≤ μ̄y¹⁰` and a numerical condition at `y = 1/128`, then
  `N⁴((1 + ε)³(Mμ)⁴ + (1 + 1/ε)³(M₈/(2t) + t/2)) ≤ (B̄/N)⁸` with `t = T y³²`;
* **`finalW`**: if `0 ≤ K ≤ K̄y⁶`, `0 ≤ μ ≤ μ̄y⁶` and a numerical condition, then
  `(1 + ε)⁷(Mμ)⁸ + (1 + 1/ε)⁷M₈ ≤ (B̄/N)⁸`.
-/

namespace BstLean.Part186.RA

open Real

/-- The constant `s_k` of `S_k ≤ s_k y^{…}`. -/
noncomputable def sk (Kb μb E : ℝ) (k : ℕ) : ℝ := Kb ^ k * (2 ^ (2 * k - 1) * (1 + E)) + μb ^ k

lemma Sb_scale {m : ℕ} {y K μ Kb μb E : ℝ} (_hy : 0 ≤ y) (hm : (m : ℝ) * y ^ 4 = 1)
    (hK0 : 0 ≤ K) (hK : K ≤ Kb * y ^ a) (hμ0 : 0 ≤ μ) (hμ : μ ≤ μb * y ^ a) (hE : 0 ≤ E)
    (k : ℕ) {e : ℕ} (he : a * k = e + 4) :
    Sb m K μ E k ≤ sk Kb μb E k * y ^ e := by
  unfold Sb sk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : K ^ k ≤ (Kb * y ^ a) ^ k := pow_le_pow_left₀ hK0 hK k
  have h2 : μ ^ k ≤ (μb * y ^ a) ^ k := pow_le_pow_left₀ hμ0 hμ k
  calc (m : ℝ) * (K ^ k * (2 ^ (2 * k - 1) * (1 + E)) + μ ^ k)
      ≤ (m : ℝ) * ((Kb * y ^ a) ^ k * (2 ^ (2 * k - 1) * (1 + E)) + (μb * y ^ a) ^ k) := by
        gcongr
    _ = (Kb ^ k * (2 ^ (2 * k - 1) * (1 + E)) + μb ^ k) * y ^ e * ((m : ℝ) * y ^ 4) := by
        rw [mul_pow, mul_pow, ← pow_mul, he, pow_add]; ring
    _ = _ := by rw [hm, mul_one]


/-- **The location scaling inequality.** -/
theorem finalF {m : ℕ} {N y K μ Kb μb ε T Bb : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 128)
    (hN : N * y ^ 2 = 1) (hm : (m : ℝ) * y ^ 4 = 1)
    (hK0 : 0 ≤ K) (hK : K ≤ Kb * y ^ 10) (hμ0 : 0 ≤ μ) (hμ : μ ≤ μb * y ^ 10)
    (hε : 0 < ε) (hT : 0 < T) (hBb : 0 ≤ Bb)
    (hnum : (1 + ε) ^ 3 * μb ^ 4 + (1 + 1 / ε) ^ 3 *
      ((105 * sk Kb μb 384 2 ^ 4 * (1 / 128) ^ 8 +
        490 * sk Kb μb 384 2 ^ 2 * sk Kb μb 10321920 4 * (1 / 128) ^ 12 +
        (63 * sk Kb μb 10321920 4 ^ 2 + 56 * sk Kb μb 384 2 * sk Kb μb 1961990553600 6) *
          (1 / 128) ^ 16 + sk Kb μb 1371195958099968000 8 * (1 / 128) ^ 20) / (2 * T) +
        T * (1 / 128) ^ 8 / 2) ≤ Bb ^ 8) :
    N ^ 4 * ((1 + ε) ^ 3 * ((m : ℝ) * μ) ^ 4 +
      (1 + 1 / ε) ^ 3 * (M8 m K μ / (2 * (T * y ^ 32)) + T * y ^ 32 / 2)) ≤ (Bb / N) ^ 8 := by
  have hKb : 0 ≤ Kb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 10); linarith
  have hμb : 0 ≤ μb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 10); linarith
  have s2 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 384) 2 (e := 16) (by norm_num)
  have s4 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 10321920) 4 (e := 36)
    (by norm_num)
  have s6 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1961990553600) 6 (e := 56)
    (by norm_num)
  have s8 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1371195958099968000) 8
    (e := 76) (by norm_num)
  set S2 := sk Kb μb 384 2
  set S4 := sk Kb μb 10321920 4
  set S6 := sk Kb μb 1961990553600 6
  set S8 := sk Kb μb 1371195958099968000 8
  have hS2 : 0 ≤ S2 := by unfold S2 sk; positivity
  have hS4 : 0 ≤ S4 := by unfold S4 sk; positivity
  have hS6 : 0 ≤ S6 := by unfold S6 sk; positivity
  have hS8 : 0 ≤ S8 := by unfold S8 sk; positivity
  have q2 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 384) 2
  have q4 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 10321920) 4
  have q6 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 1961990553600) 6
  have hM8 : M8 m K μ ≤ 105 * (S2 * y ^ 16) ^ 4 + 490 * (S2 * y ^ 16) ^ 2 * (S4 * y ^ 36) +
      63 * (S4 * y ^ 36) ^ 2 + 56 * (S2 * y ^ 16) * (S6 * y ^ 56) + S8 * y ^ 76 := by
    unfold M8; gcongr
  have hMμ : (m : ℝ) * μ ≤ μb * y ^ 6 := by
    calc (m : ℝ) * μ ≤ (m : ℝ) * (μb * y ^ 10) := by gcongr
      _ = μb * y ^ 6 * ((m : ℝ) * y ^ 4) := by ring
      _ = μb * y ^ 6 := by rw [hm, mul_one]
  have hMμ0 : 0 ≤ (m : ℝ) * μ := by positivity
  have hy' : 0 ≤ y := hy0.le
  have hp : ∀ k : ℕ, y ^ k ≤ (1 / 128) ^ k := fun k => pow_le_pow_left₀ hy' hy k
  have hNe : N = 1 / y ^ 2 := by field_simp; linarith
  have hc1 : 0 ≤ (1 + ε) ^ 3 := by positivity
  have hc2 : 0 ≤ (1 + 1 / ε) ^ 3 := by positivity
  -- the bracket
  have key : (1 + ε) ^ 3 * ((m : ℝ) * μ) ^ 4 +
      (1 + 1 / ε) ^ 3 * (M8 m K μ / (2 * (T * y ^ 32)) + T * y ^ 32 / 2) ≤
      y ^ 24 * ((1 + ε) ^ 3 * μb ^ 4 + (1 + 1 / ε) ^ 3 *
        ((105 * S2 ^ 4 * y ^ 8 + 490 * S2 ^ 2 * S4 * y ^ 12 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 16 +
          S8 * y ^ 20) / (2 * T) + T * y ^ 8 / 2)) := by
    have a1 : ((m : ℝ) * μ) ^ 4 ≤ (μb * y ^ 6) ^ 4 := pow_le_pow_left₀ hMμ0 hMμ 4
    have a2 : M8 m K μ / (2 * (T * y ^ 32)) ≤ (105 * (S2 * y ^ 16) ^ 4 +
        490 * (S2 * y ^ 16) ^ 2 * (S4 * y ^ 36) + 63 * (S4 * y ^ 36) ^ 2 +
        56 * (S2 * y ^ 16) * (S6 * y ^ 56) + S8 * y ^ 76) / (2 * (T * y ^ 32)) := by
      gcongr
    calc _ ≤ (1 + ε) ^ 3 * (μb * y ^ 6) ^ 4 + (1 + 1 / ε) ^ 3 * ((105 * (S2 * y ^ 16) ^ 4 +
          490 * (S2 * y ^ 16) ^ 2 * (S4 * y ^ 36) + 63 * (S4 * y ^ 36) ^ 2 +
          56 * (S2 * y ^ 16) * (S6 * y ^ 56) + S8 * y ^ 76) / (2 * (T * y ^ 32)) +
          T * y ^ 32 / 2) := by gcongr
      _ = _ := by field_simp; ring
  have key2 : (1 + ε) ^ 3 * μb ^ 4 + (1 + 1 / ε) ^ 3 *
        ((105 * S2 ^ 4 * y ^ 8 + 490 * S2 ^ 2 * S4 * y ^ 12 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 16 +
          S8 * y ^ 20) / (2 * T) + T * y ^ 8 / 2) ≤ Bb ^ 8 := by
    refine le_trans ?_ hnum
    have := hp 8; have := hp 12; have := hp 16; have := hp 20
    gcongr
  rw [hNe]
  calc (1 / y ^ 2) ^ 4 * ((1 + ε) ^ 3 * ((m : ℝ) * μ) ^ 4 +
        (1 + 1 / ε) ^ 3 * (M8 m K μ / (2 * (T * y ^ 32)) + T * y ^ 32 / 2))
      ≤ (1 / y ^ 2) ^ 4 * (y ^ 24 * Bb ^ 8) := by
        gcongr; exact key.trans (mul_le_mul_of_nonneg_left key2 (by positivity))
    _ = (Bb / (1 / y ^ 2)) ^ 8 := by field_simp

/-- **The energy scaling inequality.** -/
theorem finalW {m : ℕ} {N y K μ Kb μb ε Bb : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 128)
    (hN : N * y ^ 2 = 1) (hm : (m : ℝ) * y ^ 4 = 1)
    (hK0 : 0 ≤ K) (hK : K ≤ Kb * y ^ 6) (hμ0 : 0 ≤ μ) (hμ : μ ≤ μb * y ^ 6)
    (hε : 0 < ε) (hBb : 0 ≤ Bb)
    (hnum : (1 + ε) ^ 7 * μb ^ 8 + (1 + 1 / ε) ^ 7 *
      (105 * sk Kb μb 384 2 ^ 4 * (1 / 128) ^ 16 +
        490 * sk Kb μb 384 2 ^ 2 * sk Kb μb 10321920 4 * (1 / 128) ^ 20 +
        (63 * sk Kb μb 10321920 4 ^ 2 + 56 * sk Kb μb 384 2 * sk Kb μb 1961990553600 6) *
          (1 / 128) ^ 24 + sk Kb μb 1371195958099968000 8 * (1 / 128) ^ 28) ≤ Bb ^ 8) :
    (1 + ε) ^ 7 * ((m : ℝ) * μ) ^ 8 + (1 + 1 / ε) ^ 7 * M8 m K μ ≤ (Bb / N) ^ 8 := by
  have hKb : 0 ≤ Kb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 6); linarith
  have hμb : 0 ≤ μb := by
    by_contra h; push Not at h; have := mul_neg_of_neg_of_pos h (pow_pos hy0 6); linarith
  have s2 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 384) 2 (e := 8) (by norm_num)
  have s4 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 10321920) 4 (e := 20)
    (by norm_num)
  have s6 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1961990553600) 6 (e := 32)
    (by norm_num)
  have s8 := Sb_scale hy0.le hm hK0 hK hμ0 hμ (by norm_num : (0 : ℝ) ≤ 1371195958099968000) 8
    (e := 44) (by norm_num)
  set S2 := sk Kb μb 384 2
  set S4 := sk Kb μb 10321920 4
  set S6 := sk Kb μb 1961990553600 6
  set S8 := sk Kb μb 1371195958099968000 8
  have hS2 : 0 ≤ S2 := by unfold S2 sk; positivity
  have hS4 : 0 ≤ S4 := by unfold S4 sk; positivity
  have hS6 : 0 ≤ S6 := by unfold S6 sk; positivity
  have hS8 : 0 ≤ S8 := by unfold S8 sk; positivity
  have q2 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 384) 2
  have q4 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 10321920) 4
  have q6 := Sb_nonneg (m := m) hK0 hμ0 (by norm_num : (0 : ℝ) ≤ 1961990553600) 6
  have hM8 : M8 m K μ ≤ 105 * (S2 * y ^ 8) ^ 4 + 490 * (S2 * y ^ 8) ^ 2 * (S4 * y ^ 20) +
      63 * (S4 * y ^ 20) ^ 2 + 56 * (S2 * y ^ 8) * (S6 * y ^ 32) + S8 * y ^ 44 := by
    unfold M8; gcongr
  have hMμ : (m : ℝ) * μ ≤ μb * y ^ 2 := by
    calc (m : ℝ) * μ ≤ (m : ℝ) * (μb * y ^ 6) := by gcongr
      _ = μb * y ^ 2 * ((m : ℝ) * y ^ 4) := by ring
      _ = μb * y ^ 2 := by rw [hm, mul_one]
  have hMμ0 : 0 ≤ (m : ℝ) * μ := by positivity
  have hy' : 0 ≤ y := hy0.le
  have hp : ∀ k : ℕ, y ^ k ≤ (1 / 128) ^ k := fun k => pow_le_pow_left₀ hy' hy k
  have hNe : N = 1 / y ^ 2 := by field_simp; linarith
  have a1 : ((m : ℝ) * μ) ^ 8 ≤ (μb * y ^ 2) ^ 8 := pow_le_pow_left₀ hMμ0 hMμ 8
  have key : (1 + ε) ^ 7 * ((m : ℝ) * μ) ^ 8 + (1 + 1 / ε) ^ 7 * M8 m K μ ≤
      y ^ 16 * ((1 + ε) ^ 7 * μb ^ 8 + (1 + 1 / ε) ^ 7 *
        (105 * S2 ^ 4 * y ^ 16 + 490 * S2 ^ 2 * S4 * y ^ 20 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 24 +
          S8 * y ^ 28)) := by
    calc _ ≤ (1 + ε) ^ 7 * (μb * y ^ 2) ^ 8 + (1 + 1 / ε) ^ 7 * (105 * (S2 * y ^ 8) ^ 4 +
          490 * (S2 * y ^ 8) ^ 2 * (S4 * y ^ 20) + 63 * (S4 * y ^ 20) ^ 2 +
          56 * (S2 * y ^ 8) * (S6 * y ^ 32) + S8 * y ^ 44) := by gcongr
      _ = _ := by ring
  have key2 : (1 + ε) ^ 7 * μb ^ 8 + (1 + 1 / ε) ^ 7 *
        (105 * S2 ^ 4 * y ^ 16 + 490 * S2 ^ 2 * S4 * y ^ 20 + (63 * S4 ^ 2 + 56 * S2 * S6) * y ^ 24 +
          S8 * y ^ 28) ≤ Bb ^ 8 := by
    refine le_trans ?_ hnum
    have := hp 16; have := hp 20; have := hp 24; have := hp 28
    gcongr
  rw [hNe]
  calc _ ≤ y ^ 16 * Bb ^ 8 := key.trans (mul_le_mul_of_nonneg_left key2 (by positivity))
    _ = (Bb / (1 / y ^ 2)) ^ 8 := by field_simp

end BstLean.Part186.RA
