import BstLean.Part107NumKap

/-!
# Part 107: the numeric bounds for every `n ≥ 4 096` (`Numeric107`)

Every piece of `J_*`, `v̄`, `a_L` is decreasing in `n`; each piece is bounded by its value at
`n = 4 096` (or by a rational number slightly above it).
-/

namespace BstLean.Part107

open BstLean.Part105

private lemma A_bd {x : ℝ} (hx : 4096 ≤ x) : 0 ≤ x / (x - 2) ∧ x / (x - 2) ≤ 4096 / 4094 := by
  have h2 : 0 < x - 2 := by linarith
  refine ⟨div_nonneg (by linarith) h2.le, ?_⟩
  rw [div_le_iff₀ h2]; linarith

private lemma p0_eq (n : ℕ) : p0 n = 10 ^ 16 * (2027025 /
    ((2 * (n : ℝ)) * (2 * n + 2) * (2 * n + 4) * (2 * n + 6) * (2 * n + 8) * (2 * n + 10) *
      (2 * n + 12) * (2 * n + 14))) := by
  have h16 : Even 16 := by decide
  have hg : BstLean.Part29.gaussMom 16 = 2027025 := by
    rw [BstLean.Part29.gaussMom, if_pos h16]
    norm_num [Nat.doubleFactorial]
  rw [p0, sphMom, if_pos h16, hg]
  congr 2
  simp only [BstLean.Part36.rhoD, Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

private lemma p0_bd (n : ℕ) (hn : 4096 ≤ n) :
    0 ≤ (n : ℝ) * p0 n ∧ (n : ℝ) * p0 n ≤ 41 / 10000000 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  rw [p0_eq]
  set x : ℝ := (n : ℝ)
  have hx0 : 0 < x := by linarith
  have hP : (2 * x) ^ 8 ≤ (2 * x) * (2 * x + 2) * (2 * x + 4) * (2 * x + 6) * (2 * x + 8) *
      (2 * x + 10) * (2 * x + 12) * (2 * x + 14) := by
    have : (2 * x) ^ 8 = (2 * x) * (2 * x) * (2 * x) * (2 * x) * (2 * x) * (2 * x) * (2 * x) *
      (2 * x) := by ring
    rw [this]
    gcongr <;> linarith
  set P := (2 * x) * (2 * x + 2) * (2 * x + 4) * (2 * x + 6) * (2 * x + 8) *
      (2 * x + 10) * (2 * x + 12) * (2 * x + 14)
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  refine ⟨by positivity, ?_⟩
  have e : x * (10 ^ 16 * (2027025 / P)) = (10 ^ 16 * 2027025 * x) / P := by ring
  rw [e, div_le_iff₀ hP0]
  have h7 : (4096 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx 7
  have h8 : (2 * x) ^ 8 = 256 * x ^ 7 * x := by ring
  have h9 : (256 * (4096 : ℝ) ^ 7) * x ≤ P := by
    rw [h8] at hP
    refine le_trans ?_ hP
    exact mul_le_mul_of_nonneg_right (by linarith) hx0.le
  have h10 : (10 : ℝ) ^ 16 * 2027025 ≤ 41 / 10000000 * (256 * (4096 : ℝ) ^ 7) := by norm_num
  calc 10 ^ 16 * 2027025 * x ≤ 41 / 10000000 * (256 * (4096 : ℝ) ^ 7) * x :=
        mul_le_mul_of_nonneg_right h10 hx0.le
    _ = 41 / 10000000 * ((256 * (4096 : ℝ) ^ 7) * x) := by ring
    _ ≤ 41 / 10000000 * P := mul_le_mul_of_nonneg_left h9 (by norm_num)

private lemma Jstar_eq (dA n : ℕ) : Jstar dA n =
    cKap dA * (2 + 2 * rPlus dA) * ((n : ℝ) / ((n : ℝ) - 2)) +
      (4 * LipK dA ^ 2 / (1 - rPlus dA ^ 2)) *
        (((n : ℝ) / ((n : ℝ) - 2)) * ((n : ℝ) * delN dA (2 * n))) +
      ((dA : ℝ) + 1) ^ 2 * ((n : ℝ) * p0 n) := by
  unfold Jstar Lsq; ring

/-- The bounds of `δ_r` at `N = 2n`, in the form `(3/(2x) + 3S/((2x)(2x+2)))/m²`. -/
private lemma del_bd {x S M : ℝ} (hx : 4096 ≤ x) (hS : 0 ≤ S) (hM : 0 < M) :
    0 ≤ (3 / (2 * x) + 3 * S / ((2 * x) * (2 * x + 2))) / M ∧
    (3 / (2 * x) + 3 * S / ((2 * x) * (2 * x + 2))) / M ≤
      (3 / (2 * 4096) + 3 * S / ((2 * 4096) * (2 * 4096 + 2))) / M ∧
    x * ((3 / (2 * x) + 3 * S / ((2 * x) * (2 * x + 2))) / M) ≤
      (3 / 2 + 3 * S / (2 * (2 * 4096 + 2))) / M := by
  have hx0 : 0 < x := by linarith
  refine ⟨by positivity, by gcongr, ?_⟩
  have e : x * ((3 / (2 * x) + 3 * S / ((2 * x) * (2 * x + 2))) / M) =
      (3 / 2 + 3 * S / (2 * (2 * x + 2))) / M := by
    field_simp
  rw [e]; gcongr

private lemma num3 (n : ℕ) (hn : 4096 ≤ n) :
    vbar 3 n < 4 ∧ 0 ≤ Jstar 3 n ∧ aL 3 n ≤ 105 / 10 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hrp : rPlus 3 = 1111111 / 7000000 := by norm_num [rPlus, rW, Finset.sum_range_succ]
  have hc : cKap 3 = 7697 / 1000 := by simp [cKap]
  have hL : LipK 3 = 6 := by norm_num [LipK]
  have hdel : delN 3 (2 * n) =
      (3 / (2 * (n : ℝ)) + 3 * 21 / ((2 * (n : ℝ)) * (2 * (n : ℝ) + 2))) / 49 := by
    simp only [delN, Sof, if_true]; push_cast; norm_num
  obtain ⟨hA0, hA⟩ := A_bd hx
  obtain ⟨hC0, hC⟩ := p0_bd n hn
  obtain ⟨hd0, hd1, hB⟩ := del_bd (S := 21) (M := 49) hx (by norm_num) (by norm_num)
  rw [← hdel] at hd0 hd1 hB
  have hB0 : 0 ≤ (n : ℝ) * delN 3 (2 * n) := mul_nonneg hx0.le hd0
  have h1 : 0 ≤ cKap 3 * (2 + 2 * rPlus 3) ∧ cKap 3 * (2 + 2 * rPlus 3) ≤ 17837492 / 1000000 := by
    rw [hc, hrp]; norm_num
  have h2 : 0 ≤ 4 * LipK 3 ^ 2 / (1 - rPlus 3 ^ 2) ∧
      4 * LipK 3 ^ 2 / (1 - rPlus 3 ^ 2) ≤ 147721892 / 1000000 := by
    rw [hL, hrp]; norm_num
  have hJeq := Jstar_eq 3 n
  have hJ0 : 0 ≤ Jstar 3 n := by
    rw [hJeq]
    have := mul_nonneg h1.1 hA0
    have := mul_nonneg h2.1 (mul_nonneg hA0 hB0)
    positivity
  have hJ : Jstar 3 n ≤ 895287 / 40000 := by
    rw [hJeq]; push_cast
    calc _ ≤ (17837492 / 1000000 : ℝ) * (4096 / 4094) +
          147721892 / 1000000 *
            ((4096 / 4094) * ((3 / 2 + 3 * 21 / (2 * (2 * 4096 + 2))) / 49)) +
          (3 + 1) ^ 2 * (41 / 10000000) := by
            have := h1.2; have := h2.2; have := h2.1; have := h1.1
            gcongr
      _ ≤ 895287 / 40000 := by norm_num
  have hE0 : 0 ≤ Ea2 3 n := by
    unfold Ea2; positivity
  have hE : Ea2 3 n ≤ 10574039 / 500000000 := by
    unfold Ea2; push_cast
    calc _ ≤ (1 : ℝ) / (2 * 3 + 1) ^ 2 + (3 / (2 * 4096) + 3 * 21 / ((2 * 4096) * (2 * 4096 + 2))) / 49
          + 3 / 4096 := by gcongr
      _ ≤ 10574039 / 500000000 := by norm_num
  have hs : Real.sqrt (Ea2 3 n) ≤ 14542379 / 100000000 := by
    rw [Real.sqrt_le_iff]; refine ⟨by norm_num, hE.trans (by norm_num)⟩
  have hv : vbar 3 n ≤ 29693 / 25000 := by
    unfold vbar; push_cast; linarith
  refine ⟨by linarith, hJ0, ?_⟩
  have hg : (70307 / 25000 : ℝ) ≤ ((3 : ℕ) : ℝ) + 1 - vbar 3 n := by push_cast; linarith
  unfold aL
  calc _ ≤ (2 : ℝ) + 3 * (895287 / 40000) * (1 + 2 / 4096) / (70307 / 25000 : ℝ) ^ 2 := by gcongr
    _ ≤ 105 / 10 := by norm_num

private lemma num4 (n : ℕ) (hn : 4096 ≤ n) :
    vbar 4 n < 5 ∧ 0 ≤ Jstar 4 n ∧ aL 4 n ≤ 107 / 10 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hrp : rPlus 4 = 111111111 / 900000000 := by norm_num [rPlus, rW, Finset.sum_range_succ]
  have hc : cKap 4 = 15532 / 1000 := by simp [cKap]
  have hL : LipK 4 = 10 := by norm_num [LipK]
  have hdel : delN 4 (2 * n) =
      (3 / (2 * (n : ℝ)) + 3 * 37 / ((2 * (n : ℝ)) * (2 * (n : ℝ) + 2))) / 81 := by
    simp only [delN, Sof]; push_cast; norm_num
  obtain ⟨hA0, hA⟩ := A_bd hx
  obtain ⟨hC0, hC⟩ := p0_bd n hn
  obtain ⟨hd0, hd1, hB⟩ := del_bd (S := 37) (M := 81) hx (by norm_num) (by norm_num)
  rw [← hdel] at hd0 hd1 hB
  have hB0 : 0 ≤ (n : ℝ) * delN 4 (2 * n) := mul_nonneg hx0.le hd0
  have h1 : 0 ≤ cKap 4 * (2 + 2 * rPlus 4) ∧ cKap 4 * (2 + 2 * rPlus 4) ≤ 34899062 / 1000000 := by
    rw [hc, hrp]; norm_num
  have h2 : 0 ≤ 4 * LipK 4 ^ 2 / (1 - rPlus 4 ^ 2) ∧
      4 * LipK 4 ^ 2 / (1 - rPlus 4 ^ 2) ≤ 406190993 / 1000000 := by
    rw [hL, hrp]; norm_num
  have hJeq := Jstar_eq 4 n
  have hJ0 : 0 ≤ Jstar 4 n := by
    rw [hJeq]
    have := mul_nonneg h1.1 hA0
    have := mul_nonneg h2.1 (mul_nonneg hA0 hB0)
    positivity
  have hJ : Jstar 4 n ≤ 21237963 / 500000 := by
    rw [hJeq]; push_cast
    calc _ ≤ (34899062 / 1000000 : ℝ) * (4096 / 4094) +
          406190993 / 1000000 *
            ((4096 / 4094) * ((3 / 2 + 3 * 37 / (2 * (2 * 4096 + 2))) / 81)) +
          (4 + 1) ^ 2 * (41 / 10000000) := by
            have := h1.2; have := h2.2; have := h2.1; have := h1.1
            gcongr
      _ ≤ 21237963 / 500000 := by norm_num
  have hE0 : 0 ≤ Ea2 4 n := by
    unfold Ea2; positivity
  have hE : Ea2 4 n ≤ 5233057 / 400000000 := by
    unfold Ea2; push_cast
    calc _ ≤ (1 : ℝ) / (2 * 4 + 1) ^ 2 + (3 / (2 * 4096) + 3 * 37 / ((2 * 4096) * (2 * 4096 + 2))) / 81
          + 3 / 4096 := by gcongr
      _ ≤ 5233057 / 400000000 := by norm_num
  have hs : Real.sqrt (Ea2 4 n) ≤ 5718969 / 50000000 := by
    rw [Real.sqrt_le_iff]; refine ⟨by norm_num, hE.trans (by norm_num)⟩
  have hv : vbar 4 n ≤ 5768137 / 5000000 := by
    unfold vbar; push_cast; linarith
  refine ⟨by linarith, hJ0, ?_⟩
  have hg : (19231863 / 5000000 : ℝ) ≤ ((4 : ℕ) : ℝ) + 1 - vbar 4 n := by push_cast; linarith
  unfold aL
  calc _ ≤ (2 : ℝ) + 3 * (21237963 / 500000) * (1 + 2 / 4096) / (19231863 / 5000000 : ℝ) ^ 2 := by
        gcongr
    _ ≤ 107 / 10 := by norm_num

/-- **The numeric bounds** for every `n ≥ 4 096`. -/
theorem numeric107 : Numeric107 := fun n hn => ⟨num3 n hn, num4 n hn⟩

end BstLean.Part107

#print axioms BstLean.Part107.kapFacts107
#print axioms BstLean.Part107.numeric107
