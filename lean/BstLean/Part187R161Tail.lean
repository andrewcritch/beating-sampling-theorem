import BstLean.Part161Tail

/-! Part 187 (file `Part187R161Tail`): copy of `Part161Tail` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part161.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part157


/-- `poly_lower` of Part 161 with `m = 127 + e`. -/
lemma poly_lower127 {e d : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d) :
    (9229 / 10000 * (127 + e) + d - 6) ^ 2 * ((127 + e) ^ 2 + 89444 / 10000 * (127 + e) + 39) ≤
      (9229 / 10000 * (127 + e) + d - 63246 / 10000) ^ 2 *
        ((127 + e) ^ 2 + 12 * (9229 / 10000 * (127 + e) + d) - 36) := by
  nlinarith [mul_nonneg hd he, mul_nonneg hd hd, mul_nonneg he he,
    mul_nonneg (mul_nonneg hd hd) hd, mul_nonneg (mul_nonneg hd hd) he,
    mul_nonneg (mul_nonneg hd he) he, mul_nonneg (mul_nonneg he he) he]

/-- `det_core` of Part 161 with `m ≥ 127`. -/
lemma det_core127 {m A T Q : ℝ} (hm : 127 ≤ m) (hA : 9229 / 10000 * m ≤ A)
    (hTu : T ≤ A + 63246 / 10000) (hTl : A - 63246 / 10000 ≤ T)
    (hQl : m ^ 2 - 1 - 89444 / 10000 * m ≤ Q) (hQu : Q ≤ m ^ 2 + 89444 / 10000 * m + 39) :
    (A - 6) ^ 2 * (T ^ 2 + Q) ≤ T ^ 2 * (A ^ 2 + m ^ 2) ∧
      T ^ 2 * (A ^ 2 + m ^ 2) ≤ (A + 6) ^ 2 * (T ^ 2 + Q) := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ A = 9229 / 10000 * m + d :=
    ⟨A - 9229 / 10000 * m, by linarith, by ring⟩
  obtain ⟨e, he, rfl⟩ : ∃ e, 0 ≤ e ∧ m = 127 + e := ⟨m - 127, by linarith, by ring⟩
  have hAz : 0 ≤ 9229 / 10000 * (127 + e) + d - 63246 / 10000 := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hQ0 : 0 ≤ Q := by nlinarith
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hQu (sq_nonneg (9229 / 10000 * (127 + e) + d - 6))
    have h2 := poly_lower127 he hd
    have h3 : (9229 / 10000 * (127 + e) + d - 63246 / 10000) ^ 2 ≤ T ^ 2 :=
      pow_le_pow_left₀ hAz hTl 2
    have h4 : 0 ≤ (127 + e) ^ 2 + 12 * (9229 / 10000 * (127 + e) + d) - 36 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right h3 h4
    have h6 := h1.trans (h2.trans h5)
    have e1 : T ^ 2 * ((9229 / 10000 * (127 + e) + d) ^ 2 + (127 + e) ^ 2) -
        (9229 / 10000 * (127 + e) + d - 6) ^ 2 * (T ^ 2 + Q) =
        T ^ 2 * ((127 + e) ^ 2 + 12 * (9229 / 10000 * (127 + e) + d) - 36) -
          (9229 / 10000 * (127 + e) + d - 6) ^ 2 * Q := by ring
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hQl (sq_nonneg (9229 / 10000 * (127 + e) + d + 6))
    have h2 := poly_upper (by linarith : (0 : ℝ) ≤ 127 + e) hd
    have h3 : T ^ 2 ≤ (9229 / 10000 * (127 + e) + d + 63246 / 10000) ^ 2 :=
      pow_le_pow_left₀ hT0 hTu 2
    have e1 : (9229 / 10000 * (127 + e) + d + 6) ^ 2 * (T ^ 2 + Q) -
        T ^ 2 * ((9229 / 10000 * (127 + e) + d) ^ 2 + (127 + e) ^ 2) =
        (9229 / 10000 * (127 + e) + d + 6) ^ 2 * Q -
          T ^ 2 * ((127 + e) ^ 2 - 12 * (9229 / 10000 * (127 + e) + d) - 36) := by ring
    by_cases h4 : 0 ≤ (127 + e) ^ 2 - 12 * (9229 / 10000 * (127 + e) + d) - 36
    · have h5 := mul_le_mul_of_nonneg_right h3 h4
      have h6 := h5.trans (h2.trans h1)
      linarith
    · have h5 : T ^ 2 * ((127 + e) ^ 2 - 12 * (9229 / 10000 * (127 + e) + d) - 36) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (not_le.mp h4).le
      have h6 : 0 ≤ (9229 / 10000 * (127 + e) + d + 6) ^ 2 * Q :=
        mul_nonneg (sq_nonneg _) hQ0
      linarith

/-- **The deterministic part of Lemma `t7:p07:tails`.** For `n ≥ 16 384`, `a > 0`, `τ > 0` and
`0.46 ≤ θ ≤ 0.54` (`θ = n τ²/(a² + n τ²)`): if `|Z| ≤ √40` and
`n − 1 − 2√(20(n − 1)) ≤ Q ≤ n − 1 + 2√(20(n − 1)) + 40`, then
`(a + τ Z)/√((a + τ Z)² + τ² Q)` is in the bulk interval `[a/ρ − 6τ/ρ, a/ρ + 6τ/ρ]`. -/
theorem lat_det {n : ℕ} (hn : 16250 ≤ n) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ2 : n * τ ^ 2 ≤ 54 / 100 * (a ^ 2 + n * τ ^ 2)) {Z Q : ℝ} (hZ : |Z| ≤ √40)
    (hQ1 : (n : ℝ) - 1 - 2 * √(((n : ℝ) - 1) * 20) ≤ Q)
    (hQ2 : Q ≤ (n : ℝ) - 1 + 2 * √(((n : ℝ) - 1) * 20) + 40) :
    a / √(a ^ 2 + n * τ ^ 2) - 6 * τ / √(a ^ 2 + n * τ ^ 2) ≤
        (a + τ * Z) / √((a + τ * Z) ^ 2 + τ ^ 2 * Q) ∧
      (a + τ * Z) / √((a + τ * Z) ^ 2 + τ ^ 2 * Q) ≤
        a / √(a ^ 2 + n * τ ^ 2) + 6 * τ / √(a ^ 2 + n * τ ^ 2) := by
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨m, hm0, hm2⟩ : ∃ m : ℝ, 0 ≤ m ∧ m ^ 2 = n :=
    ⟨√(n : ℝ), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
  have hm128 : 127 ≤ m := by
    by_contra hc
    have : m ^ 2 < 127 ^ 2 := pow_lt_pow_left₀ (not_le.mp hc) hm0 two_ne_zero
    linarith
  have hs20 : √(((n : ℝ) - 1) * 20) ≤ 44722 / 10000 * m :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by rw [← hm2]; nlinarith⟩
  have hz : √(40 : ℝ) ≤ 63246 / 10000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  obtain ⟨A, hA0, rfl⟩ : ∃ A, 0 < A ∧ a = A * τ := ⟨a / τ, by positivity, by field_simp⟩
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hA2 : 46 / 100 * m ^ 2 ≤ 54 / 100 * A ^ 2 := by
    rw [hm2]
    have : τ ^ 2 * (46 / 100 * n) ≤ τ ^ 2 * (54 / 100 * A ^ 2) := by
      have e : (A * τ) ^ 2 = τ ^ 2 * A ^ 2 := by ring
      rw [e] at hθ2
      linarith
    exact le_of_mul_le_mul_left this hτ2
  have hA := window_A hm0 hA0 hA2
  obtain ⟨hZ1, hZ2⟩ := abs_le.mp hZ
  have hTu : A + Z ≤ A + 63246 / 10000 := by linarith
  have hTl : A - 63246 / 10000 ≤ A + Z := by linarith
  have hT0 : 0 < A + Z := by linarith
  have hQl : m ^ 2 - 1 - 89444 / 10000 * m ≤ Q := by rw [hm2]; linarith
  have hQu : Q ≤ m ^ 2 + 89444 / 10000 * m + 39 := by rw [hm2]; linarith
  have hQ0 : 0 < Q := by nlinarith
  obtain ⟨k1, k2⟩ := det_core127 hm128 hA hTu hTl hQl hQu
  have hM : 0 < (A * τ) ^ 2 + n * τ ^ 2 := by positivity
  have hx' : A * τ + τ * Z = τ * (A + Z) := by ring
  have hx : 0 ≤ A * τ + τ * Z := by rw [hx']; positivity
  have hN : 0 < (A * τ + τ * Z) ^ 2 + τ ^ 2 * Q := by positivity
  have hτ4 : 0 ≤ τ ^ 4 := by positivity
  have hA6 : 0 ≤ A * τ - 6 * τ := by
    have : A * τ - 6 * τ = τ * (A - 6) := by ring
    rw [this]
    exact mul_nonneg hτ.le (by linarith)
  constructor
  · rw [← sub_div]
    refine div_sqrt_le hA6 hx hM hN ?_
    have e1 : (A * τ - 6 * τ) ^ 2 * ((A * τ + τ * Z) ^ 2 + τ ^ 2 * Q) =
        τ ^ 4 * ((A - 6) ^ 2 * ((A + Z) ^ 2 + Q)) := by ring
    have e2 : (A * τ + τ * Z) ^ 2 * ((A * τ) ^ 2 + n * τ ^ 2) =
        τ ^ 4 * ((A + Z) ^ 2 * (A ^ 2 + m ^ 2)) := by rw [hm2]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left k1 hτ4
  · rw [← add_div]
    refine div_sqrt_le hx (by positivity) hN hM ?_
    have e1 : (A * τ + τ * Z) ^ 2 * ((A * τ) ^ 2 + n * τ ^ 2) =
        τ ^ 4 * ((A + Z) ^ 2 * (A ^ 2 + m ^ 2)) := by rw [hm2]; ring
    have e2 : (A * τ + 6 * τ) ^ 2 * ((A * τ + τ * Z) ^ 2 + τ ^ 2 * Q) =
        τ ^ 4 * ((A + 6) ^ 2 * ((A + Z) ^ 2 + Q)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left k2 hτ4

/-- **Lemma `t7:p07:tails` (the tail of the latitude).** For `n ≥ 16 384`, `a > 0`, `τ > 0` and
`0.46 ≤ θ ≤ 0.54` (`θ = n τ²/ρ²`, `ρ² = a² + n τ²`): the latitude `s = latitude a τ (Z, G)`,
`Z` standard Gaussian and `G` standard Gaussian in `ℝ^{n−1}`, is outside the bulk interval
`[a/ρ − 6τ/ρ, a/ρ + 6τ/ρ]` with probability at most `4·e^{−20}`. -/
theorem latitude_tail {n : ℕ} (hn : 16250 ≤ n) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ1 : 46 / 100 * (a ^ 2 + n * τ ^ 2) ≤ n * τ ^ 2)
    (hθ2 : n * τ ^ 2 ≤ 54 / 100 * (a ^ 2 + n * τ ^ 2)) :
    ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).real
      {p | latitude a τ p ∉ Set.Icc (a / √(a ^ 2 + n * τ ^ 2) - 6 * τ / √(a ^ 2 + n * τ ^ 2))
        (a / √(a ^ 2 + n * τ ^ 2) + 6 * τ / √(a ^ 2 + n * τ ^ 2))} ≤ 4 * exp (-20) := by
  refine (measureReal_mono ?_).trans (lat_event (n := n) (by omega))
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro h
  apply hp
  obtain ⟨hZ, hQ1, hQ2⟩ := h
  have := lat_det hn ha hτ hθ2 hZ hQ1.le hQ2.le
  exact ⟨this.1, this.2⟩

end BstLean.Part161.R

