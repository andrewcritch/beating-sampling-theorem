import BstLean.Part174End

/-!
# Part 174 (file `CapNum`): Part 171's numerical conditions with their slack kept

No proof is left open; no `native_decide` or `axiom` is used.

* `numF'`: `(n m)⁴(A₀ + A₁z₁ + A₂z₂)⁸ ≤ (270/n)⁸` (Part 171's `numF` stops at `0.004⁸`).
* `numW'`: `m⁸(A₀' + A₁'z₁ + A₂'z₂)⁸ ≤ (280/n)⁸` (Part 171's `numW` stops at `0.02⁸`).
-/

namespace BstLean.Part174.Cap

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part170 (tA)

variable {n : ℕ}

/-- **The location numerical condition** (`B_f = 0.004`). -/
theorem numF' (hn : 80000 ≤ n) :
    0 < AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) ∧
    0 < AF1 √(SminN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) ∧
    0 < AF2 √(SminN n) (DmN n) ∧
    ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 *
      (AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) +
        AF1 √(SminN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AF2 √(SminN n) (DmN n) * (754 / 100)) ^ 8 ≤ (270 / (n : ℝ)) ^ 8 := by
  obtain ⟨hr, hr2, hsm, -, htA, hstA, hO, hD, hV⟩ := r_facts hn
  obtain ⟨h5a, h5b, h2a, h2b⟩ := sqrt_consts
  obtain ⟨hφ0, hφ0', hφ1, hφ1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set r := √(n : ℝ)
  have hr0 : 0 < r := by linarith
  have hs5 : (0 : ℝ) < √5 := by positivity
  have hs2 : (0 : ℝ) < √2 := by positivity
  have h52 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the coefficients in terms of r
  have eΓ : tA n * O1n n ^ 2 + SmaxN n = 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 := by
    rw [htA, hO]; unfold SmaxN; rw [← hr2]; rw [mul_pow, h22]; ring
  have eC : √(tA n) * O1n n = 2 * (r + 2) / r ^ 2 := by
    rw [hstA, hO]; field_simp; rw [h22]
  have eD : DmN n = 16 / r ^ 6 := by unfold DmN; rw [← hr2]; ring
  have eV : VmN n = 64 / r ^ 8 := by unfold VmN; rw [← hr2]; ring
  have eP : PmN n = 1 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
  have hΓle : 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 ≤ 10 / r ^ 2 := by
    have h1 : 4 * (r + 2) ^ 2 / r ^ 4 ≤ 5 / r ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 4 * (r + 2) ^ 2 ≤ 5 * r ^ 2 := by nlinarith
      calc 4 * (r + 2) ^ 2 * r ^ 2 ≤ 5 * r ^ 2 * r ^ 2 := by gcongr
        _ = 5 * r ^ 4 := by ring
    have e : (10 : ℝ) / r ^ 2 = 5 / r ^ 2 + 5 / r ^ 2 := by ring
    linarith
  have hCle : 2 * (r + 2) / r ^ 2 ≤ 3 / r := by
    rw [div_le_div_iff₀ (by positivity) hr0]; nlinarith
  -- A₀
  have eA0 : AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) =
      8 * √5 * phiG 0 / r ^ 5 + 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 +
        3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 := by
    rw [← AF0_eq _ _ _ _ hs5.ne' hs2.ne' hr0.ne', ← eΓ]
    unfold AF0 AF0'; rw [hsm, eD, eV, eP]
  have eA1 : AF1 √(SminN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) =
      160 * phiG 1 / r ^ 5 + 4 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8 := by
    rw [← AF1_eq _ _ _ _ h52 hr0.ne', ← eC]
    unfold AF1 AF1'; rw [hsm, hD, hV, eP]
  have eA2 : AF2 √(SminN n) (DmN n) = 8 * √2 * √5 * phiG 0 / r ^ 5 := by
    rw [← AF2_eq _ _ _ hs5.ne' hr0.ne']
    unfold AF2 AF2'; rw [hsm, eD]
  rw [eA0, eA1, eA2]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  -- the bound r³·Q ≤ K/r²
  have b0 : 3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 ≤ 1 / r ^ 5 := by
    have h1 : 3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) ≤
        3 / 2 * √5 * phiG 0 * (10 / r ^ 2) := by gcongr
    have h2 : 3 / 2 * √5 * phiG 0 * (10 / r ^ 2) ≤ r ^ 2 := by
      rw [show 3 / 2 * √5 * phiG 0 * (10 / r ^ 2) = 15 * √5 * phiG 0 / r ^ 2 by ring,
        div_le_iff₀ (by positivity)]
      have hm0 := mul_le_mul h5b hφ0' hφ0.le (by norm_num)
      have hm : √5 * phiG 0 ≤ 1 := by linarith only [hm0]
      have hr4 : (282 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
      have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
      rw [e]
      have e2 : 15 * √5 * phiG 0 = 15 * (√5 * phiG 0) := by ring
      rw [e2]
      linarith only [hm, hr4]
    calc _ ≤ r ^ 2 / r ^ 7 := by gcongr; exact h1.trans h2
      _ = 1 / r ^ 5 := by field_simp
  have b1 : 4 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8 ≤ 1 / r ^ 5 := by
    have h1 : 4 * √2 * (2 * (r + 2) / r ^ 2) ≤ 4 * √2 * (3 / r) := by gcongr
    have h2 : 4 * √2 * (3 / r) ≤ r ^ 3 := by
      rw [show 4 * √2 * (3 / r) = 12 * √2 / r by ring, div_le_iff₀ hr0]
      have hr4 : (282 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
      have e : r ^ 3 * r = r ^ 4 := by ring
      rw [e]
      linarith only [hr4, h2b]
    calc _ ≤ r ^ 3 / r ^ 8 := by gcongr; exact h1.trans h2
      _ = 1 / r ^ 5 := by field_simp
  have e53 : √5 ^ 3 / √2 = 5 * √5 / √2 := by rw [pow_succ, h52]
  have k53 : 5 * √5 / √2 ≤ 15812 / 10000 * 5 := by
    rw [div_le_iff₀ hs2]; linarith only [h5b, h2a]
  set Q := 8 * √5 * phiG 0 / r ^ 5 + 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 +
        3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 +
      (160 * phiG 1 / r ^ 5 + 4 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8) * (211 / 100) +
      8 * √2 * √5 * phiG 0 / r ^ 5 * (754 / 100) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQle : Q ≤ 27 / 100 / r ^ 5 * 1000 := by
    have t1 : 8 * √5 * phiG 0 ≤ 8 * (22361 / 10000) * (39895 / 100000) := by gcongr
    have t2 : 32 * √5 ^ 3 / √2 * phiG 0 ≤ 32 * (15812 / 10000 * 5) * (39895 / 100000) := by
      rw [show 32 * √5 ^ 3 / √2 * phiG 0 = 32 * (√5 ^ 3 / √2) * phiG 0 by ring, e53]
      gcongr
    have t3 : 160 * phiG 1 ≤ 160 * (24198 / 100000) := by gcongr
    have t4 : 8 * √2 * √5 * phiG 0 ≤ 8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) := by
      gcongr
    have hr5 : 0 < r ^ 5 := by positivity
    have : Q ≤ (8 * (22361 / 10000) * (39895 / 100000) + 32 * (15812 / 10000 * 5) * (39895 / 100000) +
        1 + (160 * (24198 / 100000) + 1) * (211 / 100) +
        8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) * (754 / 100)) / r ^ 5 := by
      rw [hQ]
      have a1 : 8 * √5 * phiG 0 / r ^ 5 ≤ 8 * (22361 / 10000) * (39895 / 100000) / r ^ 5 := by gcongr
      have a2 : 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 ≤
          32 * (15812 / 10000 * 5) * (39895 / 100000) / r ^ 5 := by gcongr
      have a3 : 160 * phiG 1 / r ^ 5 ≤ 160 * (24198 / 100000) / r ^ 5 := by gcongr
      have a4 : 8 * √2 * √5 * phiG 0 / r ^ 5 ≤
          8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 5 := by gcongr
      have e : (8 * (22361 / 10000) * (39895 / 100000) + 32 * (15812 / 10000 * 5) * (39895 / 100000) +
          1 + (160 * (24198 / 100000) + 1) * (211 / 100) +
          8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) * (754 / 100)) / r ^ 5 =
          8 * (22361 / 10000) * (39895 / 100000) / r ^ 5 +
            32 * (15812 / 10000 * 5) * (39895 / 100000) / r ^ 5 + 1 / r ^ 5 +
            (160 * (24198 / 100000) / r ^ 5 + 1 / r ^ 5) * (211 / 100) +
            8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 5 * (754 / 100) := by
        ring
      rw [e]
      linarith [b0, b1, a1, a2, a3, a4]
    refine this.trans ?_
    rw [show (27 : ℝ) / 100 / r ^ 5 * 1000 = 270 / r ^ 5 by ring]
    gcongr
    norm_num
  -- (n m)⁴ Q⁸ = (r³Q)⁸ and r³Q ≤ 270/r² ≤ 0.004
  clear_value Q
  have hnm : (n : ℝ) * ((mA n : ℕ) : ℝ) = r ^ 6 := by rw [hmA, ← hr2]; ring
  rw [hnm, show (r ^ 6) ^ 4 * Q ^ 8 = (r ^ 3 * Q) ^ 8 by ring]
  refine pow_le_pow_left₀ (by positivity) ?_ 8
  calc r ^ 3 * Q ≤ r ^ 3 * (27 / 100 / r ^ 5 * 1000) := by gcongr
    _ = 270 / r ^ 2 := by field_simp; ring
    _ = 270 / (n : ℝ) := by rw [hr2]

/-- **The energy numerical condition** (`B_ω = 0.02`). -/
theorem numW' (hn : 80000 ≤ n) :
    0 < AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) ∧
    0 < AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) ∧
    0 < AW2 (DmN n) (PmN n) (√(tA n) * O1n n) ∧
    ((mA n : ℕ) : ℝ) ^ 8 *
      (AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) +
        AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AW2 (DmN n) (PmN n) (√(tA n) * O1n n) * (754 / 100)) ^ 8 ≤ (280 / (n : ℝ)) ^ 8 := by
  obtain ⟨hr, hr2, hsm, hsp, htA, hstA, hO, hD, hV⟩ := r_facts hn
  obtain ⟨h5a, h5b, h2a, h2b⟩ := sqrt_consts
  obtain ⟨hφ0, hφ0', hφ1, hφ1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set r := √(n : ℝ)
  have hr0 : 0 < r := by linarith
  have hs5 : (0 : ℝ) < √5 := by positivity
  have hs2 : (0 : ℝ) < √2 := by positivity
  have h52 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have eΓ : tA n * O1n n ^ 2 + SmaxN n = 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 := by
    rw [htA, hO]; unfold SmaxN; rw [← hr2]; rw [mul_pow, h22]; ring
  have eC : √(tA n) * O1n n = 2 * (r + 2) / r ^ 2 := by
    rw [hstA, hO]; field_simp; rw [h22]
  have eD : DmN n = 16 / r ^ 6 := by unfold DmN; rw [← hr2]; ring
  have eV : VmN n = 64 / r ^ 8 := by unfold VmN; rw [← hr2]; ring
  have eP : PmN n = 1 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
  have hΓle : 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 ≤ 10 / r ^ 2 := by
    have h1 : 4 * (r + 2) ^ 2 / r ^ 4 ≤ 5 / r ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 4 * (r + 2) ^ 2 ≤ 5 * r ^ 2 := by nlinarith
      calc 4 * (r + 2) ^ 2 * r ^ 2 ≤ 5 * r ^ 2 * r ^ 2 := by gcongr
        _ = 5 * r ^ 4 := by ring
    have e : (10 : ℝ) / r ^ 2 = 5 / r ^ 2 + 5 / r ^ 2 := by ring
    linarith
  have hCle : 2 * (r + 2) / r ^ 2 ≤ 3 / r := by
    rw [div_le_div_iff₀ (by positivity) hr0]; nlinarith
  set Γ := 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 with hΓd
  set C := 2 * (r + 2) / r ^ 2 with hCd
  have hΓ0 : 0 ≤ Γ := by positivity
  have hC0 : 0 ≤ C := by positivity
  have eA0 : AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) =
      (16 + 160 * phiG 1) / r ^ 6 + 4 * Γ / r ^ 8 := by
    rw [← AW0_eq _ _ _ h52 hr0.ne', eΓ]
    unfold AW0 AW0'; rw [hsm, eD, eV, eP]
  have eA1 : AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) =
      32 * √2 * √5 * phiG 0 / r ^ 6 + 4 * √2 * √5 * C / r ^ 9 := by
    rw [← AW1_eq _ _ _ _ hs5.ne' hr0.ne', eC]
    unfold AW1 AW1'; rw [hsm, hsp, hD, hV, eP]
  have eA2 : AW2 (DmN n) (PmN n) (√(tA n) * O1n n) = 16 / r ^ 6 + 1 / r ^ 8 * (28 * C ^ 2) := by
    unfold AW2; rw [eD, eP, eC]
  rw [eA0, eA1, eA2]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  have hr4 : (282 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
  have b0 : 4 * Γ / r ^ 8 ≤ 1 / r ^ 6 := by
    have : 4 * Γ ≤ r ^ 2 := by
      have e40 : (40 : ℝ) / r ^ 2 = 4 * (10 / r ^ 2) := by ring
      have h1 : 4 * Γ ≤ 40 / r ^ 2 := by rw [e40]; linarith only [hΓle]
      have h2 : 40 / r ^ 2 ≤ r ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 4 * Γ / r ^ 8 ≤ r ^ 2 / r ^ 8 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have b1 : 4 * √2 * √5 * C / r ^ 9 ≤ 1 / r ^ 6 := by
    have h0 : √2 * √5 ≤ 4 := by nlinarith only [h2b, h5b, hs2, hs5]
    have : 4 * √2 * √5 * C ≤ r ^ 3 := by
      have h1 : 4 * √2 * √5 * C ≤ 4 * 4 * (3 / r) := by
        rw [show 4 * √2 * √5 * C = 4 * (√2 * √5) * C by ring]; gcongr
      have h2 : 4 * 4 * (3 / r) ≤ r ^ 3 := by
        rw [show 4 * 4 * (3 / r) = 48 / r by ring, div_le_iff₀ hr0]
        have e : r ^ 3 * r = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 4 * √2 * √5 * C / r ^ 9 ≤ r ^ 3 / r ^ 9 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have b2 : 1 / r ^ 8 * (28 * C ^ 2) ≤ 1 / r ^ 6 := by
    have hC2 : C ^ 2 ≤ (3 / r) ^ 2 := pow_le_pow_left₀ hC0 hCle 2
    have : 28 * C ^ 2 ≤ r ^ 2 := by
      have h2 : 28 * (3 / r) ^ 2 ≤ r ^ 2 := by
        rw [div_pow, show 28 * (3 ^ 2 / r ^ 2) = 252 / r ^ 2 by ring, div_le_iff₀ (by positivity)]
        have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 1 / r ^ 8 * (28 * C ^ 2) ≤ 1 / r ^ 8 * r ^ 2 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have t3 : 160 * phiG 1 ≤ 160 * (24198 / 100000) := by gcongr
  have t4 : 32 * √2 * √5 * phiG 0 ≤ 32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) := by
    gcongr
  have hr6 : 0 < r ^ 6 := by positivity
  set Q := (16 + 160 * phiG 1) / r ^ 6 + 4 * Γ / r ^ 8 +
      (32 * √2 * √5 * phiG 0 / r ^ 6 + 4 * √2 * √5 * C / r ^ 9) * (211 / 100) +
      (16 / r ^ 6 + 1 / r ^ 8 * (28 * C ^ 2)) * (754 / 100) with hQ
  have hQle : Q ≤ 280 / r ^ 6 := by
    have a0 : (16 + 160 * phiG 1) / r ^ 6 ≤ (16 + 160 * (24198 / 100000)) / r ^ 6 := by gcongr
    have a1 : 32 * √2 * √5 * phiG 0 / r ^ 6 ≤
        32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 := by gcongr
    have hsum : (16 + 160 * (24198 / 100000)) / r ^ 6 + 1 / r ^ 6 +
        (32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 + 1 / r ^ 6) * (211 / 100) +
        (16 / r ^ 6 + 1 / r ^ 6) * (754 / 100) ≤ 280 / r ^ 6 := by
      rw [show (16 + 160 * (24198 / 100000)) / r ^ 6 + 1 / r ^ 6 +
        (32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 + 1 / r ^ 6) * (211 / 100) +
        (16 / r ^ 6 + 1 / r ^ 6) * (754 / 100) = ((16 + 160 * (24198 / 100000)) + 1 +
        (32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) + 1) * (211 / 100) +
        (16 + 1) * (754 / 100)) / r ^ 6 by ring]
      gcongr
      norm_num
    rw [hQ]
    linarith [a0, a1, b0, b1, b2, hsum]
  have hQ0 : 0 ≤ Q := by rw [hQ, hΓd, hCd]; positivity
  clear_value Q
  rw [hmA, ← hr2, show ((r ^ 2) ^ 2) ^ 8 * Q ^ 8 = (r ^ 4 * Q) ^ 8 by ring]
  refine pow_le_pow_left₀ (by positivity) ?_ 8
  calc r ^ 4 * Q ≤ r ^ 4 * (280 / r ^ 6) := by gcongr
    _ = 280 / r ^ 2 := by field_simp

end BstLean.Part174.Cap
