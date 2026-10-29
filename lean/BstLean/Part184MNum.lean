import BstLean.Part174All

/-!
# Part 184 (file `MNum`): the bias numerics. `numF21`: `≤ (0.01543)⁸` (`270/17 500`); `numW21`: `≤ (0.016)⁸`, `P_m = 61·PmN n`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the Part 184 `L` chain (floor 17 750) for every `n ≥ 17 500` (statistics cap `n ≤ 17 750`),
namespaces `….J175` / `BstLean.Part184.M`. The constants above are those of the Lean statements; the
docstrings of copied lemmas can carry older numbers, and the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part170 (tA)

variable {n : ℕ}

lemma r_facts21 (hn : 17500 ≤ n) :
    13228 / 100 ≤ √(n : ℝ) ∧ √(n : ℝ) ^ 2 = n ∧
    √(SminN n) = 1 / (√5 * √(n : ℝ)) ∧ √(SmaxN n) = √5 / √(n : ℝ) ∧
    tA n = 2 / √(n : ℝ) ^ 4 ∧ √(tA n) = √2 / √(n : ℝ) ^ 2 ∧
    O1n n = √2 * (√(n : ℝ) + 2) ∧ √(DmN n) = 4 / √(n : ℝ) ^ 3 ∧ √(VmN n) = 8 / √(n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr : 13228 / 100 ≤ r := by
    rw [hrd, Real.le_sqrt (by norm_num) hn0.le]
    have : (17500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  refine ⟨hr, hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SminN
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
  · unfold SmaxN; rw [Real.sqrt_div' _ hn0.le]
  · unfold tA; rw [hmA, ← hr2]; ring
  · unfold tA
    rw [hmA, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hn0.le, ← hr2]
  · unfold O1n
    rw [Real.sqrt_div' _ hn0.le, ← hrd]
    field_simp
    linear_combination (-1 : ℝ) * hr2
  · unfold DmN
    rw [Real.sqrt_div' _ (by positivity), show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), ← hr2, show (r ^ 2) ^ 3 = (r ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  · unfold VmN
    rw [Real.sqrt_div' _ (by positivity), show (64 : ℝ) = 8 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), ← hr2, show (r ^ 2) ^ 4 = (r ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]

/-- The location numerical condition with its slack: `≤ (270/n)⁸`. -/
theorem numF21r (hn : 17500 ≤ n) :
    0 < AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) ∧
    0 < AF1 √(SminN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) ∧
    0 < AF2 √(SminN n) (DmN n) ∧
    ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 *
      (AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) +
        AF1 √(SminN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AF2 √(SminN n) (DmN n) * (754 / 100)) ^ 8 ≤ (270 / (n : ℝ)) ^ 8 := by
  obtain ⟨hr, hr2, hsm, -, htA, hstA, hO, hD, hV⟩ := r_facts21 hn
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
  have eP : 61 * PmN n = 61 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
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
  have eA0 : AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) =
      8 * √5 * phiG 0 / r ^ 5 + 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 +
        (183 / 2) * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 := by
    unfold AF0; rw [hsm, eD, eV, eP, eΓ]; field_simp; ring
  have eA1 : AF1 √(SminN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) =
      160 * phiG 1 / r ^ 5 + 244 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8 := by
    unfold AF1; rw [hsm, hD, hV, eP, eC]; field_simp; rw [h52]; ring
  have eA2 : AF2 √(SminN n) (DmN n) = 8 * √2 * √5 * phiG 0 / r ^ 5 := by
    rw [← AF2_eq _ _ _ hs5.ne' hr0.ne']
    unfold AF2 AF2'; rw [hsm, eD]
  rw [eA0, eA1, eA2]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  -- the bound r³·Q ≤ K/r²
  have b0 : (183 / 2) * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 ≤ 1 / r ^ 5 := by
    have h1 : (183 / 2) * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) ≤
        (183 / 2) * √5 * phiG 0 * (10 / r ^ 2) := by gcongr
    have h2 : (183 / 2) * √5 * phiG 0 * (10 / r ^ 2) ≤ r ^ 2 := by
      rw [show (183 / 2) * √5 * phiG 0 * (10 / r ^ 2) = 915 * √5 * phiG 0 / r ^ 2 by ring,
        div_le_iff₀ (by positivity)]
      have hm0 := mul_le_mul h5b hφ0' hφ0.le (by norm_num)
      have hm : √5 * phiG 0 ≤ 1 := by linarith only [hm0]
      have hr4 : (13228 / 100 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
      have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
      rw [e]
      have e2 : 915 * √5 * phiG 0 = 915 * (√5 * phiG 0) := by ring
      rw [e2]
      linarith only [hm, hr4]
    calc _ ≤ r ^ 2 / r ^ 7 := by gcongr; exact h1.trans h2
      _ = 1 / r ^ 5 := by field_simp
  have b1 : 244 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8 ≤ 1 / r ^ 5 := by
    have h1 : 244 * √2 * (2 * (r + 2) / r ^ 2) ≤ 244 * √2 * (3 / r) := by gcongr
    have h2 : 244 * √2 * (3 / r) ≤ r ^ 3 := by
      rw [show 244 * √2 * (3 / r) = 732 * √2 / r by ring, div_le_iff₀ hr0]
      have hr4 : (13228 / 100 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
      have e : r ^ 3 * r = r ^ 4 := by ring
      rw [e]
      linarith only [hr4, h2b]
    calc _ ≤ r ^ 3 / r ^ 8 := by gcongr; exact h1.trans h2
      _ = 1 / r ^ 5 := by field_simp
  have e53 : √5 ^ 3 / √2 = 5 * √5 / √2 := by rw [pow_succ, h52]
  have k53 : 5 * √5 / √2 ≤ 15812 / 10000 * 5 := by
    rw [div_le_iff₀ hs2]; linarith only [h5b, h2a]
  set Q := 8 * √5 * phiG 0 / r ^ 5 + 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 +
        (183 / 2) * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 +
      (160 * phiG 1 / r ^ 5 + 244 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8) * (211 / 100) +
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

/-- The energy numerical condition with its slack: `≤ (280/n)⁸`. -/
theorem numW21r (hn : 17500 ≤ n) :
    0 < AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) ∧
    0 < AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) ∧
    0 < AW2 (DmN n) (61 * PmN n) (√(tA n) * O1n n) ∧
    ((mA n : ℕ) : ℝ) ^ 8 *
      (AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) +
        AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AW2 (DmN n) (61 * PmN n) (√(tA n) * O1n n) * (754 / 100)) ^ 8 ≤ (280 / (n : ℝ)) ^ 8 := by
  obtain ⟨hr, hr2, hsm, hsp, htA, hstA, hO, hD, hV⟩ := r_facts21 hn
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
  have eP : 61 * PmN n = 61 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
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
  have eA0 : AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) =
      (16 + 160 * phiG 1) / r ^ 6 + 244 * Γ / r ^ 8 := by
    unfold AW0; rw [hsm, eD, eV, eP, eΓ]; field_simp; rw [h52]; ring
  have eA1 : AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) =
      32 * √2 * √5 * phiG 0 / r ^ 6 + 244 * √2 * √5 * C / r ^ 9 := by
    unfold AW1; rw [hsm, hsp, hD, hV, eP, eC]; field_simp; ring
  have eA2 : AW2 (DmN n) (61 * PmN n) (√(tA n) * O1n n) = 16 / r ^ 6 + 1 / r ^ 8 * (1708 * C ^ 2) := by
    unfold AW2; rw [eD, eP, eC]; ring
  rw [eA0, eA1, eA2]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  have hr4 : (13228 / 100 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
  have b0 : 244 * Γ / r ^ 8 ≤ 1 / r ^ 6 := by
    have : 244 * Γ ≤ r ^ 2 := by
      have e40 : (2440 : ℝ) / r ^ 2 = 244 * (10 / r ^ 2) := by ring
      have h1 : 244 * Γ ≤ 2440 / r ^ 2 := by rw [e40]; linarith only [hΓle]
      have h2 : 2440 / r ^ 2 ≤ r ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 244 * Γ / r ^ 8 ≤ r ^ 2 / r ^ 8 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have b1 : 244 * √2 * √5 * C / r ^ 9 ≤ 1 / r ^ 6 := by
    have h0 : √2 * √5 ≤ 4 := by nlinarith only [h2b, h5b, hs2, hs5]
    have : 244 * √2 * √5 * C ≤ r ^ 3 := by
      have h1 : 244 * √2 * √5 * C ≤ 244 * 4 * (3 / r) := by
        rw [show 244 * √2 * √5 * C = 244 * (√2 * √5) * C by ring]; gcongr
      have h2 : 244 * 4 * (3 / r) ≤ r ^ 3 := by
        rw [show 244 * 4 * (3 / r) = 2928 / r by ring, div_le_iff₀ hr0]
        have e : r ^ 3 * r = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 244 * √2 * √5 * C / r ^ 9 ≤ r ^ 3 / r ^ 9 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have b2 : 1 / r ^ 8 * (1708 * C ^ 2) ≤ 1 / r ^ 6 := by
    have hC2 : C ^ 2 ≤ (3 / r) ^ 2 := pow_le_pow_left₀ hC0 hCle 2
    have : 1708 * C ^ 2 ≤ r ^ 2 := by
      have h2 : 1708 * (3 / r) ^ 2 ≤ r ^ 2 := by
        rw [div_pow, show 1708 * (3 ^ 2 / r ^ 2) = 15372 / r ^ 2 by ring, div_le_iff₀ (by positivity)]
        have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 1 / r ^ 8 * (1708 * C ^ 2) ≤ 1 / r ^ 8 * r ^ 2 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have t3 : 160 * phiG 1 ≤ 160 * (24198 / 100000) := by gcongr
  have t4 : 32 * √2 * √5 * phiG 0 ≤ 32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) := by
    gcongr
  have hr6 : 0 < r ^ 6 := by positivity
  set Q := (16 + 160 * phiG 1) / r ^ 6 + 244 * Γ / r ^ 8 +
      (32 * √2 * √5 * phiG 0 / r ^ 6 + 244 * √2 * √5 * C / r ^ 9) * (211 / 100) +
      (16 / r ^ 6 + 1 / r ^ 8 * (1708 * C ^ 2)) * (754 / 100) with hQ
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


/-- **The location numerical condition at `n ≥ 36 000`, `P_m = 3/n⁴`** (`B_f = 0.0068`). -/
theorem numF21 (hn : 17500 ≤ n) :
    0 < AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) ∧
    0 < AF1 √(SminN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) ∧
    0 < AF2 √(SminN n) (DmN n) ∧
    ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 *
      (AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) +
        AF1 √(SminN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AF2 √(SminN n) (DmN n) * (754 / 100)) ^ 8 ≤ (1543 / 100000) ^ 8 := by
  obtain ⟨h0, h1, h2, h3⟩ := numF21r hn
  refine ⟨h0, h1, h2, h3.trans (pow_le_pow_left₀ (by positivity) ?_ 8)⟩
  have hnR : (17500 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by linarith)]; linarith

/-- **The energy numerical condition at `n ≥ 36 000`, `P_m = 3/n⁴`** (`B_ω = 0.007`). -/
theorem numW21 (hn : 17500 ≤ n) :
    0 < AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) ∧
    0 < AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) ∧
    0 < AW2 (DmN n) (61 * PmN n) (√(tA n) * O1n n) ∧
    ((mA n : ℕ) : ℝ) ^ 8 *
      (AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (61 * PmN n) +
        AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (61 * PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AW2 (DmN n) (61 * PmN n) (√(tA n) * O1n n) * (754 / 100)) ^ 8 ≤ (1600 / 100000) ^ 8 := by
  obtain ⟨h0, h1, h2, h3⟩ := numW21r hn
  refine ⟨h0, h1, h2, h3.trans (pow_le_pow_left₀ (by positivity) ?_ 8)⟩
  have hnR : (17500 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by linarith)]; linarith

end BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175

open BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175 in
#print axioms numF21
open BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175 in
#print axioms numW21
