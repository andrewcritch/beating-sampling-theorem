import BstLean.Part186RA3

/-!
# Part 186 (file `RA4`): the row coefficients at the chain thresholds, every `n ≥ 16 384`

No proof is left open; no `native_decide` or `axiom` is used.

Thresholds `S₋ = 1/(5n)`, `S₊ = 5/n`, `D_m = H_m = 16/n³`, `V_m = 64/n⁴`, any `0 ≤ P_m ≤ 80/n⁴`,
`O = O₁(n)`; `r = √n ≥ 128`:

* `coefF`: `0 ≤ A₀ ≤ 108.08/r⁵`, `0 ≤ A₁ ≤ 38.73/r⁵`, `0 ≤ A₂ ≤ 10.094/r⁵` (location);
* `coefW`: `0 ≤ A₀' ≤ 54.73/r⁶`, `0 ≤ A₁' ≤ 40.38/r⁶`, `0 ≤ A₂' ≤ 16.01/r⁶` (energy).
-/

namespace BstLean.Part186.RA

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (tA)
open BstLean.Part153 (phiG phiG_pos)

variable {n : ℕ}

lemma r_facts16 (hn : 16384 ≤ n) :
    128 ≤ √(n : ℝ) ∧ √(n : ℝ) ^ 2 = n ∧
    √(SminN n) = 1 / (√5 * √(n : ℝ)) ∧ √(SmaxN n) = √5 / √(n : ℝ) ∧
    tA n = 2 / √(n : ℝ) ^ 4 ∧ √(tA n) = √2 / √(n : ℝ) ^ 2 ∧
    O1n n = √2 * (√(n : ℝ) + 2) ∧ √(DmN n) = 4 / √(n : ℝ) ^ 3 ∧ √(VmN n) = 8 / √(n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr : 128 ≤ r := by
    rw [hrd, Real.le_sqrt (by norm_num) hn0.le]
    have : (16384 : ℝ) ≤ n := by exact_mod_cast hn
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

lemma small_div {r X : ℝ} (hr : 0 < r) (hr4 : (128 : ℝ) ^ 4 ≤ r ^ 4) (_hX0 : 0 ≤ X)
    (hX : X ≤ 268435) (k : ℕ) : X / r ^ (k + 4) ≤ 1 / 1000 / r ^ k := by
  have hk : 0 < r ^ k := by positivity
  rw [div_le_div_iff₀ (by positivity) hk, pow_add]
  have h1 : X * 1000 ≤ r ^ 4 := by linarith
  have h2 : X * r ^ k * 1000 ≤ r ^ k * r ^ 4 := by nlinarith
  linarith

/-- **The location row coefficients.** -/
theorem coefF (hn : 16384 ≤ n) {Pm : ℝ} (hP0 : 0 ≤ Pm) (hP : Pm ≤ 80 * PmN n) :
    0 ≤ AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) Pm ∧
    AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) Pm ≤ 10808 / 100 / √(n : ℝ) ^ 5 ∧
    0 ≤ AF1 √(SminN n) (DmN n) (VmN n) Pm (√(tA n) * O1n n) ∧
    AF1 √(SminN n) (DmN n) (VmN n) Pm (√(tA n) * O1n n) ≤ 3873 / 100 / √(n : ℝ) ^ 5 ∧
    0 ≤ AF2 √(SminN n) (DmN n) ∧ AF2 √(SminN n) (DmN n) ≤ 10094 / 1000 / √(n : ℝ) ^ 5 := by
  obtain ⟨hr, hr2, hsm, -, htA, hstA, hO, hD, hV⟩ := r_facts16 hn
  obtain ⟨h5a, h5b, h2a, h2b⟩ := sqrt_consts
  obtain ⟨hφ0, hφ0', hφ1, hφ1'⟩ := BstLean.Part154.phiG_bounds_NumA
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
  have eP : 80 * PmN n = 80 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
  rw [eP] at hP
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
  have hr4 : (128 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
  have eA0 : AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) Pm =
      8 * √5 * phiG 0 / r ^ 5 + 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 +
        Pm * (3 / 2 * phiG 0 * (√5 * r) * Γ) := by
    unfold AF0; rw [hsm, eD, eV, eΓ]; field_simp; ring
  have eA1 : AF1 √(SminN n) (DmN n) (VmN n) Pm (√(tA n) * O1n n) =
      160 * phiG 1 / r ^ 5 + Pm * (4 * √2 * C) := by
    unfold AF1; rw [hsm, hD, hV, eC]; field_simp; rw [h52]; ring
  have eA2 : AF2 √(SminN n) (DmN n) = 8 * √2 * √5 * phiG 0 / r ^ 5 := by
    rw [← AF2_eq _ _ _ hs5.ne' hr0.ne']
    unfold AF2 AF2'; rw [hsm, eD]
  rw [eA0, eA1, eA2]
  -- the `P_m` terms
  have b0 : Pm * (3 / 2 * phiG 0 * (√5 * r) * Γ) ≤ 1 / 1000 / r ^ 5 := by
    have h1 : Pm * (3 / 2 * phiG 0 * (√5 * r) * Γ) ≤ 80 / r ^ 8 * (3 / 2 * (39895 / 100000) *
        ((22361 / 10000) * r) * (10 / r ^ 2)) := by
      gcongr
    refine h1.trans (le_of_eq_of_le ?_ (?_ : 80 * (3 / 2 * (39895 / 100000) *
        (22361 / 10000) * 10) / r ^ 9 ≤ 1 / 1000 / r ^ 5))
    · field_simp
    · exact small_div hr0 hr4 (by norm_num) (by norm_num) 5
  have b1 : Pm * (4 * √2 * C) ≤ 1 / 1000 / r ^ 5 := by
    have h1 : Pm * (4 * √2 * C) ≤ 80 / r ^ 8 * (4 * (14143 / 10000) * (3 / r)) := by gcongr
    refine h1.trans (le_of_eq_of_le ?_ (?_ : 80 * (4 * (14143 / 10000) * 3) / r ^ 9 ≤
        1 / 1000 / r ^ 5))
    · field_simp
    · exact small_div hr0 hr4 (by norm_num) (by norm_num) 5
  have e53 : √5 ^ 3 / √2 = 5 * √5 / √2 := by rw [pow_succ, h52]
  have k53 : 5 * √5 / √2 ≤ 15812 / 10000 * 5 := by
    rw [div_le_iff₀ hs2]; nlinarith only [h5b, h2a]
  have hr5 : 0 < r ^ 5 := by positivity
  have t1 : 8 * √5 * phiG 0 / r ^ 5 ≤ 8 * (22361 / 10000) * (39895 / 100000) / r ^ 5 := by
    gcongr
  have t2 : 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 ≤ 32 * (15812 / 10000 * 5) * (39895 / 100000) / r ^ 5 := by
    rw [show 32 * √5 ^ 3 / √2 * phiG 0 = 32 * (√5 ^ 3 / √2) * phiG 0 by ring, e53]
    gcongr
  have t3 : 160 * phiG 1 / r ^ 5 ≤ 160 * (24198 / 100000) / r ^ 5 := by gcongr
  have t4 : 8 * √2 * √5 * phiG 0 / r ^ 5 ≤
      8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 5 := by gcongr
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_⟩
  · have e : (10808 : ℝ) / 100 / r ^ 5 = 10807 / 100 / r ^ 5 + 1 / 100 / r ^ 5 := by ring
    have e2 : 8 * (22361 / 10000) * (39895 / 100000) / r ^ 5 +
        32 * (15812 / 10000 * 5) * (39895 / 100000) / r ^ 5 ≤ 10807 / 100 / r ^ 5 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hr5.le
    have e3 : (1 : ℝ) / 1000 / r ^ 5 ≤ 1 / 100 / r ^ 5 := by gcongr; norm_num
    linarith
  · have e2 : 160 * (24198 / 100000) / r ^ 5 + 1 / 1000 / r ^ 5 ≤ 3873 / 100 / r ^ 5 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hr5.le
    linarith
  · refine t4.trans ?_; gcongr; norm_num

/-- **The energy row coefficients.** -/
theorem coefW (hn : 16384 ≤ n) {Pm : ℝ} (hP0 : 0 ≤ Pm) (hP : Pm ≤ 80 * PmN n) :
    0 ≤ AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) Pm ∧
    AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) Pm ≤ 5473 / 100 / √(n : ℝ) ^ 6 ∧
    0 ≤ AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) Pm (√(tA n) * O1n n) ∧
    AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) Pm (√(tA n) * O1n n) ≤ 4038 / 100 / √(n : ℝ) ^ 6 ∧
    0 ≤ AW2 (DmN n) Pm (√(tA n) * O1n n) ∧
    AW2 (DmN n) Pm (√(tA n) * O1n n) ≤ 1601 / 100 / √(n : ℝ) ^ 6 := by
  obtain ⟨hr, hr2, hsm, hsp, htA, hstA, hO, hD, hV⟩ := r_facts16 hn
  obtain ⟨h5a, h5b, h2a, h2b⟩ := sqrt_consts
  obtain ⟨hφ0, hφ0', hφ1, hφ1'⟩ := BstLean.Part154.phiG_bounds_NumA
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
  have eP : 80 * PmN n = 80 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
  rw [eP] at hP
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
  have hr4 : (128 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
  have hr6 : 0 < r ^ 6 := by positivity
  have eA0 : AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) Pm =
      (16 + 160 * phiG 1) / r ^ 6 + Pm * (4 * Γ) := by
    unfold AW0; rw [hsm, eD, eV, eΓ]; field_simp; rw [h52]; ring
  have eA1 : AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) Pm (√(tA n) * O1n n) =
      32 * √2 * √5 * phiG 0 / r ^ 6 + Pm * (4 * √2 * C * (√5 / r)) := by
    unfold AW1; rw [hsm, hsp, hD, hV, eC]; field_simp; ring
  have eA2 : AW2 (DmN n) Pm (√(tA n) * O1n n) = 16 / r ^ 6 + Pm * (28 * C ^ 2) := by
    unfold AW2; rw [eD, eC]
  rw [eA0, eA1, eA2]
  have b0 : Pm * (4 * Γ) ≤ 1 / 1000 / r ^ 6 := by
    have h1 : Pm * (4 * Γ) ≤ 80 / r ^ 8 * (4 * (10 / r ^ 2)) := by gcongr
    refine h1.trans (le_of_eq_of_le ?_ (?_ : 3200 / r ^ 10 ≤ 1 / 1000 / r ^ 6))
    · field_simp; ring
    · exact small_div hr0 hr4 (by norm_num) (by norm_num) 6
  have b1 : Pm * (4 * √2 * C * (√5 / r)) ≤ 1 / 1000 / r ^ 6 := by
    have h1 : Pm * (4 * √2 * C * (√5 / r)) ≤
        80 / r ^ 8 * (4 * (14143 / 10000) * (3 / r) * ((22361 / 10000) / r)) := by gcongr
    refine h1.trans (le_of_eq_of_le ?_ (?_ : 80 * (4 * (14143 / 10000) * 3 * (22361 / 10000)) /
        r ^ 10 ≤ 1 / 1000 / r ^ 6))
    · field_simp
    · exact small_div hr0 hr4 (by norm_num) (by norm_num) 6
  have b2 : Pm * (28 * C ^ 2) ≤ 1 / 1000 / r ^ 6 := by
    have hC2 : C ^ 2 ≤ (3 / r) ^ 2 := pow_le_pow_left₀ hC0 hCle 2
    have h1 : Pm * (28 * C ^ 2) ≤ 80 / r ^ 8 * (28 * (3 / r) ^ 2) := by gcongr
    refine h1.trans (le_of_eq_of_le ?_ (?_ : 20160 / r ^ 10 ≤ 1 / 1000 / r ^ 6))
    · field_simp; ring
    · exact small_div hr0 hr4 (by norm_num) (by norm_num) 6
  have t3 : (16 + 160 * phiG 1) / r ^ 6 ≤ (16 + 160 * (24198 / 100000)) / r ^ 6 := by gcongr
  have t4 : 32 * √2 * √5 * phiG 0 / r ^ 6 ≤
      32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 := by gcongr
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_⟩
  · have e2 : (16 + 160 * (24198 / 100000)) / r ^ 6 + 1 / 1000 / r ^ 6 ≤ 5473 / 100 / r ^ 6 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hr6.le
    linarith
  · have e2 : 32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 +
        1 / 1000 / r ^ 6 ≤ 4038 / 100 / r ^ 6 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hr6.le
    linarith
  · have e2 : 16 / r ^ 6 + 1 / 1000 / r ^ 6 ≤ 1601 / 100 / r ^ 6 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hr6.le
    linarith

end BstLean.Part186.RA
