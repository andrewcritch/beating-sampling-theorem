import BstLean.Part90Arith

/-!
# Part 90: the numeric conditions of the assembly at `(3, 3)` for `n ≥ 1.5 · 10⁸`

Parameters: `η = 11`, `ω = 1/10`, `ζ = 720/√m`, `Mk = 6000`, `a = 1/200`, `b = 7/125`,
`β = 1/(600 n)`, `ξ = 1/500`, `ϑ = 1/20000`, `c_H = 456/100`, `c_T = 2604/100`,
`ε₁ = 4211/500`, `ε₂ = 3/5`, `ε₄ = 77/1000`, `ε₃ = 81/50`.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part90

open BstLean.Part86 BstLean.Part89 BstLean.Part88

/-- The threshold. -/
def N90 : ℕ := 150000000

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem arith3 (m : ℕ) (hn : N90 ≤ m + 1) :
    Num3 m (2 / 3 * (CLs 3 / (m : ℝ))) (1 / 20000) (1 / 200) (7 / 125)
      (1 / (600 * ((m + 1 : ℕ) : ℝ))) (1 / 500) ∧
    g3 m (2 / 3 * (CLs 3 / (m : ℝ)))
        (Xc (2 / 3 * (CLs 3 / (m : ℝ))) 27 ((87 / 100) ^ 3) (456 / 100) (2604 / 100)
          (4211 / 500) (3 / 5) (77 / 1000) (81 / 50) 11 (1 / 10)
          (720 * (1 / Real.sqrt (m : ℝ))))
        (1 / 20000) (1 / 200) (7 / 125) (1 / (600 * ((m + 1 : ℕ) : ℝ))) (1 / 500) +
      (400 / ((m + 1 : ℕ) : ℝ) + 2 / 6000) + 100 / ((m + 1 : ℕ) : ℝ) +
      20808 / DWr (m + 1) (JR (m + 1) 3) ≤ 1 / 100 := by
  unfold N90 at hn
  have h100 : 100 ≤ m + 1 := by omega
  have h5000 : 5000 ≤ m := by omega
  have hNW := DWr3_ge (m + 1) h100
  obtain ⟨ht0, ht1, ht2⟩ := tS3 (m + 1) (by omega)
  have hNr : (150000000 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hmN : (m : ℝ) = ((m + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have hCL : CLs 3 = 101 / 100 * 24 := by
    unfold CLs; norm_num [Nat.factorial]
  set N : ℝ := ((m + 1 : ℕ) : ℝ) with hNdef
  set NW : ℝ := DWr (m + 1) (JR (m + 1) 3) with hNWdef
  set β : ℝ := 1 / (600 * N) with hβdef
  set t : ℝ := tS (m + 1) β with htdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by rw [hmN]; linarith
  -- u = 1/√m
  set s : ℝ := Real.sqrt (m : ℝ) with hsdef
  have hs2 : s ^ 2 = (m : ℝ) := Real.sq_sqrt hm0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hm0
  have hs1 : (12247 : ℝ) ≤ s := by
    by_contra hcon
    rw [not_le] at hcon
    have : s ^ 2 < 12247 ^ 2 := pow_lt_pow_left₀ hcon hs0.le (by norm_num)
    rw [hs2, hmN] at this
    linarith
  set u : ℝ := 1 / s with hudef
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hu1 : u ≤ 1 / 12247 := one_div_le_one_div_of_le (by norm_num) hs1
  have hu2 : u ^ 2 = 1 / (m : ℝ) := by rw [hudef, div_pow, one_pow, hs2]
  -- w = 1/m
  set w : ℝ := 1 / (m : ℝ) with hwdef
  have hw0 : 0 < w := by rw [hwdef]; positivity
  have hw1 : w ≤ 677 / 100000000000 := by
    rw [hwdef, div_le_iff₀ hm0, hmN]; linarith
  have hNw : 1 / N ≤ w := one_div_le_one_div_of_le hm0 (by rw [hmN]; linarith)
  have hNi0 : 0 ≤ 1 / N := by positivity
  set L : ℝ := 2 / 3 * (CLs 3 / (m : ℝ)) with hLdef
  have hLw : L = 404 / 25 * w := by rw [hLdef, hCL, hwdef]; ring
  have hLu : L = 404 / 25 * u ^ 2 := by rw [hLw, hu2]
  have hL0 : 0 ≤ L := by rw [hLw]; positivity
  have hL1 : L ≤ 1 / 1000000 := by rw [hLw]; linarith
  have hLsq : L ^ 2 ≤ 1 / 1000000 * L := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hL1 hL0
  -- β
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβN : β * N = 1 / 600 := by rw [hβdef]; field_simp
  have hβs : β ≤ 1 / 1000000 := by
    have : β * 150000000 ≤ β * N := mul_le_mul_of_nonneg_left hNr hβ0.le
    linarith
  -- N_W
  have hN2 : (150000000 : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by norm_num) hNr 2
  have hN4 : N ^ 2 * (150000000 : ℝ) ^ 2 ≤ N ^ 4 := by
    have : N ^ 4 = N ^ 2 * N ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hN2 (sq_nonneg N)
  have hNW0 : 0 < NW := by
    have : (0 : ℝ) < N ^ 4 / 6 := by positivity
    linarith
  have hN4' : (150000000 : ℝ) ^ 2 * (150000000 : ℝ) ^ 2 ≤ N ^ 4 :=
    le_trans (mul_le_mul_of_nonneg_right hN2 (by positivity)) hN4
  have hNWs : 20808 / NW ≤ 1 / 1000000 := by
    rw [div_le_iff₀ hNW0]
    norm_num at hN4'
    linarith
  -- ν
  have hsq : (99 / 100 * (1 / 500) * β) ^ 2 * N ^ 2 = (99 / 30000000) ^ 2 := by
    have : (99 / 100 * (1 / 500) * β) ^ 2 * N ^ 2 = (99 / 50000) ^ 2 * (β * N) ^ 2 := by ring
    rw [this, hβN]; norm_num
  have hXpos : (20000 : ℝ) ≤ NW * (99 / 100 * (1 / 500) * β) ^ 2 := by
    have h1 : N ^ 4 / 6 * (99 / 100 * (1 / 500) * β) ^ 2 ≤ NW * (99 / 100 * (1 / 500) * β) ^ 2 :=
      mul_le_mul_of_nonneg_right hNW (sq_nonneg _)
    have h2 : N ^ 4 / 6 * (99 / 100 * (1 / 500) * β) ^ 2 = N ^ 2 / 6 * (99 / 30000000) ^ 2 := by
      rw [← hsq]; ring
    rw [h2] at h1
    norm_num at hN2 h1 ⊢
    linarith
  have hν : 2 / (NW * (99 / 100 * (1 / 500) * β) ^ 2) ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hS := SE6_le β hβ0.le hβs
  -- X
  set ζ : ℝ := 720 * (1 / s) with hζdef
  have hζu : ζ = 720 * u := rfl
  have hζ0 : 0 < ζ := by rw [hζu]; positivity
  set X : ℝ := Xc L 27 ((87 / 100) ^ 3) (456 / 100) (2604 / 100) (4211 / 500) (3 / 5)
    (77 / 1000) (81 / 50) 11 (1 / 10) ζ with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]; unfold Xc
    have h1 := VarM.kYc_nonneg L 27 11 (1 / 10) ζ (456 / 100) (2604 / 100) (4211 / 500)
      (3 / 5) (77 / 1000) hL0 (by linarith) (by norm_num) (by norm_num) (by norm_num) hζ0
    have h2 := VarM.kEc_nonneg L 27 11 (1 / 10) ζ hL0 (by norm_num) (by norm_num) (by norm_num)
      hζ0
    have h3 : (0 : ℝ) < 1 - L := by linarith
    have h4 : (0 : ℝ) ≤ (81 / 50 : ℝ) ^ 2 / (6 * (87 / 100) ^ 3 * (1 - L)) := by positivity
    exact add_nonneg h1 (mul_nonneg h2 h4)
  have hq : 1 / (1 - L) ≤ 1000002 / 1000000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hXle : X ≤ 746 * u := by
    have hF : (81 / 50 : ℝ) ^ 2 / (6 * (87 / 100) ^ 3 * (1 - L)) =
        ((81 / 50 : ℝ) ^ 2 / (6 * (87 / 100) ^ 3)) / (1 - L) := by
      rw [div_mul_eq_div_div]
    have hgen := X_gen L ζ (c1c 11 (1 / 10) (4211 / 500) (3 / 5) (77 / 1000))
      (c2c 11 (1 / 10))
      (c3c 27 11 (1 / 10) (456 / 100) (2604 / 100) (4211 / 500) (3 / 5) (77 / 1000))
      (c4c 27 11 (1 / 10)) ((81 / 50 : ℝ) ^ 2 / (6 * (87 / 100) ^ 3)) (1000002 / 1000000)
      (404 / 25) 720 u (1 / 12247) hu0 hu1 hLu hζu (by norm_num) (by norm_num) (by linarith) hq
      (by unfold c1c C1c; norm_num) (by unfold c2c; norm_num)
      (by unfold c3c C3c; norm_num) (by unfold c4c; norm_num) (by norm_num)
    have hXeq : X = L * c3c 27 11 (1 / 10) (456 / 100) (2604 / 100) (4211 / 500) (3 / 5)
          (77 / 1000) / (1 - L) + ζ / 2 +
        L * (c1c 11 (1 / 10) (4211 / 500) (3 / 5) (77 / 1000) +
          c3c 27 11 (1 / 10) (456 / 100) (2604 / 100) (4211 / 500) (3 / 5) (77 / 1000)) /
          ((1 - L) * (2 * ζ)) +
        L * (c4c 27 11 (1 / 10) + (c2c 11 (1 / 10) + c4c 27 11 (1 / 10)) / (2 * ζ)) *
          (((81 / 50 : ℝ) ^ 2 / (6 * (87 / 100) ^ 3)) / (1 - L)) := by
      rw [hXdef]; unfold Xc kYc kEc; rw [hF]
    rw [hXeq]
    refine hgen.trans (mul_le_mul_of_nonneg_right ?_ hu0.le)
    unfold c1c c2c c3c c4c C1c C3c
    norm_num
  have hXsq : X ^ 2 ≤ 556516 * w := by
    have h1 : X ^ 2 ≤ (746 * u) ^ 2 := pow_le_pow_left₀ hX0 hXle 2
    have h2 : (746 * u) ^ 2 = 556516 * w := by rw [mul_pow, hu2]; norm_num
    linarith
  -- the window
  have hW0 : 0 ≤ cVW 3 t L (X ^ 2) (1 / 20000) :=
    cVW_nonneg 3 t L (X ^ 2) (1 / 20000) (sq_nonneg X) (by norm_num)
  have hW := cVW_le3 t L (X ^ 2) ht0 ht1 hL0 hL1 (sq_nonneg X)
  have hV := var3 (SE (2 * 3) β (1 / 500)) (cVW 3 t L (X ^ 2) (1 / 20000)) N L
    (2 / (NW * (99 / 100 * (1 / 500) * β) ^ 2)) hS hW0 hN0 hL0 hL1 hν
  have htN : t ^ 2 ≤ 1 / 359000 * (1 / N) := by
    rw [mul_one_div, le_div_iff₀ hN0]; exact ht2
  have hE : 5 / 2 * (((3 : ℕ) : ℝ) + 1) ^ 2 * (N * L + 2) / (1 / 200 * N) =
      8000 * L + 16000 * (1 / N) := by
    push_cast; field_simp; ring
  have h100N : 100 / N = 100 * (1 / N) := by ring
  have h400N : 400 / N = 400 * (1 / N) := by ring
  refine ⟨⟨h5000, hL0, by linarith, by norm_num, by norm_num, by norm_num, by norm_num, ?_,
    hβ0, by linarith, by norm_num, by norm_num, by linarith, by linarith⟩, ?_⟩
  · linarith
  · unfold g3 semiBound89
    rw [hE, h100N, h400N]
    have hLw' : L * w ≤ 1 / 1000000 * w := mul_le_mul_of_nonneg_right hL1 hw0.le
    linarith

end BstLean.Part90

#print axioms BstLean.Part90.arith3
