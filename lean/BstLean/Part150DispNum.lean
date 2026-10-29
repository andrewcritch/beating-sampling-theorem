import BstLean.Part150Disp
import BstLean.Part149Num3

/-!
# Part 150, item 5, the frame with the parameters of `onePassA149`

* `p149 n = 1835/n + 130287/(n√n) + 5368347/n²`: the failure bound of `onePassA149` (the
  program of Part 149 with the oracle centre `bMF`).
* `pFail3_149`: the formula `pFail3` at the parameters of `onePassA149` is at most `p149 n`.
* **`displace150`**: for every `n ≥ 4096`, every measurable centre `bh` with
  `E[1_good·|bh − bMF|²] ≤ (m/n)·ξ` (`DispOK n (Gwin n) (9/100) (1/10) bh ξ`) and every `η₄ > 0`:
  `Pr(|gOutH bh − B| ≤ sd/2) ≥ 1 − ((1 + η₄)·p149 n + ξ·(625 + (1 + 1/η₄)·235))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part141 BstLean.Part145
open BstLean.Part149

variable {n : ℕ}

/-- The failure bound of `onePassA149`. -/
noncomputable def p149 (n : ℕ) : ℝ :=
  1835 / (n : ℝ) + 130287 / ((n : ℝ) * √(n : ℝ)) + 5368347 / (n : ℝ) ^ 2

lemma X_le_pFail3 {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb : ℝ}
    (hxi : 0 ≤ xiB n εD π₀ ζ₃ dQb) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    4 * aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb /
        (θ * (4 / (n : ℝ) * (222757 / 1000000))) ≤
      pFail3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb := by
  have h1θ : 0 < 1 - θ := by linarith
  have b1 : (0 : ℝ) ≤ 1 / 50000 / (n : ℝ) := by positivity
  have b2 : (0 : ℝ) ≤ 68000000 / (qA n : ℝ) ^ 2 := by positivity
  have b3 : 0 ≤ ΔKb ^ 2 / Δmax ^ 2 := by positivity
  have b4 : 0 ≤ ΔXb ^ 2 / ΔXmax ^ 2 := by positivity
  have b5 : 0 ≤ dQb ^ 2 / εQ ^ 2 := by positivity
  have b6 : (0 : ℝ) ≤ 5 / (mA n : ℝ) / εD ^ 2 := by positivity
  have b7 : 0 ≤ xiB n εD π₀ ζ₃ dQb / Dmax ^ 2 := div_nonneg hxi (sq_nonneg _)
  have b8 : 0 ≤ 2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 /
      (4 * θ * (1 - θ) * (4 / (n : ℝ) * (222757 / 1000000)) ^ 2) := by positivity
  unfold pFail3 aE3
  linarith

lemma pFail5_le {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb
    η₄ ξ D4 y4 : ℝ} (hη₄ : 0 ≤ η₄)
    (hX : 4 * aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb /
        (θ * (4 / (n : ℝ) * (222757 / 1000000))) ≤
      pFail3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb) :
    pFail5 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb
        η₄ ξ D4 y4 ≤
      (1 + η₄) * pFail3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃
          dQb + ξ / D4 ^ 2 +
        (1 + 1 / η₄) * (4 * (2 / (n : ℝ) * (2 / (1 - y4)) * ξ) /
          (θ * (4 / (n : ℝ) * (222757 / 1000000)))) := by
  unfold pFail5
  have := mul_le_mul_of_nonneg_left hX hη₄
  linarith

/-- The formula `pFail3` at the parameters of `onePassA149`. -/
theorem pFail3_149 (hn : 4096 ≤ n) :
    pFail3 n (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000) (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) 24 (95 / 100) (393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (9 / 100) (1 / 10) (88 / 100) (67 / 1000) (8441 / 10000) (9 / 100) (31 / 100) (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) ≤ p149 n := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hst : √(n : ℝ) = 1 / t := by rw [ht]; field_simp
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [hnt]; field_simp
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA6 : 1000000 ≤ mA n := by
    unfold mA
    calc 1000000 ≤ 4096 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have hcF : cF2o (mA n) ≤ 4728 / 1000 * t ^ 2 := by
    have h1 := BstLean.Part136.cF2o_sq_le hmA6
    have h0 := (BstLean.Part136.cF2o_pos hmA).le
    rw [mA_eqR] at h1
    have h2 : (2235 : ℝ) / 100 / (n : ℝ) ^ 2 = 2235 / 100 * (t ^ 2) ^ 2 := by
      rw [ht2]; field_simp
    rw [h2] at h1
    have h3 : cF2o (mA n) ^ 2 ≤ (4728 / 1000 * t ^ 2) ^ 2 := by
      refine h1.trans ?_
      have : 0 ≤ (t ^ 2) ^ 2 := by positivity
      nlinarith
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (by positivity))
  have hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dK2 n (mA n) q ≤ 393278 / 1000000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dK2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dX2 n (mA n) q ≤ 16034 / 100000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dX2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dQ1 n (mA n) q ≤ 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dQ1_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hP : POK2 (6662 / 10000) (6969 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
      (1908 / 1000) (273 / 1000) (251 / 1000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hP3 : POK3 (6969 / 10000) (284 / 10000) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8517 / 10000) (8441 / 10000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [pFail3_eq (by norm_num) (by norm_num) (by norm_num) ht0 hnt hst]
  have e2 : (1835 : ℝ) / (n : ℝ) = 1835 * t ^ 2 := by rw [ht2]; ring
  have e3 : (130287 : ℝ) / ((n : ℝ) * √(n : ℝ)) = 130287 * t ^ 3 := by
    rw [hst, hnt]; field_simp
  have e4 : (5368347 : ℝ) / (n : ℝ) ^ 2 = 5368347 * t ^ 4 := by
    rw [hnt]; field_simp
  unfold p149
  rw [e2, e3, e4]
  unfold EA2 Part149.kK2 Part149.kX2 Part149.kD2 cQ3 cD3 Kq
  have p2 : 0 < t ^ 2 := by positivity
  have p3 : 0 < t ^ 3 := by positivity
  have p4 : 0 < t ^ 4 := by positivity
  clear_value t
  ring_nf
  linarith

/-- The formula `pFail5` at the parameters of `onePassA149`, `D4 = 1/25`, `y4 = 0.9193`. -/
theorem pFail5_149 (hn : 4096 ≤ n) {ξ η₄ : ℝ} (hξ0 : 0 ≤ ξ) (hη₄ : 0 < η₄) :
    pFail5 n (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000) (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) 24 (95 / 100) (393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2) (4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (9 / 100) (1 / 10) (88 / 100) (67 / 1000) (8441 / 10000) (9 / 100) (31 / 100) (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) η₄ ξ (1 / 25) (9193 / 10000) ≤
      (1 + η₄) * p149 n + ξ * (625 + (1 + 1 / η₄) * 235) := by
  have h3 := pFail3_149 hn
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hxi : 0 ≤ xiB n (9 / 100) (88 / 100) (9 / 100)
      (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) := by
    unfold xiB cQ3 cD3 Kq; positivity
  refine (pFail5_le hη₄.le (X_le_pFail3 hxi (by norm_num) (by norm_num))).trans ?_
  have eY : 4 * (2 / (n : ℝ) * (2 / (1 - 9193 / 10000)) * ξ) /
      (95 / 100 * (4 / (n : ℝ) * (222757 / 1000000))) =
      ξ * (4 / ((1 - 9193 / 10000) * (95 / 100) * (222757 / 1000000))) := by
    have hn0 : (n : ℝ) ≠ 0 := hx0.ne'
    field_simp
    ring
  have nY : (4 : ℝ) / ((1 - 9193 / 10000) * (95 / 100) * (222757 / 1000000)) ≤ 235 := by
    norm_num
  have hY : ξ * (4 / ((1 - 9193 / 10000) * (95 / 100) * (222757 / 1000000))) ≤ ξ * 235 :=
    mul_le_mul_of_nonneg_left nY hξ0
  have hη' : (0 : ℝ) ≤ 1 + 1 / η₄ := by positivity
  have hY2 := mul_le_mul_of_nonneg_left hY hη'
  have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + η₄)
  have e6 : ξ / (1 / 25 : ℝ) ^ 2 = ξ * 625 := by ring
  rw [eY, e6]
  linarith

/-- **A program with another centre succeeds**, with the parameters of `onePassA149`. -/
theorem displace150 (hn : 4096 ≤ n) {bh : CMap n} (hbh : Measurable bh) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : DispOK n (Gwin n) (9 / 100) (1 / 10) bh ξ) {η₄ : ℝ} (hη₄ : 0 < η₄) :
    1 - ((1 + η₄) * p149 n + ξ * (625 + (1 + 1 / η₄) * 235)) ≤
      (mlpTriple 2 n).real
        {t | |gOutH bh t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2| ≤
          sdn t.1 t.2.1 t.2.2 / 2} := by
  have h5 := pFail5_149 hn hξ0 hη₄
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hst : √(n : ℝ) = 1 / t := by rw [ht]; field_simp
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [hnt]; field_simp
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA6 : 1000000 ≤ mA n := by
    unfold mA
    calc 1000000 ≤ 4096 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have hcF : cF2o (mA n) ≤ 4728 / 1000 * t ^ 2 := by
    have h1 := BstLean.Part136.cF2o_sq_le hmA6
    have h0 := (BstLean.Part136.cF2o_pos hmA).le
    rw [mA_eqR] at h1
    have h2 : (2235 : ℝ) / 100 / (n : ℝ) ^ 2 = 2235 / 100 * (t ^ 2) ^ 2 := by
      rw [ht2]; field_simp
    rw [h2] at h1
    have h3 : cF2o (mA n) ^ 2 ≤ (4728 / 1000 * t ^ 2) ^ 2 := by
      refine h1.trans ?_
      have : 0 ≤ (t ^ 2) ^ 2 := by positivity
      nlinarith
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (by positivity))
  have hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dK2 n (mA n) q ≤ 393278 / 1000000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dK2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dX2 n (mA n) q ≤ 16034 / 100000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dX2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dQ1 n (mA n) q ≤ 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dQ1_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hP : POK2 (6662 / 10000) (6969 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
      (1908 / 1000) (273 / 1000) (251 / 1000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hP3 : POK3 (6969 / 10000) (284 / 10000) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8517 / 10000) (8441 / 10000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hsq : √(8441 / 10000 : ℝ) ≤ 91876 / 100000 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hy4 : (√(8441 / 10000 : ℝ) + 1 / 25) ^ 2 ≤ 9193 / 10000 := by
    have h0 := Real.sqrt_nonneg (8441 / 10000 : ℝ)
    nlinarith
  have h := displace150_formula hn hP (η₄ := η₄) hη₄ hP3 (ζ₃ := 9 / 100) (by norm_num)
    (η₃ := 31 / 100)
    (by norm_num) (dQb := 534859 / 1000000 * t + 12510 / 1000 * t ^ 2) hdQ
    (fun q hq1 hq2 => dQ1_nonneg hq1 hq2 hn1)
    (η := 51 / 10) (by norm_num) (ζ := 56 / 1000)
    (by norm_num) (ζ₂ := 1 / 10) (by norm_num) (η₁ := 24) (by norm_num) (θ := 95 / 100)
    (by norm_num) (by norm_num) (ΔKb := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2)
    (ΔXb := 16034 / 100000 * t + 11363 / 1000 * t ^ 2) (by positivity) (by positivity) hΔK
    (fun q hq1 hq2 => dK2_nonneg hq1 hq2 hn1) hΔX (fun q _ _ => dX2_nonneg hn1) hcF
    hbh (D4 := 1 / 25) (y4 := 9193 / 10000) (by norm_num) hy4 (by norm_num) hξ0 hξ
  refine le_trans ?_ h
  exact sub_le_sub_left h5 1

end BstLean.Part150

open BstLean.Part150 in
#print axioms displace150
