import BstLean.Part170FinW

/-!
# Part 170 (file `NumW`): the numbers of the two fluctuation allowances; the numeric end theorem

No proof is left open; no `native_decide` or `axiom` is used.

* **`Wfl_le`**: `W_fl ≤ 0.1413` for every `n ≥ 80 000`.
* **`classifier_paper_bias_num80k`**: every `n ≥ 80 000`, `A_f = 0.04`, `A_ω = 0.39`. Remaining
  hypotheses: a measurable first-layer event family `Gb` with charge `δ_G ≤ 0.0006` in the window,
  and the bias moments `BiasMomF (O1n n) Gb 0.004`, `BiasMomW (O1n n) Gb 0.02`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- **`W_fl ≤ 0.1413`** for every `n ≥ 80 000`. -/
lemma Wfl_le (hn : 80000 ≤ n) : Wfl n (O1n n) ≤ 1413 / 10000 := by
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr : 282 ≤ r := by rw [hrd, Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  have hr0 : 0 < r := by linarith
  -- the pieces in terms of `r`
  have hO2 : O1n n ^ 2 = 2 * (r + 2) ^ 2 := by
    unfold O1n
    rw [mul_pow, Real.sq_sqrt (by positivity), ← hrd, ← hr2]
    field_simp
  have htA : tA n = 2 / r ^ 4 := by
    unfold tA mA
    push_cast
    rw [← hr2]; ring
  set L := √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) with hLd
  set Lb := 2 * (r + 2) / (r ^ 2 * (r - 1 / 250)) with hLbd
  have hr4 : 0 < r - 1 / 250 := by linarith
  have hLb0 : 0 < Lb := by positivity
  have hL : L ≤ Lb := by
    rw [hLd, Real.sqrt_le_left hLb0.le, htA, hO2, ← hr2]
    rw [hLbd, div_pow, mul_pow]
    have h1 : (r - 1 / 250) ^ 2 ≤ r ^ 2 - 2 := by nlinarith
    have h2 : 0 < r ^ 2 - 2 := by nlinarith
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 0 ≤ (r + 2) ^ 2 := sq_nonneg _
    have h4 : 0 < r ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h4.le)]
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hT : √(tA n * O1n n ^ 2) = 2 * (r + 2) / r ^ 2 := by
    rw [htA, hO2]
    rw [show 2 / r ^ 4 * (2 * (r + 2) ^ 2) = (2 * (r + 2) / r ^ 2) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hM : √((mA n : ℝ) + 8) ≤ r ^ 2 + 1 / 1000 := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold mA; push_cast; rw [← hr2]; nlinarith
  have h3 : √(3 : ℝ) ≤ 17321 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hpi : π ≤ 31416 / 10000 := by have := Real.pi_lt_d4; norm_num at this ⊢; linarith
  -- the polynomial inequalities
  have hX : Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) ≤ 144 / 10000 := by
    rw [hLbd]
    set d := r - 282 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 282 + d := by linarith
    rw [show 2 * (r + 2) / (r ^ 2 * (r - 1 / 250)) * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) =
      4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) / (r ^ 4 * (r - 1 / 250)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    have hP : 144 / 10000 * (r ^ 4 * (r - 1 / 250)) - 4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) =
        9 / 625 * d ^ 5 + 2547491 / 156250 * d ^ 4 + 540889924 / 78125 * d ^ 3 +
        204242985079 / 156250 * d ^ 2 + 7241340648676 / 78125 * d + 1879217731408 / 78125 := by
      rw [hrd']; ring
    have : 0 ≤ 9 / 625 * d ^ 5 + 2547491 / 156250 * d ^ 4 + 540889924 / 78125 * d ^ 3 +
        204242985079 / 156250 * d ^ 2 + 7241340648676 / 78125 * d + 1879217731408 / 78125 := by
      positivity
    linarith
  have hLs : Lb ≤ 26 / 1000000 := by
    rw [hLbd, div_le_iff₀ (by positivity)]
    set d := r - 282 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 282 + d := by linarith
    rw [hrd']
    nlinarith [pow_nonneg hd 2, pow_nonneg hd 3, mul_nonneg hd (pow_nonneg hd 2)]
  -- assemble
  unfold Wfl
  rw [← hLd, hT]
  have hpos : 0 ≤ 2 * (r + 2) / r ^ 2 := by positivity
  have hm0 : 0 ≤ √((mA n : ℝ) + 8) := Real.sqrt_nonneg _
  have hmain : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2) * (√3 * √((mA n : ℝ) + 8)) ≤
      2 * (31416 / 10000 / 2 * (18 / 10)) * (17321 / 10000) * (144 / 10000) := by
    have e : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2) * (√3 * √((mA n : ℝ) + 8)) =
        2 * (π / 2 * (18 / 10)) * √3 * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) := by ring
    rw [e]
    have h1 : L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) ≤ 144 / 10000 := by
      calc L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)
          ≤ Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) := by gcongr
        _ ≤ 144 / 10000 := hX
    have h0 : 0 ≤ L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) := by positivity
    have hpi0 := Real.pi_pos
    have h30 : 0 ≤ √(3 : ℝ) := Real.sqrt_nonneg _
    have hA : 2 * (π / 2 * (18 / 10)) * √3 ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) * (17321 / 10000) := by
      have : π / 2 * (18 / 10) ≤ 31416 / 10000 / 2 * (18 / 10) := by linarith
      have := mul_le_mul this h3 h30 (by norm_num)
      linarith
    calc 2 * (π / 2 * (18 / 10)) * √3 * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8))
        ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) * (17321 / 10000) *
          (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) :=
          mul_le_mul_of_nonneg_right hA h0
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hLL : L ≤ 26 / 1000000 := hL.trans hLs
  have ha1 : (π / 2 * (25 / 10) * L) ^ 2 + 2 * (π / 2 * (18 / 10) * L) + (π / 2 * L) ^ 2 ≤
      2 / 10000 := by
    have hpl := mul_le_mul hpi hLL hL0 (by norm_num)
    have hpi0 := Real.pi_pos
    have e1 : π / 2 * (25 / 10) * L ≤ 31416 / 10000 / 2 * (25 / 10) * (26 / 1000000) := by
      linarith [hpl]
    have e2 : π / 2 * (18 / 10) * L ≤ 31416 / 10000 / 2 * (18 / 10) * (26 / 1000000) := by
      linarith [hpl]
    have e3 : π / 2 * L ≤ 31416 / 10000 / 2 * (26 / 1000000) := by linarith [hpl]
    have p1 : 0 ≤ π / 2 * (25 / 10) * L := by positivity
    have p3 : 0 ≤ π / 2 * L := by positivity
    have q1 := pow_le_pow_left₀ p1 e1 2
    have q3 := pow_le_pow_left₀ p3 e3 2
    have hnum : (31416 / 10000 / 2 * (25 / 10) * (26 / 1000000) : ℝ) ^ 2 +
        2 * (31416 / 10000 / 2 * (18 / 10) * (26 / 1000000)) +
        (31416 / 10000 / 2 * (26 / 1000000) : ℝ) ^ 2 ≤ 2 / 10000 := by norm_num
    linarith
  norm_num at hmain
  linarith

/-- **The numeric end theorem**: every `n ≥ 80 000`, with `A_f = 0.04` and `A_ω = 0.39`.
Remaining hypotheses: a measurable first-layer event family `Gb` with charge `δ_G ≤ 0.0006` in the
window, and the bias moments `B_f = 0.004` (location) and `B_ω = 0.02` (energy) on `Gb`. -/
theorem classifier_paper_bias_num80k (hn : 80000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ 6 / 10000)
    (hBiasF : BiasMomF (O1n n) Gb (4 / 1000)) (hBiasW : BiasMomW (O1n n) Gb (2 / 100)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_flw80k hn t hGb (by norm_num) hδG (by norm_num) (by norm_num)
    (Af := 4 / 100) (Aw := 39 / 100) (by norm_num) (by norm_num) (by norm_num) hBiasF hBiasW ?_
  have hF := Ffl_le hn
  have hW := Wfl_le hn
  have hF0 : 0 ≤ Ffl n (O1n n) := by unfold Ffl; have := Real.pi_pos; positivity
  have hW0 : 0 ≤ Wfl n (O1n n) := by unfold Wfl; have := Real.pi_pos; positivity
  have h1 : ((Ffl n (O1n n) + 4 / 1000) / (4 / 100)) ^ 8 ≤ ((101 / 10000 + 4 / 1000) / (4 / 100)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have h2 : ((Wfl n (O1n n) + 2 / 100) / (39 / 100)) ^ 8 ≤
      ((1413 / 10000 + 2 / 100) / (39 / 100)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have hr := BstLean.Part167.roomE_ge
  have h3 : (6 : ℝ) / 10000 + ((101 / 10000 + 4 / 1000) / (4 / 100)) ^ 8 +
      ((1413 / 10000 + 2 / 100) / (39 / 100)) ^ 8 ≤ 1792 / 10 ^ 6 := by norm_num
  linarith

end BstLean.Part170
