import BstLean.Part204Centre
import BstLean.Part159Paper

/-! S06: calibration ratio from 4096. -/

namespace BstLean.Part204

open Real
open BstLean.Part130 BstLean.Part134 BstLean.Part159 BstLean.Part157
open BstLean.Part136 (mW_ge_million)
open BstLean.Part140 (kap1 kap1_window)

variable {n : ℕ}

lemma kapT_window (hn : 4096 ≤ n) (hK : ConstK n) :
    |kapT n - kap1 (2 * n)| ≤ 1 / 10 ^ 4 * √(1 / (mW n : ℝ)) ∧
      493719 / 1000000 ≤ kapT n ∧ kapT n ≤ 493801 / 1000000 := by
  have hn4 : 4096 ≤ n := by omega
  have hmM := mW_ge_million hn4
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hmpos : (0 : ℝ) < mW n := by linarith
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  have hK' : (kapT n - kap1 (2 * n)) ^ 2 * (mW n : ℝ) ≤ 1 / 10 ^ 8 := hK
  have h1 : (kapT n - kap1 (2 * n)) ^ 2 ≤ (1 / 10 ^ 4 * √(1 / (mW n : ℝ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have e : (1 / 10 ^ 4 : ℝ) ^ 2 * (1 / (mW n : ℝ)) = 1 / 10 ^ 8 / (mW n : ℝ) := by ring
    rw [e, le_div_iff₀ hmpos]
    exact hK'
  have h2 : |kapT n - kap1 (2 * n)| ≤ 1 / 10 ^ 4 * √(1 / (mW n : ℝ)) :=
    abs_le_of_sq_le_sq h1 (by positivity)
  have h3 : √(1 / (mW n : ℝ)) ≤ 1 / 1000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hmpos]
    nlinarith
  have h4 := abs_le.mp h2
  refine ⟨h2, ?_, ?_⟩ <;> nlinarith
lemma pap_q (hn : 4096 ≤ n) (hK : ConstK n) {θ : WHid n} (hθS : θ ∈ goodS n) :
    qOf n (ccP n) θ ≤ 1001 / 1000 ∧
      |qOf n (ccP n) θ - 1| ≤
        1002 / 1000 * |SWp θ / 2 - 1| + 407 / 100 * |kapT n - kap1 (2 * n)| := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hκ1, hκ2⟩ := kapT_window hn hK
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hθS
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 1998 / 1000 ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2002 / 1000 := by linarith
  have hκ0 : 0 < kapT n := by linarith
  have hk0 : 0 < kap1 (2 * n) := by linarith
  have hSκ : 0 < SWp θ * kapT n ^ 2 := by positivity
  have hκsq1 : (493719 / 1000000 : ℝ) ^ 2 ≤ kapT n ^ 2 := pow_le_pow_left₀ (by norm_num) hκ1 2
  have hSκ1 : 1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2 ≤ SWp θ * kapT n ^ 2 :=
    mul_le_mul hS1 hκsq1 (by norm_num) (by linarith)
  set q := qOf n (ccP n) θ with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 2 * kap1 (2 * n) ^ 2 / (SWp θ * kapT n ^ 2) := by
    rw [hq]
    unfold qOf
    rw [Real.sq_sqrt (by unfold ccP; positivity), hNcast]
    unfold ccP
    field_simp
  -- `q² − 1`
  have hnum : |2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2| ≤
      198 / 100 * |kapT n - kap1 (2 * n)| + 4878 / 10000 * |SWp θ / 2 - 1| := by
    have e : 2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2 =
        -(2 * (kapT n - kap1 (2 * n)) * (kapT n + kap1 (2 * n))) +
          -(2 * (SWp θ / 2 - 1) * kapT n ^ 2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_neg, abs_mul, abs_mul, abs_mul, abs_mul]
    have a1 : |kapT n + kap1 (2 * n)| ≤ 99 / 100 := by
      rw [abs_of_pos (by linarith)]
      linarith
    have a2 : |kapT n ^ 2| ≤ 2439 / 10000 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := pow_le_pow_left₀ hκ0.le hκ2 2
      nlinarith
    have a3 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [a3]
    have b1 : 2 * |kapT n - kap1 (2 * n)| * |kapT n + kap1 (2 * n)| ≤
        2 * |kapT n - kap1 (2 * n)| * (99 / 100) :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    have b2 : 2 * |SWp θ / 2 - 1| * |kapT n ^ 2| ≤ 2 * |SWp θ / 2 - 1| * (2439 / 10000) :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    linarith
  have hq21 : |q ^ 2 - 1| ≤
      407 / 100 * |kapT n - kap1 (2 * n)| + 1002 / 1000 * |SWp θ / 2 - 1| := by
    have e : q ^ 2 - 1 = (2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2) / (SWp θ * kapT n ^ 2) := by
      rw [hq2]; field_simp
    rw [e, abs_div, abs_of_pos hSκ, div_le_iff₀ hSκ]
    refine hnum.trans ?_
    have c1 : (487 / 1000 : ℝ) ≤ SWp θ * kapT n ^ 2 := by
      refine le_trans (by norm_num) hSκ1
    have d1 : 0 ≤ |kapT n - kap1 (2 * n)| := abs_nonneg _
    have d2 : 0 ≤ |SWp θ / 2 - 1| := abs_nonneg _
    nlinarith [mul_nonneg d1 (sub_nonneg.mpr c1), mul_nonneg d2 (sub_nonneg.mpr c1)]
  have hq1 : |q - 1| ≤ |q ^ 2 - 1| := by
    have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [e, abs_mul, abs_of_pos (by linarith : 0 < q + 1)]
    nlinarith [abs_nonneg (q - 1)]
  refine ⟨?_, by linarith⟩
  -- `q ≤ 1.001`
  have hq2le : q ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 := by
    rw [hq2, div_le_iff₀ hSκ]
    have h1 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hk0.le hk2 2
    have h2 : 2 * (4938 / 10000 : ℝ) ^ 2 ≤
        (1001 / 1000 : ℝ) ^ 2 * (1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2) := by norm_num
    nlinarith
  exact le_of_abs_le (abs_le_of_sq_le_sq hq2le (by norm_num))


/-- The computed sphere constant has relative error below one percent. -/
theorem cNt_relative (hn : 4096 ≤ n) :
    |cNt n / BstLean.Part137.cN (2 * n) - 1| ≤
      1 / (3 * 10 ^ 23 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc0 := BstLean.Part141.cN_nonneg (2 * n)
  have hcw := (BstLean.Part201.cN_even_window hn).1
  have hcpos : 0 < BstLean.Part137.cN (2 * n) := by
    have : 0 < 1 / (13 * (n : ℝ)) := by positivity
    nlinarith
  have h := BstLean.Part159.cNt_close (by omega : 1 ≤ n)
  have e : cNt n / BstLean.Part137.cN (2 * n) - 1 =
      (cNt n - BstLean.Part137.cN (2 * n)) / BstLean.Part137.cN (2 * n) := by
    field_simp
  rw [e, abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
  convert h using 1 <;> ring

/-- The smoothing variance parameter stays positive from 4096. -/
theorem dNt_lower (hn : 4096 ≤ n) :
    33 / 100 / (n : ℝ) ≤ dNt n ∧ 0 < dNt n := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set c := BstLean.Part137.cN (2 * n)
  have hc0 : 0 ≤ c := BstLean.Part141.cN_nonneg _
  have hcw := (BstLean.Part201.cN_even_window hn).2
  change c ^ 2 ≤ 8 / (100 * (n : ℝ)) at hcw
  have hd := BstLean.Part159.cNt_close (by omega : 1 ≤ n)
  have he : 1 / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hd' : |cNt n - c| ≤ c / 100 := by
    refine hd.trans ?_
    have h := mul_le_mul_of_nonneg_left he hc0
    convert h using 1 <;> ring
  obtain ⟨hda, hdb⟩ := abs_le.mp hd'
  have hct2 : cNt n ^ 2 ≤ (101 / 100 * c) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hX : c ^ 2 * (n : ℝ) ≤ 8 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hcw
    nlinarith
  have hl : 33 / 100 / (n : ℝ) ≤ dNt n := by
    unfold dNt
    rw [div_le_iff₀ hnpos]
    have e : (1 / (2 * (n : ℝ)) - 2 * cNt n ^ 2) * (n : ℝ) =
        1 / 2 - 2 * (cNt n ^ 2 * (n : ℝ)) := by field_simp
    rw [e]
    have h := mul_le_mul_of_nonneg_right hct2 hnpos.le
    nlinarith
  exact ⟨hl, lt_of_lt_of_le (by positivity) hl⟩

end BstLean.Part204

#print axioms BstLean.Part204.kapT_window
#print axioms BstLean.Part204.pap_q
#print axioms BstLean.Part204.cNt_relative
#print axioms BstLean.Part204.dNt_lower
