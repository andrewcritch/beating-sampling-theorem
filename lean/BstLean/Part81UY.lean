import BstLean.Part81US
import BstLean.Part81UX

/-!
# Part 81: `ss2 = E κ(x,y)²` is close to `1/n`, uniformly in the map degree

`ss2U_of`: the weighted-row bound with the row integrals of `Part81UX`.
`ss2U`: `ss2 n d ≤ (1082/1000)/n` for `n ≥ 6000`; `ss2U8`: `≤ (1071/1000)/n` for `n ≥ 8000`.
`sphM_setS2`: replace the `ss2` constant of `SphM`.
-/

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)

theorem ss2U_of (n d : ℕ) (hd : 1 ≤ d) (hn : 5000 ≤ n) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ss2 n d ≤ (1 + 3 / (n : ℝ)) *
        (((1 - τ) + τ * (2719 / 1000) * (1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2)) / n) +
      (eD d + 4093 / 1000 / (n : ℝ)) *
        ((1 / τ + 1719 / 1000) * (3 / (n : ℝ) ^ 2)
          + 2719 / 1000 * ((3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n)) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (5000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hS := sphMU n d hd hn (101 / 100) (by norm_num) (by norm_num) (featOpU n d hn)
  have htG : tG n d ≤ eD d + 4093 / 1000 / (n : ℝ) := by linarith [hS.1]
  have hCL : 0 ≤ ((1 - τ) + τ * (2719 / 1000) * (1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2)) / n := by
    have : 0 ≤ 1 - τ := by linarith
    positivity
  have hCH : 0 ≤ (1 / τ + 1719 / 1000) * (3 / (n : ℝ) ^ 2)
      + 2719 / 1000 * ((3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n) := by positivity
  refine (ss2_le_rowW n d hn1 τ _ _ hτ hτ1 hCL hCH
    (fun i => UX.rowL n (by omega) τ hτ (d / 2) i)
    (fun i j => UX.rowH n (by omega) τ hτ (d / 2) i j)).trans ?_
  have := mul_le_mul_of_nonneg_right htG hCH
  linarith

theorem ss2U (n d : ℕ) (hd : 1 ≤ d) (hn : 6000 ≤ n) : ss2 n d ≤ 1082 / 1000 / (n : ℝ) := by
  have hn' : (6000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 6000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have he := eD_le d
  have he0 : 0 ≤ eD d := by
    have := one_le_eD d hd; linarith
  refine (ss2U_of n d hd (by omega) (1 / 45) (by norm_num) (by norm_num)).trans ?_
  have e : (1 + 3 / (n : ℝ)) *
        (((1 - 1 / 45) + 1 / 45 * (2719 / 1000) * (1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2)) / n) +
      (eD d + 4093 / 1000 / (n : ℝ)) *
        ((1 / (1 / 45) + 1719 / 1000) * (3 / (n : ℝ) ^ 2)
          + 2719 / 1000 * ((3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n)) =
      ((1 + 3 * (1 / (n : ℝ))) *
        ((1 - 1 / 45) + 1 / 45 * (2719 / 1000) * (1 + 3 * (1 / (n : ℝ)) + 16 * (1 / (n : ℝ)) ^ 2)) +
      (eD d + 4093 / 1000 * (1 / (n : ℝ))) *
        ((45 + 1719 / 1000) * 3 + 2719 / 1000 * (3 + 16 * (1 / (n : ℝ)))) * (1 / (n : ℝ))) *
        (1 / (n : ℝ)) := by
    field_simp
  have e2 : (1082 / 1000 : ℝ) / n = 1082 / 1000 * (1 / n) := by ring
  rw [e, e2]
  apply mul_le_mul_of_nonneg_right _ hx0.le
  set x := 1 / (n : ℝ)
  have hx2 : x ^ 2 ≤ 1 / 36000000 := by
    have := pow_le_pow_left₀ hx0.le hx 2; norm_num at this; exact this
  have hA : (1 + 3 * x) * ((1 - 1 / 45) + 1 / 45 * (2719 / 1000) * (1 + 3 * x + 16 * x ^ 2)) ≤
      10389 / 10000 := by
    have h1 : (1 - 1 / 45 : ℝ) + 1 / 45 * (2719 / 1000) * (1 + 3 * x + 16 * x ^ 2) ≤
        10383 / 10000 := by linarith
    have h0 : (0 : ℝ) ≤ (1 - 1 / 45) + 1 / 45 * (2719 / 1000) * (1 + 3 * x + 16 * x ^ 2) := by
      positivity
    calc _ ≤ (1 + 3 * (1 / 6000)) * (10383 / 10000) :=
          mul_le_mul (by linarith) h1 h0 (by norm_num)
      _ ≤ _ := by norm_num
  have hB : (eD d + 4093 / 1000 * x) * ((45 + 1719 / 1000) * 3 + 2719 / 1000 * (3 + 16 * x)) * x ≤
      428 / 10000 := by
    have h1 : eD d + 4093 / 1000 * x ≤ 172 / 100 := by linarith
    have h2 : (45 + 1719 / 1000 : ℝ) * 3 + 2719 / 1000 * (3 + 16 * x) ≤ 14833 / 100 := by linarith
    have h10 : 0 ≤ eD d + 4093 / 1000 * x := by positivity
    have h20 : (0 : ℝ) ≤ (45 + 1719 / 1000) * 3 + 2719 / 1000 * (3 + 16 * x) := by positivity
    calc _ ≤ 172 / 100 * (14833 / 100) * (1 / 6000) :=
          mul_le_mul (mul_le_mul h1 h2 h20 (by norm_num)) hx hx0.le (by norm_num)
      _ ≤ _ := by norm_num
  linarith

theorem ss2U8 (n d : ℕ) (hd : 1 ≤ d) (hn : 8000 ≤ n) : ss2 n d ≤ 1071 / 1000 / (n : ℝ) := by
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have he := eD_le d
  have he0 : 0 ≤ eD d := by
    have := one_le_eD d hd; linarith
  refine (ss2U_of n d hd (by omega) (1 / 50) (by norm_num) (by norm_num)).trans ?_
  have e : (1 + 3 / (n : ℝ)) *
        (((1 - 1 / 50) + 1 / 50 * (2719 / 1000) * (1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2)) / n) +
      (eD d + 4093 / 1000 / (n : ℝ)) *
        ((1 / (1 / 50) + 1719 / 1000) * (3 / (n : ℝ) ^ 2)
          + 2719 / 1000 * ((3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n)) =
      ((1 + 3 * (1 / (n : ℝ))) *
        ((1 - 1 / 50) + 1 / 50 * (2719 / 1000) * (1 + 3 * (1 / (n : ℝ)) + 16 * (1 / (n : ℝ)) ^ 2)) +
      (eD d + 4093 / 1000 * (1 / (n : ℝ))) *
        ((50 + 1719 / 1000) * 3 + 2719 / 1000 * (3 + 16 * (1 / (n : ℝ)))) * (1 / (n : ℝ))) *
        (1 / (n : ℝ)) := by
    field_simp
  have e2 : (1071 / 1000 : ℝ) / n = 1071 / 1000 * (1 / n) := by ring
  rw [e, e2]
  apply mul_le_mul_of_nonneg_right _ hx0.le
  set x := 1 / (n : ℝ)
  have hx2 : x ^ 2 ≤ 1 / 64000000 := by
    have := pow_le_pow_left₀ hx0.le hx 2; norm_num at this; exact this
  have hA : (1 + 3 * x) * ((1 - 1 / 50) + 1 / 50 * (2719 / 1000) * (1 + 3 * x + 16 * x ^ 2)) ≤
      10349 / 10000 := by
    have h1 : (1 - 1 / 50 : ℝ) + 1 / 50 * (2719 / 1000) * (1 + 3 * x + 16 * x ^ 2) ≤
        10345 / 10000 := by linarith
    have h0 : (0 : ℝ) ≤ (1 - 1 / 50) + 1 / 50 * (2719 / 1000) * (1 + 3 * x + 16 * x ^ 2) := by
      positivity
    calc _ ≤ (1 + 3 * (1 / 8000)) * (10345 / 10000) :=
          mul_le_mul (by linarith) h1 h0 (by norm_num)
      _ ≤ _ := by norm_num
  have hB : (eD d + 4093 / 1000 * x) * ((50 + 1719 / 1000) * 3 + 2719 / 1000 * (3 + 16 * x)) * x ≤
      352 / 10000 := by
    have h1 : eD d + 4093 / 1000 * x ≤ 172 / 100 := by linarith
    have h2 : (50 + 1719 / 1000 : ℝ) * 3 + 2719 / 1000 * (3 + 16 * x) ≤ 16333 / 100 := by linarith
    have h10 : 0 ≤ eD d + 4093 / 1000 * x := by positivity
    have h20 : (0 : ℝ) ≤ (50 + 1719 / 1000) * 3 + 2719 / 1000 * (3 + 16 * x) := by positivity
    calc _ ≤ 172 / 100 * (16333 / 100) * (1 / 8000) :=
          mul_le_mul (mul_le_mul h1 h2 h20 (by norm_num)) hx hx0.le (by norm_num)
      _ ≤ _ := by norm_num
  linarith

lemma sphM_setS2 {n d : ℕ} {M1 S2 B1 B2 B3 S2' : ℝ} (h : ss2 n d ≤ S2' / (n : ℝ))
    (hS : SphM n d M1 S2 B1 B2 B3) : SphM n d M1 S2' B1 B2 B3 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8⟩ := hS
  exact ⟨a1, a2, a3, a4, a5, a6, h, a8⟩

lemma sphC_setS2 {n d : ℕ} {M1 S2 B1 VK sM S2' : ℝ} (h : ss2 n d ≤ S2' / (n : ℝ))
    (hS : SphC n d M1 S2 B1 VK sM) : SphC n d M1 S2' B1 VK sM := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7, a8, a9⟩ := hS
  exact ⟨a1, a2, a3, a4, a5, h, a7, a8, a9⟩

end BstLean.Part81

#print axioms BstLean.Part81.ss2U
#print axioms BstLean.Part81.ss2U8
