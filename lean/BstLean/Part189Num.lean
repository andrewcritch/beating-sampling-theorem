import BstLean.Part189Bounds

/-! Part 189: exact rational cost certificates. Each result applies for every larger dimension. -/

namespace BstLean.Part189

theorem paperCount_lt_8000 {n : ℕ} (hn : 8000 ≤ n) :
    (paperCount n : ℝ) < (10003 / 10000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 8000) (d := 89) (q := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_8355 {n : ℕ} (hn : 8355 ≤ n) :
    (paperCount n : ℝ) < (125027 / 125000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 8355) (d := 91) (q := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_8514 {n : ℕ} (hn : 8514 ≤ n) :
    (paperCount n : ℝ) < (5001 / 5000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 8514) (d := (9227 / 100 : ℝ)) (q := (1921 / 200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_9963 {n : ℕ} (hn : 9963 ≤ n) :
    (paperCount n : ℝ) < (1000109 / 1000000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 9963) (d := 99) (q := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_10301 {n : ℕ} (hn : 10301 ≤ n) :
    (paperCount n : ℝ) < (25003 / 25000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 10301) (d := 101) (q := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_11364 {n : ℕ} (hn : 11364 ≤ n) :
    (paperCount n : ℝ) < (200013 / 200000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 11364) (d := 106) (q := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_11883 {n : ℕ} (hn : 11883 ≤ n) :
    (paperCount n : ℝ) < (200011 / 200000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 11883) (d := 109) (q := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_12225 {n : ℕ} (hn : 12225 ≤ n) :
    (paperCount n : ℝ) < (1000049 / 1000000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 12225) (d := 110) (q := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_13225 {n : ℕ} (hn : 13225 ≤ n) :
    (paperCount n : ℝ) < (10000363 / 10000000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 13225) (d := 115) (q := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_13483 {n : ℕ} (hn : 13483 ≤ n) :
    (paperCount n : ℝ) < (10000337 / 10000000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 13483) (d := 116) (q := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_14152 {n : ℕ} (hn : 14152 ≤ n) :
    (paperCount n : ℝ) < (250007 / 250000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 14152) (d := 118) (q := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_15324 {n : ℕ} (hn : 15324 ≤ n) :
    (paperCount n : ℝ) < (1000021 / 1000000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 15324) (d := 123) (q := 11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

theorem paperCount_lt_15469 {n : ℕ} (hn : 15469 ≤ n) :
    (paperCount n : ℝ) < (50001 / 50000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  apply paperCount_lt_of_certificate (a := 15469) (d := 124) (q := 11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hn
  norm_num [overhead]

end BstLean.Part189
