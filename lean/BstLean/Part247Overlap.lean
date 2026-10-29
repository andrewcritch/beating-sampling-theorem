import BstLean.Part247SCell

/-! Part 247: rational overlap certificates on both full closed classes. -/
namespace BstLean.Part247
open Real Set BstLean.Part130 BstLean.Part182

theorem core_slope : kdot (705 / 1000) ≤ (75 / 100 : ℝ) :=
  (sn_kU (by norm_num) (by norm_num)).trans (by norm_num [snKU, snP7])

theorem wide_slope : kdot (7792 / 10000) ≤ (792 / 1000 : ℝ) :=
  (en_kdot_le (θ := 915 / 1000) (by norm_num) (by norm_num)
    (by norm_num)).trans (by norm_num)

theorem core_s {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hlo : (40 / 100 : ℝ) ≤ c) (hhi : c ≤ 63 / 100) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
      s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧
      s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 eta c ≤ (n : ℝ) * (25 / 100) ∧ s3c1 n 46 c ≤ 705 / 1000 := by
  apply s_cell hn (cl := 40 / 100) (ch := 63 / 100)
    (Su := 916516 / 10 ^ 6) (Sd := 776595 / 10 ^ 6) (Sc := 776596 / 10 ^ 6)
    (dlo := 7733 / 10000) (C1 := 705 / 1000) (q1 := 141003 / 100000)
    (kd1 := 75 / 100)
  all_goals first | exact hlo | exact hhi | exact core_slope |
    norm_num [snKU, snKL, snP7, snP5]

theorem wide_s {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hlo : (34 / 100 : ℝ) ≤ c) (hhi : c ≤ 73 / 100) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
      s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧
      s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 eta c ≤ (n : ℝ) * (40 / 100) ∧ s3c1 n 46 c ≤ 7792 / 10000 := by
  apply s_cell hn (cl := 34 / 100) (ch := 73 / 100)
    (Su := 940426 / 10 ^ 6) (Sd := 683447 / 10 ^ 6) (Sc := 683448 / 10 ^ 6)
    (dlo := 6708 / 10000) (C1 := 7792 / 10000) (q1 := 159547 / 100000)
    (kd1 := 792 / 1000)
  all_goals first | exact hlo | exact hhi | exact wide_slope |
    norm_num [snKU, snKL, snP7, snP5]

end BstLean.Part247
