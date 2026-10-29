import BstLean.Part247Overlap
import BstLean.Part247EBound

/-! Part 247: uniform numeric premises for the sharp two-input bound. -/
namespace BstLean.Part247
open Real BstLean.Part130 BstLean.Part182 BstLean.Part244
open BstLean.Part245 (kdot_mono)

theorem core_E {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hlo : (40 / 100 : ℝ) ≤ c) (hhi : c ≤ 63 / 100) :
    e3s_bound n ((mA n : ℝ) * (kdot (s3c1 n 46 c) / 2 + eta)) (√(2 * 46))
      (e4_b n ((mA n : ℝ) * (1 / 2 + eta)) 46)
      (e4_b n ((mA n : ℝ) * (kdot (63 / 100) / 2 + eta)) 46 ^ 2)
      (e4_b n 2 46) ≤ n * (595 / 1000) := by
  have hc1 := (core_s hn hlo hhi).2.2.2.2.2.2.2
  have h0 : kdot (63 / 100) ≤ (718 / 1000 : ℝ) :=
    (sn_kU (by norm_num) (by norm_num)).trans (by norm_num [snKU, snP7])
  have h1 : kdot (s3c1 n 46 c) ≤ (75 / 100 : ℝ) :=
    (kdot_mono hc1).trans core_slope
  exact e_bound hn h0 h1 (a := 847827 / 10^6) (ak := 613 / 1000)
    (R := 3419 / 100000) (m := 86195 / 100000)
    (by norm_num) (by norm_num [eta]) (by norm_num) (by norm_num [eta])
    (by norm_num) (by norm_num) (by norm_num [eta])

theorem core_num {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (40 / 100) (63 / 100) (595 / 1000) (35 / 1000) (25 / 100) eta 46 := by
  refine ⟨ko_bound hn, (core_s hn (c := 40 / 100) (by norm_num) (by norm_num)).1, ?_⟩
  intro c hlo hhi
  obtain ⟨_, hd, hd2, hc1, hC, he, hs, _⟩ := core_s hn hlo hhi
  exact ⟨hd, hd2, hc1, hC, he, core_E hn hlo hhi, hs⟩

theorem wide_E {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hlo : (34 / 100 : ℝ) ≤ c) (hhi : c ≤ 73 / 100) :
    e3s_bound n ((mA n : ℝ) * (kdot (s3c1 n 46 c) / 2 + eta)) (√(2 * 46))
      (e4_b n ((mA n : ℝ) * (1 / 2 + eta)) 46)
      (e4_b n ((mA n : ℝ) * (kdot (73 / 100) / 2 + eta)) 46 ^ 2)
      (e4_b n 2 46) ≤ n * (663 / 1000) := by
  have hc1 := (wide_s hn hlo hhi).2.2.2.2.2.2.2
  have h0 : kdot (73 / 100) ≤ (762 / 1000 : ℝ) :=
    (sn_kU (by norm_num) (by norm_num)).trans (by norm_num [snKU, snP7])
  have h1 : kdot (s3c1 n 46 c) ≤ (792 / 1000 : ℝ) :=
    (kdot_mono hc1).trans wide_slope
  exact e_bound hn h0 h1 (a := 87339 / 100000) (ak := 63 / 100)
    (R := 3513 / 100000) (m := 88751 / 100000)
    (by norm_num) (by norm_num [eta]) (by norm_num) (by norm_num [eta])
    (by norm_num) (by norm_num) (by norm_num [eta])

theorem wide_num {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (34 / 100) (73 / 100) (663 / 1000) (35 / 1000) (40 / 100) eta 46 := by
  refine ⟨ko_bound hn, (wide_s hn (c := 34 / 100) (by norm_num) (by norm_num)).1, ?_⟩
  intro c hlo hhi
  obtain ⟨_, hd, hd2, hc1, hC, he, hs, _⟩ := wide_s hn hlo hhi
  exact ⟨hd, hd2, hc1, hC, he, wide_E hn hlo hhi, hs⟩

theorem core_lam : ta_lam (595 / 1000) (35 / 1000) (25 / 100) ≤ (60 / 100 : ℝ) := by
  have hs : √((((595 / 1000 : ℝ) - 25 / 100) / 2)^2 + (35 / 1000)^2) ≤
      60 / 100 - (595 / 1000 + 25 / 100) / 2 := by
    apply en_sq_le <;> norm_num
  unfold ta_lam
  linarith

theorem wide_lam : ta_lam (663 / 1000) (35 / 1000) (40 / 100) ≤ (67 / 100 : ℝ) := by
  have hs : √((((663 / 1000 : ℝ) - 40 / 100) / 2)^2 + (35 / 1000)^2) ≤
      67 / 100 - (663 / 1000 + 40 / 100) / 2 := by
    apply en_sq_le <;> norm_num
  unfold ta_lam
  linarith

end BstLean.Part247
