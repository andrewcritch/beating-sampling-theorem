import BstLean.Part263WorldWindow

namespace BstLean.Part269
open Real Set BstLean.Part263

theorem noise_upper_bound {n : ℕ} {N R U : ℝ}
    (hn : N ≤ n) (hN : 0 < N) (hR : 0 ≤ R)
    (hs : 12 ≤ R ^ 2 * N)
    (hden : 0 < (1 - 2 * R) + (202831 / 100000 - 1))
    (hU : (202831 / 100000 - 1) / ((1 - 2 * R) + (202831 / 100000 - 1)) ≤ U) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ U := by
  have hnpos : (0 : ℝ) < n := hN.trans_le hn
  have hroot : √(12 / (n : ℝ)) ≤ R := by
    apply sqrt_le_iff.mpr
    refine ⟨hR, ?_⟩
    apply (div_le_iff₀ hnpos).mpr
    exact hs.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg R))
  unfold BstLean.Part227.noiseUpper
  apply le_trans ?_ hU
  exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith)

theorem noise_upper_early {n : ℕ} (hn : 12350 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (5231 / 10000 : ℝ) := by
  apply noise_upper_bound (N := 12350) (R := 31172 / 1000000)
  · exact_mod_cast hn
  all_goals norm_num

theorem noise_upper_late {n : ℕ} (hn : 12800 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (5228 / 10000 : ℝ) := by
  apply noise_upper_bound (N := 12800) (R := 30619 / 1000000)
  · exact_mod_cast hn
  all_goals norm_num

noncomputable def earlyGrid {n : ℕ} (hn : 12350 ≤ n) (top : ℝ)
    (ht : top ∈ Icc (5315 / 10000 : ℝ) (5319 / 10000)) : Grid where
  top := top
  worldLower := BstLean.Part227.noiseLower (202225 / 100000)
  worldUpper := BstLean.Part227.noiseUpper n (202831 / 100000)
  top_pos := by linarith [ht.1]
  lower_node := by
    apply lt_of_lt_of_le _ BstLean.Part250.noiselo.1
    unfold noiseNode
    linarith [ht.2]
  upper_node := (noise_upper_early hn).trans_lt (by unfold noiseNode; linarith [ht.1])

noncomputable def lateGrid {n : ℕ} (hn : 12800 ≤ n) (top : ℝ)
    (ht : top ∈ Icc (5313 / 10000 : ℝ) (5319 / 10000)) : Grid where
  top := top
  worldLower := BstLean.Part227.noiseLower (202225 / 100000)
  worldUpper := BstLean.Part227.noiseUpper n (202831 / 100000)
  top_pos := by linarith [ht.1]
  lower_node := by
    apply lt_of_lt_of_le _ BstLean.Part250.noiselo.1
    unfold noiseNode
    linarith [ht.2]
  upper_node := (noise_upper_late hn).trans_lt (by unfold noiseNode; linarith [ht.1])

end BstLean.Part269
