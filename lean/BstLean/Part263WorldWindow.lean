import BstLean.Part263Cells
import BstLean.Part250Noiselo
import BstLean.Part250Noisehi

/-! Exact World-window endpoints at each dimension. -/
namespace BstLean.Part263
open Real Set

theorem world_upper_le {n : ℕ} (hn : 12225 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ (523141 / 10 ^ 6 : ℝ) := by
  have hnr : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : √(12 / (n : ℝ)) ≤ √(12 / (12225 : ℝ)) := by
    apply sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnr
  have hroot0 : √(12 / (12225 : ℝ)) ≤ (32 / 1000 : ℝ) :=
    sqrt_le_iff.mpr (by norm_num)
  have hden : 0 < (1 - 2 * √(12 / (12225 : ℝ))) + (202831 / 100000 - 1) := by
    linarith
  have hmono : BstLean.Part227.noiseUpper n (202831 / 100000) ≤
      BstLean.Part227.noiseUpper 12225 (202831 / 100000) := by
    unfold BstLean.Part227.noiseUpper
    exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
  exact hmono.trans (BstLean.Part250.noisehi.2.trans (by norm_num))

noncomputable def worldGrid {n : ℕ} (hn : 12225 ≤ n) (top : ℝ)
    (htop : 46 / 100 < top)
    (hlower : noiseNode top 10 < (472080 / 10 ^ 6 : ℝ))
    (hupper : (523141 / 10 ^ 6 : ℝ) < noiseNode top 53) : Grid where
  top := top
  worldLower := BstLean.Part227.noiseLower (202225 / 100000)
  worldUpper := BstLean.Part227.noiseUpper n (202831 / 100000)
  top_pos := htop
  lower_node := hlower.trans_le (le_trans (by norm_num) BstLean.Part250.noiselo.1)
  upper_node := (world_upper_le hn).trans_lt hupper

theorem worldGrid_domain {n : ℕ} (hn : 12225 ≤ n) (top : ℝ)
    (htop : 46 / 100 < top)
    (hlower : noiseNode top 10 < (472080 / 10 ^ 6 : ℝ))
    (hupper : (523141 / 10 ^ 6 : ℝ) < noiseNode top 53) :
    Icc (worldGrid hn top htop hlower hupper).worldLower
      (worldGrid hn top htop hlower hupper).worldUpper =
    Icc (BstLean.Part227.noiseLower (202225 / 100000))
      (BstLean.Part227.noiseUpper n (202831 / 100000)) := rfl

end BstLean.Part263
