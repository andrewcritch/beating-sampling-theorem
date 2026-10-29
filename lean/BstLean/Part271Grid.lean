import BstLean.Part269Grid

/-! A World grid whose upper guard takes a per-dimension bound on the noise upper end. -/
namespace BstLean.Part271
open Real Set BstLean.Part263

noncomputable def worldGrid {n : ℕ} {U : ℝ}
    (hU : BstLean.Part227.noiseUpper n (202831/100000) ≤ U) (top : ℝ)
    (htop : 46/100 < top)
    (hlower : noiseNode top 10 < (472080/10^6 : ℝ))
    (hupper : U < noiseNode top 53) : Grid where
  top := top
  worldLower := BstLean.Part227.noiseLower (202225/100000)
  worldUpper := BstLean.Part227.noiseUpper n (202831/100000)
  top_pos := htop
  lower_node := hlower.trans_le (le_trans (by norm_num) BstLean.Part250.noiselo.1)
  upper_node := hU.trans_lt hupper

end BstLean.Part271
