import BstLean.Part263WorldWindow

namespace BstLean.Part269
open Real BstLean.Part263

theorem endpoint13224_upper :
    BstLean.Part227.noiseUpper 13224 (202831 / 100000) <
      noiseNode (132831509352788689670147 / 250000000000000000000000) 53 := by
  have hs : √(12 / (13224 : ℝ)) ≤ (30125 / 1000000 : ℝ) :=
    sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part227.noiseUpper
  have hd : 0 < (1 - 2 * √(12 / (13224 : ℝ))) + (202831 / 100000 - 1) := by
    linarith
  apply (div_lt_iff₀ hd).mpr
  norm_num [noiseNode] at *
  nlinarith

noncomputable def endpointGrid13224 : Grid where
  top := 132831509352788689670147 / 250000000000000000000000
  worldLower := BstLean.Part227.noiseLower (202225 / 100000)
  worldUpper := BstLean.Part227.noiseUpper 13224 (202831 / 100000)
  top_pos := by norm_num
  lower_node := by
    apply lt_of_lt_of_le _ BstLean.Part250.noiselo.1
    norm_num [noiseNode]
  upper_node := endpoint13224_upper

end BstLean.Part269
