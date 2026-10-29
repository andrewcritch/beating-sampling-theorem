import BstLean.Part271R4TableShared
import BstLean.Part271R4TableTransfer

namespace BstLean.Part271.R4.SharedTable
open Real Set BstLean.Part263

theorem containment (top : ℝ) (htop : top ∈ Icc (105958839397/200000000000) (21253017353/40000000000))
    (i : Fin 60) : (table i).lower ≤ noiseNode top i.val ∧
      noiseNode top (i.val+1) ≤ (table i).upper := by
  fin_cases i <;> norm_num [table,noiseNode]
  all_goals try constructor
  all_goals linarith only [htop.1,htop.2]

end BstLean.Part271.R4.SharedTable
