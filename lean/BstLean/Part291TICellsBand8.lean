import BstLean.Part291TICellsBase

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255

theorem lowTISupplyBand8 {n : ℕ} (hn : 8000 ≤ n) (j : Fin 160)
    (hj : 128 ≤ j.val ∧ j.val < 144) :
    LowTISupply n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j) := by
  by_cases h128 : j.val = 128
  · have hi := lowTISupply128 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h128] at hi ⊢
    exact hi
  by_cases h129 : j.val = 129
  · have hi := lowTISupply129 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h129] at hi ⊢
    exact hi
  by_cases h130 : j.val = 130
  · have hi := lowTISupply130 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h130] at hi ⊢
    exact hi
  by_cases h131 : j.val = 131
  · have hi := lowTISupply131 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h131] at hi ⊢
    exact hi
  by_cases h132 : j.val = 132
  · have hi := lowTISupply132 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h132] at hi ⊢
    exact hi
  by_cases h133 : j.val = 133
  · have hi := lowTISupply133 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h133] at hi ⊢
    exact hi
  by_cases h134 : j.val = 134
  · have hi := lowTISupply134 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h134] at hi ⊢
    exact hi
  by_cases h135 : j.val = 135
  · have hi := lowTISupply135 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h135] at hi ⊢
    exact hi
  by_cases h136 : j.val = 136
  · have hi := lowTISupply136 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h136] at hi ⊢
    exact hi
  by_cases h137 : j.val = 137
  · have hi := lowTISupply137 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h137] at hi ⊢
    exact hi
  by_cases h138 : j.val = 138
  · have hi := lowTISupply138 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h138] at hi ⊢
    exact hi
  by_cases h139 : j.val = 139
  · have hi := lowTISupply139 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h139] at hi ⊢
    exact hi
  by_cases h140 : j.val = 140
  · have hi := lowTISupply140 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h140] at hi ⊢
    exact hi
  by_cases h141 : j.val = 141
  · have hi := lowTISupply141 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h141] at hi ⊢
    exact hi
  by_cases h142 : j.val = 142
  · have hi := lowTISupply142 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h142] at hi ⊢
    exact hi
  by_cases h143 : j.val = 143
  · have hi := lowTISupply143 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h143] at hi ⊢
    exact hi
  · omega

end BstLean.BlueprintLow
