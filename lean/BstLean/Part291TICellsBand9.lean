import BstLean.Part291TICellsBase

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255

theorem lowTISupplyBand9 {n : ℕ} (hn : 8000 ≤ n) (j : Fin 160)
    (hj : 144 ≤ j.val ∧ j.val < 160) :
    LowTISupply n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j) := by
  by_cases h144 : j.val = 144
  · have hi := lowTISupply144 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h144] at hi ⊢
    exact hi
  by_cases h145 : j.val = 145
  · have hi := lowTISupply145 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h145] at hi ⊢
    exact hi
  by_cases h146 : j.val = 146
  · have hi := lowTISupply146 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h146] at hi ⊢
    exact hi
  by_cases h147 : j.val = 147
  · have hi := lowTISupply147 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h147] at hi ⊢
    exact hi
  by_cases h148 : j.val = 148
  · have hi := lowTISupply148 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h148] at hi ⊢
    exact hi
  by_cases h149 : j.val = 149
  · have hi := lowTISupply149 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h149] at hi ⊢
    exact hi
  by_cases h150 : j.val = 150
  · have hi := lowTISupply150 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h150] at hi ⊢
    exact hi
  by_cases h151 : j.val = 151
  · have hi := lowTISupply151 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h151] at hi ⊢
    exact hi
  by_cases h152 : j.val = 152
  · have hi := lowTISupply152 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h152] at hi ⊢
    exact hi
  by_cases h153 : j.val = 153
  · have hi := lowTISupply153 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h153] at hi ⊢
    exact hi
  by_cases h154 : j.val = 154
  · have hi := lowTISupply154 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h154] at hi ⊢
    exact hi
  by_cases h155 : j.val = 155
  · have hi := lowTISupply155 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h155] at hi ⊢
    exact hi
  by_cases h156 : j.val = 156
  · have hi := lowTISupply156 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h156] at hi ⊢
    exact hi
  by_cases h157 : j.val = 157
  · have hi := lowTISupply157 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h157] at hi ⊢
    exact hi
  by_cases h158 : j.val = 158
  · have hi := lowTISupply158 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h158] at hi ⊢
    exact hi
  by_cases h159 : j.val = 159
  · have hi := lowTISupply159 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h159] at hi ⊢
    exact hi
  · omega

end BstLean.BlueprintLow
