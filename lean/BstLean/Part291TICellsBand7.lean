import BstLean.Part291TICellsBase

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255

theorem lowTISupplyBand7 {n : ℕ} (hn : 8000 ≤ n) (j : Fin 160)
    (hj : 112 ≤ j.val ∧ j.val < 128) :
    LowTISupply n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j) := by
  by_cases h112 : j.val = 112
  · have hi := lowTISupply112 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h112] at hi ⊢
    exact hi
  by_cases h113 : j.val = 113
  · have hi := lowTISupply113 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h113] at hi ⊢
    exact hi
  by_cases h114 : j.val = 114
  · have hi := lowTISupply114 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h114] at hi ⊢
    exact hi
  by_cases h115 : j.val = 115
  · have hi := lowTISupply115 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h115] at hi ⊢
    exact hi
  by_cases h116 : j.val = 116
  · have hi := lowTISupply116 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h116] at hi ⊢
    exact hi
  by_cases h117 : j.val = 117
  · have hi := lowTISupply117 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h117] at hi ⊢
    exact hi
  by_cases h118 : j.val = 118
  · have hi := lowTISupply118 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h118] at hi ⊢
    exact hi
  by_cases h119 : j.val = 119
  · have hi := lowTISupply119 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h119] at hi ⊢
    exact hi
  by_cases h120 : j.val = 120
  · have hi := lowTISupply120 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h120] at hi ⊢
    exact hi
  by_cases h121 : j.val = 121
  · have hi := lowTISupply121 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h121] at hi ⊢
    exact hi
  by_cases h122 : j.val = 122
  · have hi := lowTISupply122 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h122] at hi ⊢
    exact hi
  by_cases h123 : j.val = 123
  · have hi := lowTISupply123 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h123] at hi ⊢
    exact hi
  by_cases h124 : j.val = 124
  · have hi := lowTISupply124 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h124] at hi ⊢
    exact hi
  by_cases h125 : j.val = 125
  · have hi := lowTISupply125 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h125] at hi ⊢
    exact hi
  by_cases h126 : j.val = 126
  · have hi := lowTISupply126 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h126] at hi ⊢
    exact hi
  by_cases h127 : j.val = 127
  · have hi := lowTISupply127 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h127] at hi ⊢
    exact hi
  · omega

end BstLean.BlueprintLow
