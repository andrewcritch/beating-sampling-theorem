import BstLean.Part291TICellsBase

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255

theorem lowTISupplyBand6 {n : ℕ} (hn : 8000 ≤ n) (j : Fin 160)
    (hj : 96 ≤ j.val ∧ j.val < 112) :
    LowTISupply n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j) := by
  by_cases h96 : j.val = 96
  · have hi := lowTISupply96 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h96] at hi ⊢
    exact hi
  by_cases h97 : j.val = 97
  · have hi := lowTISupply97 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h97] at hi ⊢
    exact hi
  by_cases h98 : j.val = 98
  · have hi := lowTISupply98 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h98] at hi ⊢
    exact hi
  by_cases h99 : j.val = 99
  · have hi := lowTISupply99 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h99] at hi ⊢
    exact hi
  by_cases h100 : j.val = 100
  · have hi := lowTISupply100 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h100] at hi ⊢
    exact hi
  by_cases h101 : j.val = 101
  · have hi := lowTISupply101 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h101] at hi ⊢
    exact hi
  by_cases h102 : j.val = 102
  · have hi := lowTISupply102 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h102] at hi ⊢
    exact hi
  by_cases h103 : j.val = 103
  · have hi := lowTISupply103 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h103] at hi ⊢
    exact hi
  by_cases h104 : j.val = 104
  · have hi := lowTISupply104 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h104] at hi ⊢
    exact hi
  by_cases h105 : j.val = 105
  · have hi := lowTISupply105 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h105] at hi ⊢
    exact hi
  by_cases h106 : j.val = 106
  · have hi := lowTISupply106 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h106] at hi ⊢
    exact hi
  by_cases h107 : j.val = 107
  · have hi := lowTISupply107 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h107] at hi ⊢
    exact hi
  by_cases h108 : j.val = 108
  · have hi := lowTISupply108 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h108] at hi ⊢
    exact hi
  by_cases h109 : j.val = 109
  · have hi := lowTISupply109 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h109] at hi ⊢
    exact hi
  by_cases h110 : j.val = 110
  · have hi := lowTISupply110 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h110] at hi ⊢
    exact hi
  by_cases h111 : j.val = 111
  · have hi := lowTISupply111 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h111] at hi ⊢
    exact hi
  · omega

end BstLean.BlueprintLow
