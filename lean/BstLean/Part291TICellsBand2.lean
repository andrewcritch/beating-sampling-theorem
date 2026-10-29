import BstLean.Part291TICellsBase

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255

theorem lowTISupplyBand2 {n : ℕ} (hn : 8000 ≤ n) (j : Fin 160)
    (hj : 32 ≤ j.val ∧ j.val < 48) :
    LowTISupply n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j) := by
  by_cases h32 : j.val = 32
  · have hi := lowTISupply32 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h32] at hi ⊢
    exact hi
  by_cases h33 : j.val = 33
  · have hi := lowTISupply33 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h33] at hi ⊢
    exact hi
  by_cases h34 : j.val = 34
  · have hi := lowTISupply34 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h34] at hi ⊢
    exact hi
  by_cases h35 : j.val = 35
  · have hi := lowTISupply35 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h35] at hi ⊢
    exact hi
  by_cases h36 : j.val = 36
  · have hi := lowTISupply36 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h36] at hi ⊢
    exact hi
  by_cases h37 : j.val = 37
  · have hi := lowTISupply37 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h37] at hi ⊢
    exact hi
  by_cases h38 : j.val = 38
  · have hi := lowTISupply38 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h38] at hi ⊢
    exact hi
  by_cases h39 : j.val = 39
  · have hi := lowTISupply39 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h39] at hi ⊢
    exact hi
  by_cases h40 : j.val = 40
  · have hi := lowTISupply40 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h40] at hi ⊢
    exact hi
  by_cases h41 : j.val = 41
  · have hi := lowTISupply41 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h41] at hi ⊢
    exact hi
  by_cases h42 : j.val = 42
  · have hi := lowTISupply42 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h42] at hi ⊢
    exact hi
  by_cases h43 : j.val = 43
  · have hi := lowTISupply43 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h43] at hi ⊢
    exact hi
  by_cases h44 : j.val = 44
  · have hi := lowTISupply44 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h44] at hi ⊢
    exact hi
  by_cases h45 : j.val = 45
  · have hi := lowTISupply45 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h45] at hi ⊢
    exact hi
  by_cases h46 : j.val = 46
  · have hi := lowTISupply46 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h46] at hi ⊢
    exact hi
  by_cases h47 : j.val = 47
  · have hi := lowTISupply47 hn
    norm_num [lowTIParameters, lowTIParametersBatch0, lowTIParametersBatch1, lowTIParametersBatch2, lowTIParametersBatch3, lowTIParametersBatch4, lowTIParametersBatch5, lowTIParametersBatch6, lowTIParametersBatch7, lowTIParametersBatch8, lowTIParametersBatch9, frameNoiseLower, frameNoiseUpper, h47] at hi ⊢
    exact hi
  · omega

end BstLean.BlueprintLow
