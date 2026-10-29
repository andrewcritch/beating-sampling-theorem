import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13050 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13050. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13050 : WorldParameters where
  hiddenCharge := (578725287 / 500000000000 : ℝ)
  frame := (620913662459 / 1000000000000 : ℝ)
  moment := (2196439499 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13050 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182830623747 / 125000000000 : ℝ)
    root := (2067174373 / 250000000000 : ℝ) }

noncomputable def scalar13050 : ScalarCertificate 13050 world13050 agent13050 where
  dimensionLo := 13050
  dimensionHi := 13050
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2307266899 / 1000000000000 : ℝ)
  frameLo := (620913662459 / 1000000000000 : ℝ)
  frameHi := (182830623747 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13050]
  agentFrame_pos := by norm_num only [agent13050]
  worldRadius := (2307266899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13050]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (270824013 / 250000000000 : ℝ)
  lowerTail := (1045079 / 800000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (69966199 / 10000000000 : ℝ)
  ledger := by
    have h : (578725287 / 500000000000 : ℚ) +
        (2196439499 / 250000000000000000 : ℚ) / (2307266899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (270824013 / 250000000000 : ℚ) + (1045079 / 800000000 : ℚ) ≤
        (69966199 / 10000000000 : ℚ) := by norm_num only
    have hc : (((578725287 / 500000000000 : ℚ) +
        (2196439499 / 250000000000000000 : ℚ) / (2307266899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (270824013 / 250000000000 : ℚ) + (1045079 / 800000000 : ℚ) : ℚ) : ℝ) ≤
        ((69966199 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13050]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13050 :
    2 * 160 < 13050 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999239 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13050 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13051 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13051. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13051 : WorldParameters where
  hiddenCharge := (1157410779 / 1000000000000 : ℝ)
  frame := (620900564141 / 1000000000000 : ℝ)
  moment := (8784000561 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13051 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365654029421 / 250000000000 : ℝ)
    root := (516755101 / 62500000000 : ℝ) }

noncomputable def scalar13051 : ScalarCertificate 13051 world13051 agent13051 where
  dimensionLo := 13051
  dimensionHi := 13051
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2307630199 / 1000000000000 : ℝ)
  frameLo := (620900564141 / 1000000000000 : ℝ)
  frameHi := (365654029421 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13051]
  agentFrame_pos := by norm_num only [agent13051]
  worldRadius := (2307630199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13051]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1082414811 / 1000000000000 : ℝ)
  lowerTail := (163170277 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3496931347 / 500000000000 : ℝ)
  ledger := by
    have h : (1157410779 / 1000000000000 : ℚ) +
        (8784000561 / 1000000000000000000 : ℚ) / (2307630199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1082414811 / 1000000000000 : ℚ) + (163170277 / 125000000000 : ℚ) ≤
        (3496931347 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1157410779 / 1000000000000 : ℚ) +
        (8784000561 / 1000000000000000000 : ℚ) / (2307630199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1082414811 / 1000000000000 : ℚ) + (163170277 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3496931347 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13051]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13051 :
    2 * 160 < 13051 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999881 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13051 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13052 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13052. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13052 : WorldParameters where
  hiddenCharge := (231474199 / 200000000000 : ℝ)
  frame := (38805466741 / 62500000000 : ℝ)
  moment := (4391121809 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13052 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462587262897 / 1000000000000 : ℝ)
    root := (8267465847 / 1000000000000 : ℝ) }

noncomputable def scalar13052 : ScalarCertificate 13052 world13052 agent13052 where
  dimensionLo := 13052
  dimensionHi := 13052
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2307993599 / 1000000000000 : ℝ)
  frameLo := (38805466741 / 62500000000 : ℝ)
  frameHi := (1462587262897 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13052]
  agentFrame_pos := by norm_num only [agent13052]
  worldRadius := (2307993599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13052]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1081534433 / 1000000000000 : ℝ)
  lowerTail := (1304376599 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6991107681 / 1000000000000 : ℝ)
  ledger := by
    have h : (231474199 / 200000000000 : ℚ) +
        (4391121809 / 500000000000000000 : ℚ) / (2307993599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1081534433 / 1000000000000 : ℚ) + (1304376599 / 1000000000000 : ℚ) ≤
        (6991107681 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((231474199 / 200000000000 : ℚ) +
        (4391121809 / 500000000000000000 : ℚ) / (2307993599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1081534433 / 1000000000000 : ℚ) + (1304376599 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6991107681 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13052]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13052 :
    2 * 160 < 13052 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999023 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13052 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13053 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13053. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13053 : WorldParameters where
  hiddenCharge := (1157331221 / 1000000000000 : ℝ)
  frame := (155218593401 / 250000000000 : ℝ)
  moment := (1756097433 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13053 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462558425607 / 1000000000000 : ℝ)
    root := (8266850311 / 1000000000000 : ℝ) }

noncomputable def scalar13053 : ScalarCertificate 13053 world13053 agent13053 where
  dimensionLo := 13053
  dimensionHi := 13053
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2308356899 / 1000000000000 : ℝ)
  frameLo := (155218593401 / 250000000000 : ℝ)
  frameHi := (1462558425607 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13053]
  agentFrame_pos := by norm_num only [agent13053]
  worldRadius := (2308356899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13053]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (67540929 / 62500000000 : ℝ)
  lowerTail := (651695917 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1747088757 / 250000000000 : ℝ)
  ledger := by
    have h : (1157331221 / 1000000000000 : ℚ) +
        (1756097433 / 200000000000000000 : ℚ) / (2308356899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67540929 / 62500000000 : ℚ) + (651695917 / 500000000000 : ℚ) ≤
        (1747088757 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1157331221 / 1000000000000 : ℚ) +
        (1756097433 / 200000000000000000 : ℚ) / (2308356899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67540929 / 62500000000 : ℚ) + (651695917 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1747088757 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13053]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13053 :
    2 * 160 < 13053 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995429 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13053 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13054 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13054. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13054 : WorldParameters where
  hiddenCharge := (1157291457 / 1000000000000 : ℝ)
  frame := (77607660173 / 125000000000 : ℝ)
  moment := (2194682801 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13054 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731264799981 / 500000000000 : ℝ)
    root := (2066558721 / 250000000000 : ℝ) }

noncomputable def scalar13054 : ScalarCertificate 13054 world13054 agent13054 where
  dimensionLo := 13054
  dimensionHi := 13054
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2308720399 / 1000000000000 : ℝ)
  frameLo := (77607660173 / 125000000000 : ℝ)
  frameHi := (731264799981 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13054]
  agentFrame_pos := by norm_num only [agent13054]
  worldRadius := (2308720399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13054]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1079776203 / 1000000000000 : ℝ)
  lowerTail := (1302408033 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1746401129 / 250000000000 : ℝ)
  ledger := by
    have h : (1157291457 / 1000000000000 : ℚ) +
        (2194682801 / 250000000000000000 : ℚ) / (2308720399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1079776203 / 1000000000000 : ℚ) + (1302408033 / 1000000000000 : ℚ) ≤
        (1746401129 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1157291457 / 1000000000000 : ℚ) +
        (2194682801 / 250000000000000000 : ℚ) / (2308720399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1079776203 / 1000000000000 : ℚ) + (1302408033 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1746401129 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13054]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13054 :
    2 * 160 < 13054 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (12499993 / 1250000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13054 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13055 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13055. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13055 : WorldParameters where
  hiddenCharge := (144656463 / 125000000000 : ℝ)
  frame := (124169638239 / 200000000000 : ℝ)
  moment := (8776975733 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13055 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462500785957 / 1000000000000 : ℝ)
    root := (8265619689 / 1000000000000 : ℝ) }

noncomputable def scalar13055 : ScalarCertificate 13055 world13055 agent13055 where
  dimensionLo := 13055
  dimensionHi := 13055
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2309083599 / 1000000000000 : ℝ)
  frameLo := (124169638239 / 200000000000 : ℝ)
  frameHi := (1462500785957 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13055]
  agentFrame_pos := by norm_num only [agent13055]
  worldRadius := (2309083599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13055]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (215779639 / 200000000000 : ℝ)
  lowerTail := (650712453 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6982856313 / 1000000000000 : ℝ)
  ledger := by
    have h : (144656463 / 125000000000 : ℚ) +
        (8776975733 / 1000000000000000000 : ℚ) / (2309083599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (215779639 / 200000000000 : ℚ) + (650712453 / 500000000000 : ℚ) ≤
        (6982856313 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((144656463 / 125000000000 : ℚ) +
        (8776975733 / 1000000000000000000 : ℚ) / (2309083599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (215779639 / 200000000000 : ℚ) + (650712453 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6982856313 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13055]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13055 :
    2 * 160 < 13055 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995917 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13055 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13056 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13056. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13056 : WorldParameters where
  hiddenCharge := (28930299 / 25000000000 : ℝ)
  frame := (310417551519 / 500000000000 : ℝ)
  moment := (8775220753 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13056 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (45702249487 / 31250000000 : ℝ)
    root := (1033125583 / 125000000000 : ℝ) }

noncomputable def scalar13056 : ScalarCertificate 13056 world13056 agent13056 where
  dimensionLo := 13056
  dimensionHi := 13056
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2309447099 / 1000000000000 : ℝ)
  frameLo := (310417551519 / 500000000000 : ℝ)
  frameHi := (45702249487 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13056]
  agentFrame_pos := by norm_num only [agent13056]
  worldRadius := (2309447099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13056]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1078021201 / 1000000000000 : ℝ)
  lowerTail := (1300442861 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6980110331 / 1000000000000 : ℝ)
  ledger := by
    have h : (28930299 / 25000000000 : ℚ) +
        (8775220753 / 1000000000000000000 : ℚ) / (2309447099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1078021201 / 1000000000000 : ℚ) + (1300442861 / 1000000000000 : ℚ) ≤
        (6980110331 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((28930299 / 25000000000 : ℚ) +
        (8775220753 / 1000000000000000000 : ℚ) / (2309447099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1078021201 / 1000000000000 : ℚ) + (1300442861 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6980110331 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13056]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13056 :
    2 * 160 < 13056 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999991 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13056 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13057 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13057. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13057 : WorldParameters where
  hiddenCharge := (1157172227 / 1000000000000 : ℝ)
  frame := (38801376057 / 62500000000 : ℝ)
  moment := (8773466263 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13057 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462443204529 / 1000000000000 : ℝ)
    root := (4132194873 / 500000000000 : ℝ) }

noncomputable def scalar13057 : ScalarCertificate 13057 world13057 agent13057 where
  dimensionLo := 13057
  dimensionHi := 13057
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2309810499 / 1000000000000 : ℝ)
  frameLo := (38801376057 / 62500000000 : ℝ)
  frameHi := (1462443204529 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13057]
  agentFrame_pos := by norm_num only [agent13057]
  worldRadius := (2309810499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13057]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (21542899 / 20000000000 : ℝ)
  lowerTail := (1299461603 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6977366577 / 1000000000000 : ℝ)
  ledger := by
    have h : (1157172227 / 1000000000000 : ℚ) +
        (8773466263 / 1000000000000000000 : ℚ) / (2309810499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (21542899 / 20000000000 : ℚ) + (1299461603 / 1000000000000 : ℚ) ≤
        (6977366577 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1157172227 / 1000000000000 : ℚ) +
        (8773466263 / 1000000000000000000 : ℚ) / (2309810499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (21542899 / 20000000000 : ℚ) + (1299461603 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6977366577 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13057]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13057 :
    2 * 160 < 13057 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995153 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13057 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13058 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13058. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13058 : WorldParameters where
  hiddenCharge := (144641563 / 125000000000 : ℝ)
  frame := (38800558301 / 62500000000 : ℝ)
  moment := (1096464033 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13058 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91400901953 / 62500000000 : ℝ)
    root := (8263775061 / 1000000000000 : ℝ) }

noncomputable def scalar13058 : ScalarCertificate 13058 world13058 agent13058 where
  dimensionLo := 13058
  dimensionHi := 13058
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2310173899 / 1000000000000 : ℝ)
  frameLo := (38800558301 / 62500000000 : ℝ)
  frameHi := (91400901953 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13058]
  agentFrame_pos := by norm_num only [agent13058]
  worldRadius := (2310173899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13058]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1076269531 / 1000000000000 : ℝ)
  lowerTail := (20288769 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6974625079 / 1000000000000 : ℝ)
  ledger := by
    have h : (144641563 / 125000000000 : ℚ) +
        (1096464033 / 125000000000000000 : ℚ) / (2310173899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1076269531 / 1000000000000 : ℚ) + (20288769 / 15625000000 : ℚ) ≤
        (6974625079 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((144641563 / 125000000000 : ℚ) +
        (1096464033 / 125000000000000000 : ℚ) / (2310173899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1076269531 / 1000000000000 : ℚ) + (20288769 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((6974625079 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13058]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13058 :
    2 * 160 < 13058 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999629 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13058 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13059 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13059. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13059 : WorldParameters where
  hiddenCharge := (144636599 / 125000000000 : ℝ)
  frame := (620795850749 / 1000000000000 : ℝ)
  moment := (4384979377 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13059 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462385675427 / 1000000000000 : ℝ)
    root := (2065790121 / 250000000000 : ℝ) }

noncomputable def scalar13059 : ScalarCertificate 13059 world13059 agent13059 where
  dimensionLo := 13059
  dimensionHi := 13059
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2310537299 / 1000000000000 : ℝ)
  frameLo := (620795850749 / 1000000000000 : ℝ)
  frameHi := (1462385675427 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13059]
  agentFrame_pos := by norm_num only [agent13059]
  worldRadius := (2310537299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13059]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1075394901 / 1000000000000 : ℝ)
  lowerTail := (259500333 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6971885759 / 1000000000000 : ℝ)
  ledger := by
    have h : (144636599 / 125000000000 : ℚ) +
        (4384979377 / 500000000000000000 : ℚ) / (2310537299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1075394901 / 1000000000000 : ℚ) + (259500333 / 200000000000 : ℚ) ≤
        (6971885759 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((144636599 / 125000000000 : ℚ) +
        (4384979377 / 500000000000000000 : ℚ) / (2310537299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1075394901 / 1000000000000 : ℚ) + (259500333 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6971885759 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13059]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13059 :
    2 * 160 < 13059 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999733 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13059 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13060 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13060. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13060 : WorldParameters where
  hiddenCharge := (1157053089 / 1000000000000 : ℝ)
  frame := (77597846339 / 125000000000 : ℝ)
  moment := (4384102867 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13060 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29245592213 / 20000000000 : ℝ)
    root := (8262546139 / 1000000000000 : ℝ) }

noncomputable def scalar13060 : ScalarCertificate 13060 world13060 agent13060 where
  dimensionLo := 13060
  dimensionHi := 13060
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2311017599 / 1000000000000 : ℝ)
  frameLo := (77597846339 / 125000000000 : ℝ)
  frameHi := (29245592213 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13060]
  agentFrame_pos := by norm_num only [agent13060]
  worldRadius := (2311017599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13060]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1074332163 / 1000000000000 : ℝ)
  lowerTail := (129627407 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (217767023 / 31250000000 : ℝ)
  ledger := by
    have h : (1157053089 / 1000000000000 : ℚ) +
        (4384102867 / 500000000000000000 : ℚ) / (2311017599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1074332163 / 1000000000000 : ℚ) + (129627407 / 100000000000 : ℚ) ≤
        (217767023 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1157053089 / 1000000000000 : ℚ) +
        (4384102867 / 500000000000000000 : ℚ) / (2311017599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1074332163 / 1000000000000 : ℚ) + (129627407 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((217767023 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13060]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13060 :
    2 * 160 < 13060 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995577 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13060 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13061 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13061. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13061 : WorldParameters where
  hiddenCharge := (1157013397 / 1000000000000 : ℝ)
  frame := (19399052897 / 31250000000 : ℝ)
  moment := (2191613301 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13061 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731125442371 / 500000000000 : ℝ)
    root := (8261931963 / 1000000000000 : ℝ) }

noncomputable def scalar13061 : ScalarCertificate 13061 world13061 agent13061 where
  dimensionLo := 13061
  dimensionHi := 13061
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2311381099 / 1000000000000 : ℝ)
  frameLo := (19399052897 / 31250000000 : ℝ)
  frameHi := (731125442371 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13061]
  agentFrame_pos := by norm_num only [agent13061]
  worldRadius := (2311381099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13061]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1073459407 / 1000000000000 : ℝ)
  lowerTail := (1295296521 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1741452591 / 250000000000 : ℝ)
  ledger := by
    have h : (1157013397 / 1000000000000 : ℚ) +
        (2191613301 / 250000000000000000 : ℚ) / (2311381099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1073459407 / 1000000000000 : ℚ) + (1295296521 / 1000000000000 : ℚ) ≤
        (1741452591 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1157013397 / 1000000000000 : ℚ) +
        (2191613301 / 250000000000000000 : ℚ) / (2311381099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1073459407 / 1000000000000 : ℚ) + (1295296521 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1741452591 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13061]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13061 :
    2 * 160 < 13061 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994921 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13061 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13062 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13062. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13062 : WorldParameters where
  hiddenCharge := (231394743 / 200000000000 : ℝ)
  frame := (620756616723 / 1000000000000 : ℝ)
  moment := (8764701163 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13062 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462222170429 / 1000000000000 : ℝ)
    root := (4130658947 / 500000000000 : ℝ) }

noncomputable def scalar13062 : ScalarCertificate 13062 world13062 agent13062 where
  dimensionLo := 13062
  dimensionHi := 13062
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2311744499 / 1000000000000 : ℝ)
  frameLo := (620756616723 / 1000000000000 : ℝ)
  frameHi := (1462222170429 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13062]
  agentFrame_pos := by norm_num only [agent13062]
  worldRadius := (2311744499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13062]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (268146837 / 250000000000 : ℝ)
  lowerTail := (258863941 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3481539059 / 500000000000 : ℝ)
  ledger := by
    have h : (231394743 / 200000000000 : ℚ) +
        (8764701163 / 1000000000000000000 : ℚ) / (2311744499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (268146837 / 250000000000 : ℚ) + (258863941 / 200000000000 : ℚ) ≤
        (3481539059 / 500000000000 : ℚ) := by norm_num only
    have hc : (((231394743 / 200000000000 : ℚ) +
        (8764701163 / 1000000000000000000 : ℚ) / (2311744499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (268146837 / 250000000000 : ℚ) + (258863941 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3481539059 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13062]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13062 :
    2 * 160 < 13062 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996681 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13062 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13063 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13063. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13063 : WorldParameters where
  hiddenCharge := (1156934043 / 1000000000000 : ℝ)
  frame := (620743542771 / 1000000000000 : ℝ)
  moment := (2190737403 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13063 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365548368387 / 250000000000 : ℝ)
    root := (4130352029 / 500000000000 : ℝ) }

noncomputable def scalar13063 : ScalarCertificate 13063 world13063 agent13063 where
  dimensionLo := 13063
  dimensionHi := 13063
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2312107799 / 1000000000000 : ℝ)
  frameLo := (620743542771 / 1000000000000 : ℝ)
  frameHi := (365548368387 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13063]
  agentFrame_pos := by norm_num only [agent13063]
  worldRadius := (2312107799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13063]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1071716091 / 1000000000000 : ℝ)
  lowerTail := (1293343731 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (435021763 / 62500000000 : ℝ)
  ledger := by
    have h : (1156934043 / 1000000000000 : ℚ) +
        (2190737403 / 250000000000000000 : ℚ) / (2312107799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1071716091 / 1000000000000 : ℚ) + (1293343731 / 1000000000000 : ℚ) ≤
        (435021763 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1156934043 / 1000000000000 : ℚ) +
        (2190737403 / 250000000000000000 : ℚ) / (2312107799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1071716091 / 1000000000000 : ℚ) + (1293343731 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((435021763 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13063]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13063 :
    2 * 160 < 13063 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995143 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13063 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13064 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13064. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13064 : WorldParameters where
  hiddenCharge := (578447191 / 500000000000 : ℝ)
  frame := (124146094169 / 200000000000 : ℝ)
  moment := (8761198549 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13064 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462164788251 / 1000000000000 : ℝ)
    root := (1032511291 / 125000000000 : ℝ) }

noncomputable def scalar13064 : ScalarCertificate 13064 world13064 agent13064 where
  dimensionLo := 13064
  dimensionHi := 13064
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2312471399 / 1000000000000 : ℝ)
  frameLo := (124146094169 / 200000000000 : ℝ)
  frameHi := (1462164788251 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13064]
  agentFrame_pos := by norm_num only [agent13064]
  worldRadius := (2312471399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13064]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1070845799 / 1000000000000 : ℝ)
  lowerTail := (1292368787 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3478810209 / 500000000000 : ℝ)
  ledger := by
    have h : (578447191 / 500000000000 : ℚ) +
        (8761198549 / 1000000000000000000 : ℚ) / (2312471399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1070845799 / 1000000000000 : ℚ) + (1292368787 / 1000000000000 : ℚ) ≤
        (3478810209 / 500000000000 : ℚ) := by norm_num only
    have hc : (((578447191 / 500000000000 : ℚ) +
        (8761198549 / 1000000000000000000 : ℚ) / (2312471399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1070845799 / 1000000000000 : ℚ) + (1292368787 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3478810209 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13064]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13064 :
    2 * 160 < 13064 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995983 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13064 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13065 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13065. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13065 : WorldParameters where
  hiddenCharge := (115685473 / 100000000000 : ℝ)
  frame := (620717400947 / 1000000000000 : ℝ)
  moment := (1094930997 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13065 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146213611453 / 100000000000 : ℝ)
    root := (825947683 / 100000000000 : ℝ) }

noncomputable def scalar13065 : ScalarCertificate 13065 world13065 agent13065 where
  dimensionLo := 13065
  dimensionHi := 13065
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2312834799 / 1000000000000 : ℝ)
  frameLo := (620717400947 / 1000000000000 : ℝ)
  frameHi := (146213611453 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13065]
  agentFrame_pos := by norm_num only [agent13065]
  worldRadius := (2312834799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13065]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (534988109 / 500000000000 : ℝ)
  lowerTail := (258278917 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3477447457 / 500000000000 : ℝ)
  ledger := by
    have h : (115685473 / 100000000000 : ℚ) +
        (1094930997 / 125000000000000000 : ℚ) / (2312834799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (534988109 / 500000000000 : ℚ) + (258278917 / 200000000000 : ℚ) ≤
        (3477447457 / 500000000000 : ℚ) := by norm_num only
    have hc : (((115685473 / 100000000000 : ℚ) +
        (1094930997 / 125000000000000000 : ℚ) / (2312834799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (534988109 / 500000000000 : ℚ) + (258278917 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3477447457 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13065]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13065 :
    2 * 160 < 13065 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999591 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13065 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13066 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13066. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13066 : WorldParameters where
  hiddenCharge := (1156815089 / 1000000000000 : ℝ)
  frame := (310352166537 / 500000000000 : ℝ)
  moment := (8757697891 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13066 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462107458223 / 1000000000000 : ℝ)
    root := (4129431719 / 500000000000 : ℝ) }

noncomputable def scalar13066 : ScalarCertificate 13066 world13066 agent13066 where
  dimensionLo := 13066
  dimensionHi := 13066
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2313198299 / 1000000000000 : ℝ)
  frameLo := (310352166537 / 500000000000 : ℝ)
  frameHi := (1462107458223 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13066]
  agentFrame_pos := by norm_num only [agent13066]
  worldRadius := (2313198299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13066]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1069107487 / 1000000000000 : ℝ)
  lowerTail := (645210643 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6952171573 / 1000000000000 : ℝ)
  ledger := by
    have h : (1156815089 / 1000000000000 : ℚ) +
        (8757697891 / 1000000000000000000 : ℚ) / (2313198299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1069107487 / 1000000000000 : ℚ) + (645210643 / 500000000000 : ℚ) ≤
        (6952171573 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1156815089 / 1000000000000 : ℚ) +
        (8757697891 / 1000000000000000000 : ℚ) / (2313198299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1069107487 / 1000000000000 : ℚ) + (645210643 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6952171573 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13066]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13066 :
    2 * 160 < 13066 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (399999961 / 40000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13066 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13067 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13067. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13067 : WorldParameters where
  hiddenCharge := (578387729 / 500000000000 : ℝ)
  frame := (620691267227 / 1000000000000 : ℝ)
  moment := (1751189659 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13067 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462078819323 / 1000000000000 : ℝ)
    root := (8258250279 / 1000000000000 : ℝ) }

noncomputable def scalar13067 : ScalarCertificate 13067 world13067 agent13067 where
  dimensionLo := 13067
  dimensionHi := 13067
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2313561699 / 1000000000000 : ℝ)
  frameLo := (620691267227 / 1000000000000 : ℝ)
  frameHi := (1462078819323 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13067]
  agentFrame_pos := by norm_num only [agent13067]
  worldRadius := (2313561699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13067]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1068239553 / 1000000000000 : ℝ)
  lowerTail := (644724413 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6949450559 / 1000000000000 : ℝ)
  ledger := by
    have h : (578387729 / 500000000000 : ℚ) +
        (1751189659 / 200000000000000000 : ℚ) / (2313561699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1068239553 / 1000000000000 : ℚ) + (644724413 / 500000000000 : ℚ) ≤
        (6949450559 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578387729 / 500000000000 : ℚ) +
        (1751189659 / 200000000000000000 : ℚ) / (2313561699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1068239553 / 1000000000000 : ℚ) + (644724413 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6949450559 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13067]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13067 :
    2 * 160 < 13067 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995489 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13067 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13068 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13068. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13068 : WorldParameters where
  hiddenCharge := (1156735837 / 1000000000000 : ℝ)
  frame := (310339101703 / 500000000000 : ℝ)
  moment := (2188549797 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13068 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731025093069 / 500000000000 : ℝ)
    root := (330305489 / 40000000000 : ℝ) }

noncomputable def scalar13068 : ScalarCertificate 13068 world13068 agent13068 where
  dimensionLo := 13068
  dimensionHi := 13068
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2313925299 / 1000000000000 : ℝ)
  frameLo := (310339101703 / 500000000000 : ℝ)
  frameHi := (731025093069 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13068]
  agentFrame_pos := by norm_num only [agent13068]
  worldRadius := (2313925299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13068]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (533686247 / 500000000000 : ℝ)
  lowerTail := (644238647 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1736682903 / 250000000000 : ℝ)
  ledger := by
    have h : (1156735837 / 1000000000000 : ℚ) +
        (2188549797 / 250000000000000000 : ℚ) / (2313925299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (533686247 / 500000000000 : ℚ) + (644238647 / 500000000000 : ℚ) ≤
        (1736682903 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1156735837 / 1000000000000 : ℚ) +
        (2188549797 / 250000000000000000 : ℚ) / (2313925299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (533686247 / 500000000000 : ℚ) + (644238647 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1736682903 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13068]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13068 :
    2 * 160 < 13068 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999979 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13068 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13069 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13069. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13069 : WorldParameters where
  hiddenCharge := (578348113 / 500000000000 : ℝ)
  frame := (620665141609 / 1000000000000 : ℝ)
  moment := (1094056321 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13069 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462021576191 / 1000000000000 : ℝ)
    root := (8257024403 / 1000000000000 : ℝ) }

noncomputable def scalar13069 : ScalarCertificate 13069 world13069 agent13069 where
  dimensionLo := 13069
  dimensionHi := 13069
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2314288699 / 1000000000000 : ℝ)
  frameLo := (620665141609 / 1000000000000 : ℝ)
  frameHi := (1462021576191 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13069]
  agentFrame_pos := by norm_num only [agent13069]
  worldRadius := (2314288699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13069]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1066506183 / 1000000000000 : ℝ)
  lowerTail := (321876637 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6944015033 / 1000000000000 : ℝ)
  ledger := by
    have h : (578348113 / 500000000000 : ℚ) +
        (1094056321 / 125000000000000000 : ℚ) / (2314288699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1066506183 / 1000000000000 : ℚ) + (321876637 / 250000000000 : ℚ) ≤
        (6944015033 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578348113 / 500000000000 : ℚ) +
        (1094056321 / 125000000000000000 : ℚ) / (2314288699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1066506183 / 1000000000000 : ℚ) + (321876637 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6944015033 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13069]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13069 :
    2 * 160 < 13069 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997653 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13069 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13070 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13070. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13070 : WorldParameters where
  hiddenCharge := (578328313 / 500000000000 : ℝ)
  frame := (155163020459 / 250000000000 : ℝ)
  moment := (8750702437 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13070 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730957876881 / 500000000000 : ℝ)
    root := (33025647 / 4000000000 : ℝ) }

noncomputable def scalar13070 : ScalarCertificate 13070 world13070 agent13070 where
  dimensionLo := 13070
  dimensionHi := 13070
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2314769299 / 1000000000000 : ℝ)
  frameLo := (155163020459 / 250000000000 : ℝ)
  frameHi := (730957876881 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13070]
  agentFrame_pos := by norm_num only [agent13070]
  worldRadius := (2314769299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13070]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1065453509 / 1000000000000 : ℝ)
  lowerTail := (321572473 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6940701337 / 1000000000000 : ℝ)
  ledger := by
    have h : (578328313 / 500000000000 : ℚ) +
        (8750702437 / 1000000000000000000 : ℚ) / (2314769299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1065453509 / 1000000000000 : ℚ) + (321572473 / 250000000000 : ℚ) ≤
        (6940701337 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578328313 / 500000000000 : ℚ) +
        (8750702437 / 1000000000000000000 : ℚ) / (2314769299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1065453509 / 1000000000000 : ℚ) + (321572473 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6940701337 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13070]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13070 :
    2 * 160 < 13070 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999313 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13070 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13071 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13071. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13071 : WorldParameters where
  hiddenCharge := (289154259 / 250000000000 : ℝ)
  frame := (620639024087 / 1000000000000 : ℝ)
  moment := (4374477397 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13071 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1461887167753 / 1000000000000 : ℝ)
    root := (8255799203 / 1000000000000 : ℝ) }

noncomputable def scalar13071 : ScalarCertificate 13071 world13071 agent13071 where
  dimensionLo := 13071
  dimensionHi := 13071
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2315132899 / 1000000000000 : ℝ)
  frameLo := (620639024087 / 1000000000000 : ℝ)
  frameHi := (1461887167753 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13071]
  agentFrame_pos := by norm_num only [agent13071]
  worldRadius := (2315132899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13071]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (133073627 / 125000000000 : ℝ)
  lowerTail := (642660547 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (867248681 / 125000000000 : ℝ)
  ledger := by
    have h : (289154259 / 250000000000 : ℚ) +
        (4374477397 / 500000000000000000 : ℚ) / (2315132899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (133073627 / 125000000000 : ℚ) + (642660547 / 500000000000 : ℚ) ≤
        (867248681 / 125000000000 : ℚ) := by norm_num only
    have hc : (((289154259 / 250000000000 : ℚ) +
        (4374477397 / 500000000000000000 : ℚ) / (2315132899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (133073627 / 125000000000 : ℚ) + (642660547 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((867248681 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13071]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13071 :
    2 * 160 < 13071 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999849 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13071 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13072 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13072. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13072 : WorldParameters where
  hiddenCharge := (231315491 / 200000000000 : ℝ)
  frame := (620625968361 / 1000000000000 : ℝ)
  moment := (4373603819 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13072 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (18273232489 / 12500000000 : ℝ)
    root := (4127593443 / 500000000000 : ℝ) }

noncomputable def scalar13072 : ScalarCertificate 13072 world13072 agent13072 where
  dimensionLo := 13072
  dimensionHi := 13072
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2315496399 / 1000000000000 : ℝ)
  frameLo := (620625968361 / 1000000000000 : ℝ)
  frameHi := (18273232489 / 12500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13072]
  agentFrame_pos := by norm_num only [agent13072]
  worldRadius := (2315496399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13072]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (265931329 / 250000000000 : ℝ)
  lowerTail := (128435313 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3467639937 / 500000000000 : ℝ)
  ledger := by
    have h : (231315491 / 200000000000 : ℚ) +
        (4373603819 / 500000000000000000 : ℚ) / (2315496399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265931329 / 250000000000 : ℚ) + (128435313 / 100000000000 : ℚ) ≤
        (3467639937 / 500000000000 : ℚ) := by norm_num only
    have hc : (((231315491 / 200000000000 : ℚ) +
        (4373603819 / 500000000000000000 : ℚ) / (2315496399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265931329 / 250000000000 : ℚ) + (128435313 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3467639937 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13072]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13072 :
    2 * 160 < 13072 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997437 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13072 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13073 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13073. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13073 : WorldParameters where
  hiddenCharge := (231307577 / 200000000000 : ℝ)
  frame := (310306457329 / 500000000000 : ℝ)
  moment := (874546097 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13073 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1461830036171 / 1000000000000 : ℝ)
    root := (2063643669 / 250000000000 : ℝ) }

noncomputable def scalar13073 : ScalarCertificate 13073 world13073 agent13073 where
  dimensionLo := 13073
  dimensionHi := 13073
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2315859899 / 1000000000000 : ℝ)
  frameLo := (310306457329 / 500000000000 : ℝ)
  frameHi := (1461830036171 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13073]
  agentFrame_pos := by norm_num only [agent13073]
  worldRadius := (2315859899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13073]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1062862353 / 1000000000000 : ℝ)
  lowerTail := (1283385939 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1733143089 / 250000000000 : ℝ)
  ledger := by
    have h : (231307577 / 200000000000 : ℚ) +
        (874546097 / 100000000000000000 : ℚ) / (2315859899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1062862353 / 1000000000000 : ℚ) + (1283385939 / 1000000000000 : ℚ) ≤
        (1733143089 / 250000000000 : ℚ) := by norm_num only
    have hc : (((231307577 / 200000000000 : ℚ) +
        (874546097 / 100000000000000000 : ℚ) / (2315859899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1062862353 / 1000000000000 : ℚ) + (1283385939 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1733143089 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13073]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13073 :
    2 * 160 < 13073 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999181 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13073 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13074 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13074. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13074 : WorldParameters where
  hiddenCharge := (578249163 / 500000000000 : ℝ)
  frame := (620599862977 / 1000000000000 : ℝ)
  moment := (8743714789 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13074 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292360298117 / 200000000000 : ℝ)
    root := (8253962697 / 1000000000000 : ℝ) }

noncomputable def scalar13074 : ScalarCertificate 13074 world13074 agent13074 where
  dimensionLo := 13074
  dimensionHi := 13074
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2316223499 / 1000000000000 : ℝ)
  frameLo := (620599862977 / 1000000000000 : ℝ)
  frameHi := (292360298117 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13074]
  agentFrame_pos := by norm_num only [agent13074]
  worldRadius := (2316223499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13074]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1062000313 / 1000000000000 : ℝ)
  lowerTail := (1282419729 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6929867149 / 1000000000000 : ℝ)
  ledger := by
    have h : (578249163 / 500000000000 : ℚ) +
        (8743714789 / 1000000000000000000 : ℚ) / (2316223499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1062000313 / 1000000000000 : ℚ) + (1282419729 / 1000000000000 : ℚ) ≤
        (6929867149 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578249163 / 500000000000 : ℚ) +
        (8743714789 / 1000000000000000000 : ℚ) / (2316223499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1062000313 / 1000000000000 : ℚ) + (1282419729 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6929867149 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13074]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13074 :
    2 * 160 < 13074 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999973 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13074 {← IO.monoMsNow}" : IO Unit)
