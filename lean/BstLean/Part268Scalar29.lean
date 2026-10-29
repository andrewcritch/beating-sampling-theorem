import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13075 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13075. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13075 : WorldParameters where
  hiddenCharge := (144557347 / 125000000000 : ℝ)
  frame := (310293406659 / 500000000000 : ℝ)
  moment := (1092746137 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13075 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365443240589 / 250000000000 : ℝ)
    root := (8253350823 / 1000000000000 : ℝ) }

noncomputable def scalar13075 : ScalarCertificate 13075 world13075 agent13075 where
  dimensionLo := 13075
  dimensionHi := 13075
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2316587099 / 1000000000000 : ℝ)
  frameLo := (310293406659 / 500000000000 : ℝ)
  frameHi := (365443240589 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13075]
  agentFrame_pos := by norm_num only [agent13075]
  worldRadius := (2316587099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13075]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1061139049 / 1000000000000 : ℝ)
  lowerTail := (1281454341 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3463582043 / 500000000000 : ℝ)
  ledger := by
    have h : (144557347 / 125000000000 : ℚ) +
        (1092746137 / 125000000000000000 : ℚ) / (2316587099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1061139049 / 1000000000000 : ℚ) + (1281454341 / 1000000000000 : ℚ) ≤
        (3463582043 / 500000000000 : ℚ) := by norm_num only
    have hc : (((144557347 / 125000000000 : ℚ) +
        (1092746137 / 125000000000000000 : ℚ) / (2316587099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1061139049 / 1000000000000 : ℚ) + (1281454341 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3463582043 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13075]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13075 :
    2 * 160 < 13075 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999307 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13075 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13076 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13076. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13076 : WorldParameters where
  hiddenCharge := (289104809 / 250000000000 : ℝ)
  frame := (7757172071 / 12500000000 : ℝ)
  moment := (8740223889 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13076 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730872108917 / 500000000000 : ℝ)
    root := (4126369559 / 500000000000 : ℝ) }

noncomputable def scalar13076 : ScalarCertificate 13076 world13076 agent13076 where
  dimensionLo := 13076
  dimensionHi := 13076
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2316950999 / 1000000000000 : ℝ)
  frameLo := (7757172071 / 12500000000 : ℝ)
  frameHi := (730872108917 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13076]
  agentFrame_pos := by norm_num only [agent13076]
  worldRadius := (2316950999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13076]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1060277999 / 1000000000000 : ℝ)
  lowerTail := (1280489033 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (10819471 / 1562500000 : ℝ)
  ledger := by
    have h : (289104809 / 250000000000 : ℚ) +
        (8740223889 / 1000000000000000000 : ℚ) / (2316950999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1060277999 / 1000000000000 : ℚ) + (1280489033 / 1000000000000 : ℚ) ≤
        (10819471 / 1562500000 : ℚ) := by norm_num only
    have hc : (((289104809 / 250000000000 : ℚ) +
        (8740223889 / 1000000000000000000 : ℚ) / (2316950999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1060277999 / 1000000000000 : ℚ) + (1280489033 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((10819471 / 1562500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13076]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13076 :
    2 * 160 < 13076 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999267 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13076 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13077 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13077. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13077 : WorldParameters where
  hiddenCharge := (1156379707 / 1000000000000 : ℝ)
  frame := (620560720063 / 1000000000000 : ℝ)
  moment := (8738479169 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13077 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1461715403057 / 1000000000000 : ℝ)
    root := (8252127643 / 1000000000000 : ℝ) }

noncomputable def scalar13077 : ScalarCertificate 13077 world13077 agent13077 where
  dimensionLo := 13077
  dimensionHi := 13077
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2317315099 / 1000000000000 : ℝ)
  frameLo := (620560720063 / 1000000000000 : ℝ)
  frameHi := (1461715403057 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13077]
  agentFrame_pos := by norm_num only [agent13077]
  worldRadius := (2317315099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13077]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1059417637 / 1000000000000 : ℝ)
  lowerTail := (3198811 / 2500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (865220053 / 125000000000 : ℝ)
  ledger := by
    have h : (1156379707 / 1000000000000 : ℚ) +
        (8738479169 / 1000000000000000000 : ℚ) / (2317315099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1059417637 / 1000000000000 : ℚ) + (3198811 / 2500000000 : ℚ) ≤
        (865220053 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1156379707 / 1000000000000 : ℚ) +
        (8738479169 / 1000000000000000000 : ℚ) / (2317315099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1059417637 / 1000000000000 : ℚ) + (3198811 / 2500000000 : ℚ) : ℚ) : ℝ) ≤
        ((865220053 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13077]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13077 :
    2 * 160 < 13077 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999751 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13077 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13078 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13078. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13078 : WorldParameters where
  hiddenCharge := (289085047 / 250000000000 : ℝ)
  frame := (310273838233 / 500000000000 : ℝ)
  moment := (1092091867 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13078 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292337319959 / 200000000000 : ℝ)
    root := (4125758137 / 500000000000 : ℝ) }

noncomputable def scalar13078 : ScalarCertificate 13078 world13078 agent13078 where
  dimensionLo := 13078
  dimensionHi := 13078
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2317679099 / 1000000000000 : ℝ)
  frameLo := (310273838233 / 500000000000 : ℝ)
  frameHi := (292337319959 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13078]
  agentFrame_pos := by norm_num only [agent13078]
  worldRadius := (2317679099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13078]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1058557963 / 1000000000000 : ℝ)
  lowerTail := (1278560489 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1689224 / 244140625 : ℝ)
  ledger := by
    have h : (289085047 / 250000000000 : ℚ) +
        (1092091867 / 125000000000000000 : ℚ) / (2317679099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1058557963 / 1000000000000 : ℚ) + (1278560489 / 1000000000000 : ℚ) ≤
        (1689224 / 244140625 : ℚ) := by norm_num only
    have hc : (((289085047 / 250000000000 : ℚ) +
        (1092091867 / 125000000000000000 : ℚ) / (2317679099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1058557963 / 1000000000000 : ℚ) + (1278560489 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1689224 / 244140625 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13078]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13078 :
    2 * 160 < 13078 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998699 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13078 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13079 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13079. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13079 : WorldParameters where
  hiddenCharge := (1156300679 / 1000000000000 : ℝ)
  frame := (77566829361 / 125000000000 : ℝ)
  moment := (873499119 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13079 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292331562777 / 200000000000 : ℝ)
    root := (1650181027 / 200000000000 : ℝ) }

noncomputable def scalar13079 : ScalarCertificate 13079 world13079 agent13079 where
  dimensionLo := 13079
  dimensionHi := 13079
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2318043099 / 1000000000000 : ℝ)
  frameLo := (77566829361 / 125000000000 : ℝ)
  frameHi := (292331562777 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13079]
  agentFrame_pos := by norm_num only [agent13079]
  worldRadius := (2318043099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13079]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1057699143 / 1000000000000 : ℝ)
  lowerTail := (1277597481 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6916364887 / 1000000000000 : ℝ)
  ledger := by
    have h : (1156300679 / 1000000000000 : ℚ) +
        (873499119 / 100000000000000000 : ℚ) / (2318043099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1057699143 / 1000000000000 : ℚ) + (1277597481 / 1000000000000 : ℚ) ≤
        (6916364887 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1156300679 / 1000000000000 : ℚ) +
        (873499119 / 100000000000000000 : ℚ) / (2318043099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1057699143 / 1000000000000 : ℚ) + (1277597481 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6916364887 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13079]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13079 :
    2 * 160 < 13079 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999679 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13079 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13080 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13080. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13080 : WorldParameters where
  hiddenCharge := (57813059 / 50000000000 : ℝ)
  frame := (62052159533 / 100000000000 : ℝ)
  moment := (873324793 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13080 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1461551935159 / 1000000000000 : ℝ)
    root := (8250294101 / 1000000000000 : ℝ) }

noncomputable def scalar13080 : ScalarCertificate 13080 world13080 agent13080 where
  dimensionLo := 13080
  dimensionHi := 13080
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2318524399 / 1000000000000 : ℝ)
  frameLo := (62052159533 / 100000000000 : ℝ)
  frameHi := (1461551935159 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13080]
  agentFrame_pos := by norm_num only [agent13080]
  worldRadius := (2318524399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13080]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1056655637 / 1000000000000 : ℝ)
  lowerTail := (159548829 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1382615177 / 200000000000 : ℝ)
  ledger := by
    have h : (57813059 / 50000000000 : ℚ) +
        (873324793 / 100000000000000000 : ℚ) / (2318524399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1056655637 / 1000000000000 : ℚ) + (159548829 / 125000000000 : ℚ) ≤
        (1382615177 / 200000000000 : ℚ) := by norm_num only
    have hc : (((57813059 / 50000000000 : ℚ) +
        (873324793 / 100000000000000000 : ℚ) / (2318524399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1056655637 / 1000000000000 : ℚ) + (159548829 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1382615177 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13080]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13080 :
    2 * 160 < 13080 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999209 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13080 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13081 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13081. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13081 : WorldParameters where
  hiddenCharge := (1156221691 / 1000000000000 : ℝ)
  frame := (62050855779 / 100000000000 : ℝ)
  moment := (2182876289 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13081 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730761589477 / 500000000000 : ℝ)
    root := (4124841649 / 500000000000 : ℝ) }

noncomputable def scalar13081 : ScalarCertificate 13081 world13081 agent13081 where
  dimensionLo := 13081
  dimensionHi := 13081
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2318888499 / 1000000000000 : ℝ)
  frameLo := (62050855779 / 100000000000 : ℝ)
  frameHi := (730761589477 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13081]
  agentFrame_pos := by norm_num only [agent13081]
  worldRadius := (2318888499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13081]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (263949653 / 250000000000 : ℝ)
  lowerTail := (1275429547 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6910384047 / 1000000000000 : ℝ)
  ledger := by
    have h : (1156221691 / 1000000000000 : ℚ) +
        (2182876289 / 250000000000000000 : ℚ) / (2318888499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (263949653 / 250000000000 : ℚ) + (1275429547 / 1000000000000 : ℚ) ≤
        (6910384047 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1156221691 / 1000000000000 : ℚ) +
        (2182876289 / 250000000000000000 : ℚ) / (2318888499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (263949653 / 250000000000 : ℚ) + (1275429547 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6910384047 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13081]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13081 :
    2 * 160 < 13081 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996313 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13081 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13082 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13082. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13082 : WorldParameters where
  hiddenCharge := (289045553 / 250000000000 : ℝ)
  frame := (620495522269 / 1000000000000 : ℝ)
  moment := (2182440717 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13082 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1461494434239 / 1000000000000 : ℝ)
    root := (8249072599 / 1000000000000 : ℝ) }

noncomputable def scalar13082 : ScalarCertificate 13082 world13082 agent13082 where
  dimensionLo := 13082
  dimensionHi := 13082
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2319252599 / 1000000000000 : ℝ)
  frameLo := (620495522269 / 1000000000000 : ℝ)
  frameHi := (1461494434239 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13082]
  agentFrame_pos := by norm_num only [agent13082]
  worldRadius := (2319252599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13082]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (527471169 / 500000000000 : ℝ)
  lowerTail := (254893851 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3453847147 / 500000000000 : ℝ)
  ledger := by
    have h : (289045553 / 250000000000 : ℚ) +
        (2182440717 / 250000000000000000 : ℚ) / (2319252599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (527471169 / 500000000000 : ℚ) + (254893851 / 200000000000 : ℚ) ≤
        (3453847147 / 500000000000 : ℚ) := by norm_num only
    have hc : (((289045553 / 250000000000 : ℚ) +
        (2182440717 / 250000000000000000 : ℚ) / (2319252599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (527471169 / 500000000000 : ℚ) + (254893851 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3453847147 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13082]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13082 :
    2 * 160 < 13082 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999501 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13082 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13083 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13083. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13083 : WorldParameters where
  hiddenCharge := (144517843 / 125000000000 : ℝ)
  frame := (124096497753 / 200000000000 : ℝ)
  moment := (1745604213 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13083 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29229314137 / 20000000000 : ℝ)
    root := (824846213 / 100000000000 : ℝ) }

noncomputable def scalar13083 : ScalarCertificate 13083 world13083 agent13083 where
  dimensionLo := 13083
  dimensionHi := 13083
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2319616699 / 1000000000000 : ℝ)
  frameLo := (124096497753 / 200000000000 : ℝ)
  frameHi := (29229314137 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13083]
  agentFrame_pos := by norm_num only [agent13083]
  worldRadius := (2319616699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13083]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (527043457 / 500000000000 : ℝ)
  lowerTail := (636754931 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1381001367 / 200000000000 : ℝ)
  ledger := by
    have h : (144517843 / 125000000000 : ℚ) +
        (1745604213 / 200000000000000000 : ℚ) / (2319616699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (527043457 / 500000000000 : ℚ) + (636754931 / 500000000000 : ℚ) ≤
        (1381001367 / 200000000000 : ℚ) := by norm_num only
    have hc : (((144517843 / 125000000000 : ℚ) +
        (1745604213 / 200000000000000000 : ℚ) / (2319616699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (527043457 / 500000000000 : ℚ) + (636754931 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1381001367 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13083]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13083 :
    2 * 160 < 13083 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999937 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13083 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13084 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13084. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13084 : WorldParameters where
  hiddenCharge := (578051643 / 500000000000 : ℝ)
  frame := (620469457279 / 1000000000000 : ℝ)
  moment := (8726279749 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13084 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730718498389 / 500000000000 : ℝ)
    root := (8247851767 / 1000000000000 : ℝ) }

noncomputable def scalar13084 : ScalarCertificate 13084 world13084 agent13084 where
  dimensionLo := 13084
  dimensionHi := 13084
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2319980899 / 1000000000000 : ℝ)
  frameLo := (620469457279 / 1000000000000 : ℝ)
  frameHi := (730718498389 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13084]
  agentFrame_pos := by norm_num only [agent13084]
  worldRadius := (2319980899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13084]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (263308081 / 250000000000 : ℝ)
  lowerTail := (1272551359 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6902321503 / 1000000000000 : ℝ)
  ledger := by
    have h : (578051643 / 500000000000 : ℚ) +
        (8726279749 / 1000000000000000000 : ℚ) / (2319980899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (263308081 / 250000000000 : ℚ) + (1272551359 / 1000000000000 : ℚ) ≤
        (6902321503 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578051643 / 500000000000 : ℚ) +
        (8726279749 / 1000000000000000000 : ℚ) / (2319980899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (263308081 / 250000000000 : ℚ) + (1272551359 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6902321503 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13084]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13084 :
    2 * 160 < 13084 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999399 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13084 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13085 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13085. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13085 : WorldParameters where
  hiddenCharge := (1156063837 / 1000000000000 : ℝ)
  frame := (620456427809 / 1000000000000 : ℝ)
  moment := (4362269459 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13085 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1461408298179 / 1000000000000 : ℝ)
    root := (8247241571 / 1000000000000 : ℝ) }

noncomputable def scalar13085 : ScalarCertificate 13085 world13085 agent13085 where
  dimensionLo := 13085
  dimensionHi := 13085
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2320344999 / 1000000000000 : ℝ)
  frameLo := (620456427809 / 1000000000000 : ℝ)
  frameHi := (1461408298179 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13085]
  agentFrame_pos := by norm_num only [agent13085]
  worldRadius := (2320344999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13085]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1052378457 / 1000000000000 : ℝ)
  lowerTail := (635796807 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1379927667 / 200000000000 : ℝ)
  ledger := by
    have h : (1156063837 / 1000000000000 : ℚ) +
        (4362269459 / 500000000000000000 : ℚ) / (2320344999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1052378457 / 1000000000000 : ℚ) + (635796807 / 500000000000 : ℚ) ≤
        (1379927667 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1156063837 / 1000000000000 : ℚ) +
        (4362269459 / 500000000000000000 : ℚ) / (2320344999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1052378457 / 1000000000000 : ℚ) + (635796807 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1379927667 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13085]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13085 :
    2 * 160 < 13085 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999057 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13085 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13086 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13086. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13086 : WorldParameters where
  hiddenCharge := (1156024399 / 1000000000000 : ℝ)
  frame := (155110850089 / 250000000000 : ℝ)
  moment := (2180699643 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13086 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730689808443 / 500000000000 : ℝ)
    root := (2061657901 / 250000000000 : ℝ) }

noncomputable def scalar13086 : ScalarCertificate 13086 world13086 agent13086 where
  dimensionLo := 13086
  dimensionHi := 13086
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2320709099 / 1000000000000 : ℝ)
  frameLo := (155110850089 / 250000000000 : ℝ)
  frameHi := (730689808443 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13086]
  agentFrame_pos := by norm_num only [agent13086]
  worldRadius := (2320709099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13086]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1051525437 / 1000000000000 : ℝ)
  lowerTail := (254127353 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3448478727 / 500000000000 : ℝ)
  ledger := by
    have h : (1156024399 / 1000000000000 : ℚ) +
        (2180699643 / 250000000000000000 : ℚ) / (2320709099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1051525437 / 1000000000000 : ℚ) + (254127353 / 200000000000 : ℚ) ≤
        (3448478727 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1156024399 / 1000000000000 : ℚ) +
        (2180699643 / 250000000000000000 : ℚ) / (2320709099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1051525437 / 1000000000000 : ℚ) + (254127353 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3448478727 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13086]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13086 :
    2 * 160 < 13086 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995811 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13086 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13087 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13087. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13087 : WorldParameters where
  hiddenCharge := (1155984971 / 1000000000000 : ℝ)
  frame := (310215187459 / 500000000000 : ℝ)
  moment := (8721058711 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13087 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730675473527 / 500000000000 : ℝ)
    root := (4123010871 / 500000000000 : ℝ) }

noncomputable def scalar13087 : ScalarCertificate 13087 world13087 agent13087 where
  dimensionLo := 13087
  dimensionHi := 13087
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2321073299 / 1000000000000 : ℝ)
  frameLo := (310215187459 / 500000000000 : ℝ)
  frameHi := (730675473527 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13087]
  agentFrame_pos := by norm_num only [agent13087]
  worldRadius := (2321073299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13087]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1050673229 / 1000000000000 : ℝ)
  lowerTail := (1269680779 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (861784831 / 125000000000 : ℝ)
  ledger := by
    have h : (1155984971 / 1000000000000 : ℚ) +
        (8721058711 / 1000000000000000000 : ℚ) / (2321073299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1050673229 / 1000000000000 : ℚ) + (1269680779 / 1000000000000 : ℚ) ≤
        (861784831 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1155984971 / 1000000000000 : ℚ) +
        (8721058711 / 1000000000000000000 : ℚ) / (2321073299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1050673229 / 1000000000000 : ℚ) + (1269680779 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((861784831 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13087]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13087 :
    2 * 160 < 13087 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999541 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13087 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13088 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13088. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13088 : WorldParameters where
  hiddenCharge := (1155945553 / 1000000000000 : ℝ)
  frame := (124083470299 / 200000000000 : ℝ)
  moment := (1743863867 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13088 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365330572169 / 250000000000 : ℝ)
    root := (8245412109 / 1000000000000 : ℝ) }

noncomputable def scalar13088 : ScalarCertificate 13088 world13088 agent13088 where
  dimensionLo := 13088
  dimensionHi := 13088
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2321437399 / 1000000000000 : ℝ)
  frameLo := (124083470299 / 200000000000 : ℝ)
  frameHi := (365330572169 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13088]
  agentFrame_pos := by norm_num only [agent13088]
  worldRadius := (2321437399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13088]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1049821781 / 1000000000000 : ℝ)
  lowerTail := (1268725589 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3445801041 / 500000000000 : ℝ)
  ledger := by
    have h : (1155945553 / 1000000000000 : ℚ) +
        (1743863867 / 200000000000000000 : ℚ) / (2321437399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1049821781 / 1000000000000 : ℚ) + (1268725589 / 1000000000000 : ℚ) ≤
        (3445801041 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1155945553 / 1000000000000 : ℚ) +
        (1743863867 / 200000000000000000 : ℚ) / (2321437399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1049821781 / 1000000000000 : ℚ) + (1268725589 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3445801041 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13088]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13088 :
    2 * 160 < 13088 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999929 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13088 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13089 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13089. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13089 : WorldParameters where
  hiddenCharge := (577953073 / 500000000000 : ℝ)
  frame := (620404330087 / 1000000000000 : ℝ)
  moment := (2179395111 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13089 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91330853339 / 62500000000 : ℝ)
    root := (8244802581 / 1000000000000 : ℝ) }

noncomputable def scalar13089 : ScalarCertificate 13089 world13089 agent13089 where
  dimensionLo := 13089
  dimensionHi := 13089
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2321801399 / 1000000000000 : ℝ)
  frameLo := (620404330087 / 1000000000000 : ℝ)
  frameHi := (91330853339 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13089]
  agentFrame_pos := by norm_num only [agent13089]
  worldRadius := (2321801399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13089]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1048971051 / 1000000000000 : ℝ)
  lowerTail := (633885581 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3444463839 / 500000000000 : ℝ)
  ledger := by
    have h : (577953073 / 500000000000 : ℚ) +
        (2179395111 / 250000000000000000 : ℚ) / (2321801399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1048971051 / 1000000000000 : ℚ) + (633885581 / 500000000000 : ℚ) ≤
        (3444463839 / 500000000000 : ℚ) := by norm_num only
    have hc : (((577953073 / 500000000000 : ℚ) +
        (2179395111 / 250000000000000000 : ℚ) / (2321801399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1048971051 / 1000000000000 : ℚ) + (633885581 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3444463839 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13089]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13089 :
    2 * 160 < 13089 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994413 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13089 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13090 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13090. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13090 : WorldParameters where
  hiddenCharge := (288966687 / 250000000000 : ℝ)
  frame := (310195655347 / 500000000000 : ℝ)
  moment := (4357921019 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13090 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365297005363 / 250000000000 : ℝ)
    root := (412209661 / 50000000000 : ℝ) }

noncomputable def scalar13090 : ScalarCertificate 13090 world13090 agent13090 where
  dimensionLo := 13090
  dimensionHi := 13090
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2322282899 / 1000000000000 : ℝ)
  frameLo := (310195655347 / 500000000000 : ℝ)
  frameHi := (365297005363 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13090]
  agentFrame_pos := by norm_num only [agent13090]
  worldRadius := (2322282899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13090]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (523968681 / 500000000000 : ℝ)
  lowerTail := (50663 / 40000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3442832781 / 500000000000 : ℝ)
  ledger := by
    have h : (288966687 / 250000000000 : ℚ) +
        (4357921019 / 500000000000000000 : ℚ) / (2322282899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (523968681 / 500000000000 : ℚ) + (50663 / 40000000 : ℚ) ≤
        (3442832781 / 500000000000 : ℚ) := by norm_num only
    have hc : (((288966687 / 250000000000 : ℚ) +
        (4357921019 / 500000000000000000 : ℚ) / (2322282899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (523968681 / 500000000000 : ℚ) + (50663 / 40000000 : ℚ) : ℚ) : ℝ) ≤
        ((3442832781 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13090]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13090 :
    2 * 160 < 13090 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997607 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13090 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13091 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13091. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13091 : WorldParameters where
  hiddenCharge := (7223921 / 6250000000 : ℝ)
  frame := (310189146657 / 500000000000 : ℝ)
  moment := (2178526029 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13091 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91322463121 / 62500000000 : ℝ)
    root := (8243584087 / 1000000000000 : ℝ) }

noncomputable def scalar13091 : ScalarCertificate 13091 world13091 agent13091 where
  dimensionLo := 13091
  dimensionHi := 13091
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2322647199 / 1000000000000 : ℝ)
  frameLo := (310189146657 / 500000000000 : ℝ)
  frameHi := (91322463121 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13091]
  agentFrame_pos := by norm_num only [agent13091]
  worldRadius := (2322647199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13091]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1047088561 / 1000000000000 : ℝ)
  lowerTail := (1265622641 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (860374491 / 125000000000 : ℝ)
  ledger := by
    have h : (7223921 / 6250000000 : ℚ) +
        (2178526029 / 250000000000000000 : ℚ) / (2322647199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1047088561 / 1000000000000 : ℚ) + (1265622641 / 1000000000000 : ℚ) ≤
        (860374491 / 125000000000 : ℚ) := by norm_num only
    have hc : (((7223921 / 6250000000 : ℚ) +
        (2178526029 / 250000000000000000 : ℚ) / (2322647199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1047088561 / 1000000000000 : ℚ) + (1265622641 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((860374491 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13091]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13091 :
    2 * 160 < 13091 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998937 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13091 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13092 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13092. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13092 : WorldParameters where
  hiddenCharge := (1155787983 / 1000000000000 : ℝ)
  frame := (620365277947 / 1000000000000 : ℝ)
  moment := (4356183339 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13092 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182641351961 / 125000000000 : ℝ)
    root := (8242975059 / 1000000000000 : ℝ) }

noncomputable def scalar13092 : ScalarCertificate 13092 world13092 agent13092 where
  dimensionLo := 13092
  dimensionHi := 13092
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2323011299 / 1000000000000 : ℝ)
  frameLo := (620365277947 / 1000000000000 : ℝ)
  frameHi := (182641351961 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13092]
  agentFrame_pos := by norm_num only [agent13092]
  worldRadius := (2323011299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13092]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (104624039 / 100000000000 : ℝ)
  lowerTail := (1264670943 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6880328401 / 1000000000000 : ℝ)
  ledger := by
    have h : (1155787983 / 1000000000000 : ℚ) +
        (4356183339 / 500000000000000000 : ℚ) / (2323011299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (104624039 / 100000000000 : ℚ) + (1264670943 / 1000000000000 : ℚ) ≤
        (6880328401 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1155787983 / 1000000000000 : ℚ) +
        (4356183339 / 500000000000000000 : ℚ) / (2323011299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (104624039 / 100000000000 : ℚ) + (1264670943 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6880328401 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13092]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13092 :
    2 * 160 < 13092 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995191 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13092 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13093 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13093. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13093 : WorldParameters where
  hiddenCharge := (144468577 / 125000000000 : ℝ)
  frame := (620352264593 / 1000000000000 : ℝ)
  moment := (2177657431 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13093 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292220446573 / 200000000000 : ℝ)
    root := (412118313 / 50000000000 : ℝ) }

noncomputable def scalar13093 : ScalarCertificate 13093 world13093 agent13093 where
  dimensionLo := 13093
  dimensionHi := 13093
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2323375499 / 1000000000000 : ℝ)
  frameLo := (620352264593 / 1000000000000 : ℝ)
  frameHi := (292220446573 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13093]
  agentFrame_pos := by norm_num only [agent13093]
  worldRadius := (2323375499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13093]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (522696553 / 500000000000 : ℝ)
  lowerTail := (157965023 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (53731743 / 7812500000 : ℝ)
  ledger := by
    have h : (144468577 / 125000000000 : ℚ) +
        (2177657431 / 250000000000000000 : ℚ) / (2323375499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (522696553 / 500000000000 : ℚ) + (157965023 / 125000000000 : ℚ) ≤
        (53731743 / 7812500000 : ℚ) := by norm_num only
    have hc : (((144468577 / 125000000000 : ℚ) +
        (2177657431 / 250000000000000000 : ℚ) / (2323375499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (522696553 / 500000000000 : ℚ) + (157965023 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((53731743 / 7812500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13093]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13093 :
    2 * 160 < 13093 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999521 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13093 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13094 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13094. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13094 : WorldParameters where
  hiddenCharge := (577854629 / 500000000000 : ℝ)
  frame := (620339253251 / 1000000000000 : ℝ)
  moment := (4354446627 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13094 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1461073661459 / 1000000000000 : ℝ)
    root := (1648351513 / 200000000000 : ℝ) }

noncomputable def scalar13094 : ScalarCertificate 13094 world13094 agent13094 where
  dimensionLo := 13094
  dimensionHi := 13094
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2323739699 / 1000000000000 : ℝ)
  frameLo := (620339253251 / 1000000000000 : ℝ)
  frameHi := (1461073661459 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13094]
  agentFrame_pos := by norm_num only [agent13094]
  worldRadius := (2323739699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13094]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1044546563 / 1000000000000 : ℝ)
  lowerTail := (39461569 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3437499933 / 500000000000 : ℝ)
  ledger := by
    have h : (577854629 / 500000000000 : ℚ) +
        (4354446627 / 500000000000000000 : ℚ) / (2323739699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1044546563 / 1000000000000 : ℚ) + (39461569 / 31250000000 : ℚ) ≤
        (3437499933 / 500000000000 : ℚ) := by norm_num only
    have hc : (((577854629 / 500000000000 : ℚ) +
        (4354446627 / 500000000000000000 : ℚ) / (2323739699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1044546563 / 1000000000000 : ℚ) + (39461569 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((3437499933 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13094]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13094 :
    2 * 160 < 13094 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997911 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13094 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13095 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13095. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13095 : WorldParameters where
  hiddenCharge := (1155669911 / 1000000000000 : ℝ)
  frame := (620326243921 / 1000000000000 : ℝ)
  moment := (2176789317 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13095 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730522553651 / 500000000000 : ℝ)
    root := (2060287259 / 250000000000 : ℝ) }

noncomputable def scalar13095 : ScalarCertificate 13095 world13095 agent13095 where
  dimensionLo := 13095
  dimensionHi := 13095
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2324103999 / 1000000000000 : ℝ)
  frameLo := (620326243921 / 1000000000000 : ℝ)
  frameHi := (730522553651 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13095]
  agentFrame_pos := by norm_num only [agent13095]
  worldRadius := (2324103999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13095]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (260925221 / 250000000000 : ℝ)
  lowerTail := (1261821153 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (53690147 / 7812500000 : ℝ)
  ledger := by
    have h : (1155669911 / 1000000000000 : ℚ) +
        (2176789317 / 250000000000000000 : ℚ) / (2324103999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260925221 / 250000000000 : ℚ) + (1261821153 / 1000000000000 : ℚ) ≤
        (53690147 / 7812500000 : ℚ) := by norm_num only
    have hc : (((1155669911 / 1000000000000 : ℚ) +
        (2176789317 / 250000000000000000 : ℚ) / (2324103999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260925221 / 250000000000 : ℚ) + (1261821153 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((53690147 / 7812500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13095]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13095 :
    2 * 160 < 13095 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (12499997 / 1250000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13095 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13096 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13096. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13096 : WorldParameters where
  hiddenCharge := (577815287 / 500000000000 : ℝ)
  frame := (310156618301 / 500000000000 : ℝ)
  moment := (1741084353 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13096 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182627070569 / 125000000000 : ℝ)
    root := (1648108147 / 200000000000 : ℝ) }

noncomputable def scalar13096 : ScalarCertificate 13096 world13096 agent13096 where
  dimensionLo := 13096
  dimensionHi := 13096
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2324468199 / 1000000000000 : ℝ)
  frameLo := (310156618301 / 500000000000 : ℝ)
  frameHi := (182627070569 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13096]
  agentFrame_pos := by norm_num only [agent13096]
  worldRadius := (2324468199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13096]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1042855959 / 1000000000000 : ℝ)
  lowerTail := (157609111 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6869679987 / 1000000000000 : ℝ)
  ledger := by
    have h : (577815287 / 500000000000 : ℚ) +
        (1741084353 / 200000000000000000 : ℚ) / (2324468199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1042855959 / 1000000000000 : ℚ) + (157609111 / 125000000000 : ℚ) ≤
        (6869679987 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((577815287 / 500000000000 : ℚ) +
        (1741084353 / 200000000000000000 : ℚ) / (2324468199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1042855959 / 1000000000000 : ℚ) + (157609111 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6869679987 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13096]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13096 :
    2 * 160 < 13096 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999933 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13096 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13097 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13097. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13097 : WorldParameters where
  hiddenCharge := (1155591247 / 1000000000000 : ℝ)
  frame := (310150115647 / 500000000000 : ℝ)
  moment := (4351843373 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13097 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460988039039 / 1000000000000 : ℝ)
    root := (8239932539 / 1000000000000 : ℝ) }

noncomputable def scalar13097 : ScalarCertificate 13097 world13097 agent13097 where
  dimensionLo := 13097
  dimensionHi := 13097
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2324832399 / 1000000000000 : ℝ)
  frameLo := (310150115647 / 500000000000 : ℝ)
  frameHi := (1460988039039 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13097]
  agentFrame_pos := by norm_num only [agent13097]
  worldRadius := (2324832399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13097]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (65125737 / 62500000000 : ℝ)
  lowerTail := (1259925427 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6867023257 / 1000000000000 : ℝ)
  ledger := by
    have h : (1155591247 / 1000000000000 : ℚ) +
        (4351843373 / 500000000000000000 : ℚ) / (2324832399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (65125737 / 62500000000 : ℚ) + (1259925427 / 1000000000000 : ℚ) ≤
        (6867023257 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1155591247 / 1000000000000 : ℚ) +
        (4351843373 / 500000000000000000 : ℚ) / (2324832399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (65125737 / 62500000000 : ℚ) + (1259925427 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6867023257 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13097]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13097 :
    2 * 160 < 13097 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999211 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13097 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13098 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13098. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13098 : WorldParameters where
  hiddenCharge := (115555193 / 100000000000 : ℝ)
  frame := (155071806999 / 250000000000 : ℝ)
  moment := (870195221 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13098 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365239882689 / 250000000000 : ℝ)
    root := (2059831127 / 250000000000 : ℝ) }

noncomputable def scalar13098 : ScalarCertificate 13098 world13098 agent13098 where
  dimensionLo := 13098
  dimensionHi := 13098
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2325196699 / 1000000000000 : ℝ)
  frameLo := (155071806999 / 250000000000 : ℝ)
  frameHi := (365239882689 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13098]
  agentFrame_pos := by norm_num only [agent13098]
  worldRadius := (2325196699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13098]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (520584243 / 500000000000 : ℝ)
  lowerTail := (251795777 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6864368707 / 1000000000000 : ℝ)
  ledger := by
    have h : (115555193 / 100000000000 : ℚ) +
        (870195221 / 100000000000000000 : ℚ) / (2325196699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (520584243 / 500000000000 : ℚ) + (251795777 / 200000000000 : ℚ) ≤
        (6864368707 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((115555193 / 100000000000 : ℚ) +
        (870195221 / 100000000000000000 : ℚ) / (2325196699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (520584243 / 500000000000 : ℚ) + (251795777 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6864368707 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13098]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13098 :
    2 * 160 < 13098 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995411 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13098 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13099 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13099. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13099 : WorldParameters where
  hiddenCharge := (1155512623 / 1000000000000 : ℝ)
  frame := (155068556677 / 250000000000 : ℝ)
  moment := (8700218157 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13099 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58437241121 / 40000000000 : ℝ)
    root := (4119358353 / 500000000000 : ℝ) }

noncomputable def scalar13099 : ScalarCertificate 13099 world13099 agent13099 where
  dimensionLo := 13099
  dimensionHi := 13099
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2325560899 / 1000000000000 : ℝ)
  frameLo := (155068556677 / 250000000000 : ℝ)
  frameHi := (58437241121 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13099]
  agentFrame_pos := by norm_num only [agent13099]
  worldRadius := (2325560899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13099]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (130040739 / 125000000000 : ℝ)
  lowerTail := (251606621 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (857714541 / 125000000000 : ℝ)
  ledger := by
    have h : (1155512623 / 1000000000000 : ℚ) +
        (8700218157 / 1000000000000000000 : ℚ) / (2325560899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (130040739 / 125000000000 : ℚ) + (251606621 / 200000000000 : ℚ) ≤
        (857714541 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1155512623 / 1000000000000 : ℚ) +
        (8700218157 / 1000000000000000000 : ℚ) / (2325560899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (130040739 / 125000000000 : ℚ) + (251606621 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((857714541 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13099]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13099 :
    2 * 160 < 13099 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (249999997 / 25000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13099 {← IO.monoMsNow}" : IO Unit)
