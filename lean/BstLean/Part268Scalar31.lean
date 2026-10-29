import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13125 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13125. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13125 : WorldParameters where
  hiddenCharge := (1154494173 / 1000000000000 : ℝ)
  frame := (123987379403 / 200000000000 : ℝ)
  moment := (8655301759 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13125 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729982298171 / 500000000000 : ℝ)
    root := (4111485261 / 500000000000 : ℝ) }

noncomputable def scalar13125 : ScalarCertificate 13125 world13125 agent13125 where
  dimensionLo := 13125
  dimensionHi := 13125
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2335387399 / 1000000000000 : ℝ)
  frameLo := (123987379403 / 200000000000 : ℝ)
  frameHi := (729982298171 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13125]
  agentFrame_pos := by norm_num only [agent13125]
  worldRadius := (2335387399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13125]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (127269763 / 125000000000 : ℝ)
  lowerTail := (1233025317 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3395888813 / 500000000000 : ℝ)
  ledger := by
    have h : (1154494173 / 1000000000000 : ℚ) +
        (8655301759 / 1000000000000000000 : ℚ) / (2335387399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127269763 / 125000000000 : ℚ) + (1233025317 / 1000000000000 : ℚ) ≤
        (3395888813 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1154494173 / 1000000000000 : ℚ) +
        (8655301759 / 1000000000000000000 : ℚ) / (2335387399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127269763 / 125000000000 : ℚ) + (1233025317 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3395888813 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13125]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13125 :
    2 * 160 < 13125 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999807 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13125 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13126 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13126. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13126 : WorldParameters where
  hiddenCharge := (1154455137 / 1000000000000 : ℝ)
  frame := (619923949803 / 1000000000000 : ℝ)
  moment := (8653580683 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13126 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459936471397 / 1000000000000 : ℝ)
    root := (8222367101 / 1000000000000 : ℝ) }

noncomputable def scalar13126 : ScalarCertificate 13126 world13126 agent13126 where
  dimensionLo := 13126
  dimensionHi := 13126
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2335751899 / 1000000000000 : ℝ)
  frameLo := (619923949803 / 1000000000000 : ℝ)
  frameHi := (1459936471397 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13126]
  agentFrame_pos := by norm_num only [agent13126]
  worldRadius := (2335751899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13126]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (508668463 / 500000000000 : ℝ)
  lowerTail := (616051131 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6789183637 / 1000000000000 : ℝ)
  ledger := by
    have h : (1154455137 / 1000000000000 : ℚ) +
        (8653580683 / 1000000000000000000 : ℚ) / (2335751899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (508668463 / 500000000000 : ℚ) + (616051131 / 500000000000 : ℚ) ≤
        (6789183637 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1154455137 / 1000000000000 : ℚ) +
        (8653580683 / 1000000000000000000 : ℚ) / (2335751899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (508668463 / 500000000000 : ℚ) + (616051131 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6789183637 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13126]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13126 :
    2 * 160 < 13126 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997983 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13126 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13127 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13127. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13127 : WorldParameters where
  hiddenCharge := (1154416111 / 1000000000000 : ℝ)
  frame := (619911004587 / 1000000000000 : ℝ)
  moment := (1730372017 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13127 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459908089479 / 1000000000000 : ℝ)
    root := (8221763843 / 1000000000000 : ℝ) }

noncomputable def scalar13127 : ScalarCertificate 13127 world13127 agent13127 where
  dimensionLo := 13127
  dimensionHi := 13127
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2336116799 / 1000000000000 : ℝ)
  frameLo := (619911004587 / 1000000000000 : ℝ)
  frameHi := (1459908089479 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13127]
  agentFrame_pos := by norm_num only [agent13127]
  worldRadius := (2336116799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13127]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (101651587 / 100000000000 : ℝ)
  lowerTail := (1231179171 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6786589719 / 1000000000000 : ℝ)
  ledger := by
    have h : (1154416111 / 1000000000000 : ℚ) +
        (1730372017 / 200000000000000000 : ℚ) / (2336116799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (101651587 / 100000000000 : ℚ) + (1231179171 / 1000000000000 : ℚ) ≤
        (6786589719 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1154416111 / 1000000000000 : ℚ) +
        (1730372017 / 200000000000000000 : ℚ) / (2336116799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (101651587 / 100000000000 : ℚ) + (1231179171 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6786589719 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13127]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13127 :
    2 * 160 < 13127 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997923 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13127 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13128 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13128. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13128 : WorldParameters where
  hiddenCharge := (230875419 / 200000000000 : ℝ)
  frame := (309949030683 / 500000000000 : ℝ)
  moment := (1730027993 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13128 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729939841907 / 500000000000 : ℝ)
    root := (8221160749 / 1000000000000 : ℝ) }

noncomputable def scalar13128 : ScalarCertificate 13128 world13128 agent13128 where
  dimensionLo := 13128
  dimensionHi := 13128
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2336481799 / 1000000000000 : ℝ)
  frameLo := (309949030683 / 500000000000 : ℝ)
  frameHi := (729939841907 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13128]
  agentFrame_pos := by norm_num only [agent13128]
  worldRadius := (2336481799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13128]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (253923879 / 250000000000 : ℝ)
  lowerTail := (1230256803 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1356799523 / 200000000000 : ℝ)
  ledger := by
    have h : (230875419 / 200000000000 : ℚ) +
        (1730027993 / 200000000000000000 : ℚ) / (2336481799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253923879 / 250000000000 : ℚ) + (1230256803 / 1000000000000 : ℚ) ≤
        (1356799523 / 200000000000 : ℚ) := by norm_num only
    have hc : (((230875419 / 200000000000 : ℚ) +
        (1730027993 / 200000000000000000 : ℚ) / (2336481799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253923879 / 250000000000 : ℚ) + (1230256803 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1356799523 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13128]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13128 :
    2 * 160 < 13128 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994567 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13128 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13129 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13129. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13129 : WorldParameters where
  hiddenCharge := (1154338089 / 1000000000000 : ℝ)
  frame := (619885120141 / 1000000000000 : ℝ)
  moment := (8648420323 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13129 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459851283549 / 1000000000000 : ℝ)
    root := (8220557817 / 1000000000000 : ℝ) }

noncomputable def scalar13129 : ScalarCertificate 13129 world13129 agent13129 where
  dimensionLo := 13129
  dimensionHi := 13129
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2336846799 / 1000000000000 : ℝ)
  frameLo := (619885120141 / 1000000000000 : ℝ)
  frameHi := (1459851283549 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13129]
  agentFrame_pos := by norm_num only [agent13129]
  worldRadius := (2336846799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13129]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (202975179 / 200000000000 : ℝ)
  lowerTail := (614667603 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6781407543 / 1000000000000 : ℝ)
  ledger := by
    have h : (1154338089 / 1000000000000 : ℚ) +
        (8648420323 / 1000000000000000000 : ℚ) / (2336846799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (202975179 / 200000000000 : ℚ) + (614667603 / 500000000000 : ℚ) ≤
        (6781407543 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1154338089 / 1000000000000 : ℚ) +
        (8648420323 / 1000000000000000000 : ℚ) / (2336846799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (202975179 / 200000000000 : ℚ) + (614667603 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6781407543 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13129]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13129 :
    2 * 160 < 13129 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (499999989 / 50000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13129 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13130 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13130. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13130 : WorldParameters where
  hiddenCharge := (1154299093 / 1000000000000 : ℝ)
  frame := (619872180909 / 1000000000000 : ℝ)
  moment := (8646701159 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13130 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729873166247 / 500000000000 : ℝ)
    root := (8219955111 / 1000000000000 : ℝ) }

noncomputable def scalar13130 : ScalarCertificate 13130 world13130 agent13130 where
  dimensionLo := 13130
  dimensionHi := 13130
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2337329499 / 1000000000000 : ℝ)
  frameLo := (619872180909 / 1000000000000 : ℝ)
  frameHi := (729873166247 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13130]
  agentFrame_pos := by norm_num only [agent13130]
  worldRadius := (2337329499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13130]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (506939883 / 500000000000 : ℝ)
  lowerTail := (76761239 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (211820259 / 31250000000 : ℝ)
  ledger := by
    have h : (1154299093 / 1000000000000 : ℚ) +
        (8646701159 / 1000000000000000000 : ℚ) / (2337329499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (506939883 / 500000000000 : ℚ) + (76761239 / 62500000000 : ℚ) ≤
        (211820259 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1154299093 / 1000000000000 : ℚ) +
        (8646701159 / 1000000000000000000 : ℚ) / (2337329499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (506939883 / 500000000000 : ℚ) + (76761239 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((211820259 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13130]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13130 :
    2 * 160 < 13130 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996557 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13130 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13131 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13131. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13131 : WorldParameters where
  hiddenCharge := (1154260107 / 1000000000000 : ℝ)
  frame := (77482405459 / 125000000000 : ℝ)
  moment := (1080622809 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13131 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729858983593 / 500000000000 : ℝ)
    root := (1643870501 / 200000000000 : ℝ) }

noncomputable def scalar13131 : ScalarCertificate 13131 world13131 agent13131 where
  dimensionLo := 13131
  dimensionHi := 13131
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2337694599 / 1000000000000 : ℝ)
  frameLo := (77482405459 / 125000000000 : ℝ)
  frameHi := (729858983593 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13131]
  agentFrame_pos := by norm_num only [agent13131]
  worldRadius := (2337694599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13131]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1013061869 / 1000000000000 : ℝ)
  lowerTail := (1227260083 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3387831409 / 500000000000 : ℝ)
  ledger := by
    have h : (1154260107 / 1000000000000 : ℚ) +
        (1080622809 / 125000000000000000 : ℚ) / (2337694599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1013061869 / 1000000000000 : ℚ) + (1227260083 / 1000000000000 : ℚ) ≤
        (3387831409 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1154260107 / 1000000000000 : ℚ) +
        (1080622809 / 125000000000000000 : ℚ) / (2337694599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1013061869 / 1000000000000 : ℚ) + (1227260083 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3387831409 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13131]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13131 :
    2 * 160 < 13131 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996201 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13131 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13132 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13132. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13132 : WorldParameters where
  hiddenCharge := (1154221131 / 1000000000000 : ℝ)
  frame := (154961577107 / 250000000000 : ℝ)
  moment := (4321632131 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13132 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364922403273 / 250000000000 : ℝ)
    root := (4109375031 / 500000000000 : ℝ) }

noncomputable def scalar13132 : ScalarCertificate 13132 world13132 agent13132 where
  dimensionLo := 13132
  dimensionHi := 13132
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2338059699 / 1000000000000 : ℝ)
  frameLo := (154961577107 / 250000000000 : ℝ)
  frameHi := (364922403273 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13132]
  agentFrame_pos := by norm_num only [agent13132]
  worldRadius := (2338059699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13132]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (506122361 / 500000000000 : ℝ)
  lowerTail := (613170567 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1354615883 / 200000000000 : ℝ)
  ledger := by
    have h : (1154221131 / 1000000000000 : ℚ) +
        (4321632131 / 500000000000000000 : ℚ) / (2338059699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (506122361 / 500000000000 : ℚ) + (613170567 / 500000000000 : ℚ) ≤
        (1354615883 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1154221131 / 1000000000000 : ℚ) +
        (4321632131 / 500000000000000000 : ℚ) / (2338059699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (506122361 / 500000000000 : ℚ) + (613170567 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1354615883 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13132]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13132 :
    2 * 160 < 13132 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999347 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13132 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13133 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13133. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13133 : WorldParameters where
  hiddenCharge := (230836433 / 200000000000 : ℝ)
  frame := (309916687589 / 500000000000 : ℝ)
  moment := (864154653 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13133 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729830638017 / 500000000000 : ℝ)
    root := (4109073891 / 500000000000 : ℝ) }

noncomputable def scalar13133 : ScalarCertificate 13133 world13133 agent13133 where
  dimensionLo := 13133
  dimensionHi := 13133
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2338424699 / 1000000000000 : ℝ)
  frameLo := (309916687589 / 500000000000 : ℝ)
  frameHi := (729830638017 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13133]
  agentFrame_pos := by norm_num only [agent13133]
  worldRadius := (2338424699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13133]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (25285707 / 25000000000 : ℝ)
  lowerTail := (122542293 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3385249061 / 500000000000 : ℝ)
  ledger := by
    have h : (230836433 / 200000000000 : ℚ) +
        (864154653 / 100000000000000000 : ℚ) / (2338424699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25285707 / 25000000000 : ℚ) + (122542293 / 100000000000 : ℚ) ≤
        (3385249061 / 500000000000 : ℚ) := by norm_num only
    have hc : (((230836433 / 200000000000 : ℚ) +
        (864154653 / 100000000000000000 : ℚ) / (2338424699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25285707 / 25000000000 : ℚ) + (122542293 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3385249061 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13133]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13133 :
    2 * 160 < 13133 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998349 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13133 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13134 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13134. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13134 : WorldParameters where
  hiddenCharge := (1154143209 / 1000000000000 : ℝ)
  frame := (619820443919 / 1000000000000 : ℝ)
  moment := (345593171 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13134 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459632956007 / 1000000000000 : ℝ)
    root := (1643509133 / 200000000000 : ℝ) }

noncomputable def scalar13134 : ScalarCertificate 13134 world13134 agent13134 where
  dimensionLo := 13134
  dimensionHi := 13134
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2338789799 / 1000000000000 : ℝ)
  frameLo := (619820443919 / 1000000000000 : ℝ)
  frameHi := (1459632956007 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13134]
  agentFrame_pos := by norm_num only [agent13134]
  worldRadius := (2338789799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13134]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (252653167 / 250000000000 : ℝ)
  lowerTail := (1224505613 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (845989867 / 125000000000 : ℝ)
  ledger := by
    have h : (1154143209 / 1000000000000 : ℚ) +
        (345593171 / 40000000000000000 : ℚ) / (2338789799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (252653167 / 250000000000 : ℚ) + (1224505613 / 1000000000000 : ℚ) ≤
        (845989867 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1154143209 / 1000000000000 : ℚ) +
        (345593171 / 40000000000000000 : ℚ) / (2338789799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (252653167 / 250000000000 : ℚ) + (1224505613 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((845989867 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13134]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13134 :
    2 * 160 < 13134 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (499999757 / 50000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13134 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13135 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13135. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13135 : WorldParameters where
  hiddenCharge := (577052131 / 500000000000 : ℝ)
  frame := (619807514653 / 1000000000000 : ℝ)
  moment := (8638112497 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13135 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182450580897 / 125000000000 : ℝ)
    root := (8216943709 / 1000000000000 : ℝ) }

noncomputable def scalar13135 : ScalarCertificate 13135 world13135 agent13135 where
  dimensionLo := 13135
  dimensionHi := 13135
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2339154899 / 1000000000000 : ℝ)
  frameLo := (619807514653 / 1000000000000 : ℝ)
  frameHi := (182450580897 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13135]
  agentFrame_pos := by norm_num only [agent13135]
  worldRadius := (2339154899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13135]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (201959561 / 200000000000 : ℝ)
  lowerTail := (1223589087 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3382670907 / 500000000000 : ℝ)
  ledger := by
    have h : (577052131 / 500000000000 : ℚ) +
        (8638112497 / 1000000000000000000 : ℚ) / (2339154899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (201959561 / 200000000000 : ℚ) + (1223589087 / 1000000000000 : ℚ) ≤
        (3382670907 / 500000000000 : ℚ) := by norm_num only
    have hc : (((577052131 / 500000000000 : ℚ) +
        (8638112497 / 1000000000000000000 : ℚ) / (2339154899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (201959561 / 200000000000 : ℚ) + (1223589087 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3382670907 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13135]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13135 :
    2 * 160 < 13135 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994719 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13135 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13136 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13136. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13136 : WorldParameters where
  hiddenCharge := (577032663 / 500000000000 : ℝ)
  frame := (309897293689 / 500000000000 : ℝ)
  moment := (1727279239 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13136 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291915269907 / 200000000000 : ℝ)
    root := (8216341917 / 1000000000000 : ℝ) }

noncomputable def scalar13136 : ScalarCertificate 13136 world13136 agent13136 where
  dimensionLo := 13136
  dimensionHi := 13136
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2339519999 / 1000000000000 : ℝ)
  frameLo := (309897293689 / 500000000000 : ℝ)
  frameHi := (291915269907 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13136]
  agentFrame_pos := by norm_num only [agent13136]
  worldRadius := (2339519999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13136]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (126122961 / 125000000000 : ℝ)
  lowerTail := (152834169 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6762766751 / 1000000000000 : ℝ)
  ledger := by
    have h : (577032663 / 500000000000 : ℚ) +
        (1727279239 / 200000000000000000 : ℚ) / (2339519999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (126122961 / 125000000000 : ℚ) + (152834169 / 125000000000 : ℚ) ≤
        (6762766751 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((577032663 / 500000000000 : ℚ) +
        (1727279239 / 200000000000000000 : ℚ) / (2339519999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (126122961 / 125000000000 : ℚ) + (152834169 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6762766751 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13136]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13136 :
    2 * 160 < 13136 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997067 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13136 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13137 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13137. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13137 : WorldParameters where
  hiddenCharge := (1442533 / 1250000000 : ℝ)
  frame := (309890831047 / 500000000000 : ℝ)
  moment := (863468037 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13137 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364887017227 / 250000000000 : ℝ)
    root := (8215740287 / 1000000000000 : ℝ) }

noncomputable def scalar13137 : ScalarCertificate 13137 world13137 agent13137 where
  dimensionLo := 13137
  dimensionHi := 13137
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2339885099 / 1000000000000 : ℝ)
  frameLo := (309890831047 / 500000000000 : ℝ)
  frameHi := (364887017227 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13137]
  agentFrame_pos := by norm_num only [agent13137]
  worldRadius := (2339885099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13137]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (31505323 / 31250000000 : ℝ)
  lowerTail := (1221758429 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (676019379 / 100000000000 : ℝ)
  ledger := by
    have h : (1442533 / 1250000000 : ℚ) +
        (863468037 / 100000000000000000 : ℚ) / (2339885099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (31505323 / 31250000000 : ℚ) + (1221758429 / 1000000000000 : ℚ) ≤
        (676019379 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1442533 / 1250000000 : ℚ) +
        (863468037 / 100000000000000000 : ℚ) / (2339885099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (31505323 / 31250000000 : ℚ) + (1221758429 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((676019379 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13137]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13137 :
    2 * 160 < 13137 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999649 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13137 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13138 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13138. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13138 : WorldParameters where
  hiddenCharge := (1153987483 / 1000000000000 : ℝ)
  frame := (619768738801 / 1000000000000 : ℝ)
  moment := (8632965021 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13138 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459519799459 / 1000000000000 : ℝ)
    root := (4107569409 / 500000000000 : ℝ) }

noncomputable def scalar13138 : ScalarCertificate 13138 world13138 agent13138 where
  dimensionLo := 13138
  dimensionHi := 13138
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2340250199 / 1000000000000 : ℝ)
  frameLo := (619768738801 / 1000000000000 : ℝ)
  frameHi := (1459519799459 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13138]
  agentFrame_pos := by norm_num only [agent13138]
  worldRadius := (2340250199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13138]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1007357729 / 1000000000000 : ℝ)
  lowerTail := (244168859 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1351524577 / 200000000000 : ℝ)
  ledger := by
    have h : (1153987483 / 1000000000000 : ℚ) +
        (8632965021 / 1000000000000000000 : ℚ) / (2340250199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1007357729 / 1000000000000 : ℚ) + (244168859 / 200000000000 : ℚ) ≤
        (1351524577 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1153987483 / 1000000000000 : ℚ) +
        (8632965021 / 1000000000000000000 : ℚ) / (2340250199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1007357729 / 1000000000000 : ℚ) + (244168859 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1351524577 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13138]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13138 :
    2 * 160 < 13138 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999321 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13138 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13139 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13139. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13139 : WorldParameters where
  hiddenCharge := (1153948577 / 1000000000000 : ℝ)
  frame := (309877908749 / 500000000000 : ℝ)
  moment := (8631250149 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13139 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364872886753 / 250000000000 : ℝ)
    root := (1026817189 / 125000000000 : ℝ) }

noncomputable def scalar13139 : ScalarCertificate 13139 world13139 agent13139 where
  dimensionLo := 13139
  dimensionHi := 13139
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2340615199 / 1000000000000 : ℝ)
  frameLo := (309877908749 / 500000000000 : ℝ)
  frameHi := (364872886753 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13139]
  agentFrame_pos := by norm_num only [agent13139]
  worldRadius := (2340615199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13139]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (503272911 / 500000000000 : ℝ)
  lowerTail := (1219930901 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3377527039 / 500000000000 : ℝ)
  ledger := by
    have h : (1153948577 / 1000000000000 : ℚ) +
        (8631250149 / 1000000000000000000 : ℚ) / (2340615199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (503272911 / 500000000000 : ℚ) + (1219930901 / 1000000000000 : ℚ) ≤
        (3377527039 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1153948577 / 1000000000000 : ℚ) +
        (8631250149 / 1000000000000000000 : ℚ) / (2340615199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (503272911 / 500000000000 : ℚ) + (1219930901 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3377527039 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13139]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13139 :
    2 * 160 < 13139 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998913 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13139 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13140 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13140. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13140 : WorldParameters where
  hiddenCharge := (1153909681 / 1000000000000 : ℝ)
  frame := (77467862273 / 125000000000 : ℝ)
  moment := (1078691969 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13140 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364846709671 / 250000000000 : ℝ)
    root := (8213936369 / 1000000000000 : ℝ) }

noncomputable def scalar13140 : ScalarCertificate 13140 world13140 agent13140 where
  dimensionLo := 13140
  dimensionHi := 13140
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2341098299 / 1000000000000 : ℝ)
  frameLo := (77467862273 / 125000000000 : ℝ)
  frameHi := (364846709671 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13140]
  agentFrame_pos := by norm_num only [agent13140]
  worldRadius := (2341098299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13140]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1005559103 / 1000000000000 : ℝ)
  lowerTail := (6093929 / 5000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6751920403 / 1000000000000 : ℝ)
  ledger := by
    have h : (1153909681 / 1000000000000 : ℚ) +
        (1078691969 / 125000000000000000 : ℚ) / (2341098299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1005559103 / 1000000000000 : ℚ) + (6093929 / 5000000000 : ℚ) ≤
        (6751920403 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1153909681 / 1000000000000 : ℚ) +
        (1078691969 / 125000000000000000 : ℚ) / (2341098299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1005559103 / 1000000000000 : ℚ) + (6093929 / 5000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6751920403 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13140]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13140 :
    2 * 160 < 13140 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (99999997 / 10000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13140 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13141 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13141. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13141 : WorldParameters where
  hiddenCharge := (576935397 / 500000000000 : ℝ)
  frame := (619729980859 / 1000000000000 : ℝ)
  moment := (1078477729 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13141 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (36483965381 / 25000000000 : ℝ)
    root := (8213335387 / 1000000000000 : ℝ) }

noncomputable def scalar13141 : ScalarCertificate 13141 world13141 agent13141 where
  dimensionLo := 13141
  dimensionHi := 13141
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2341463299 / 1000000000000 : ℝ)
  frameLo := (619729980859 / 1000000000000 : ℝ)
  frameHi := (36483965381 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13141]
  agentFrame_pos := by norm_num only [agent13141]
  worldRadius := (2341463299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13141]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1004748819 / 1000000000000 : ℝ)
  lowerTail := (304468537 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6749356111 / 1000000000000 : ℝ)
  ledger := by
    have h : (576935397 / 500000000000 : ℚ) +
        (1078477729 / 125000000000000000 : ℚ) / (2341463299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1004748819 / 1000000000000 : ℚ) + (304468537 / 250000000000 : ℚ) ≤
        (6749356111 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576935397 / 500000000000 : ℚ) +
        (1078477729 / 125000000000000000 : ℚ) / (2341463299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1004748819 / 1000000000000 : ℚ) + (304468537 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6749356111 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13141]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13141 :
    2 * 160 < 13141 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998563 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13141 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13142 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13142. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13142 : WorldParameters where
  hiddenCharge := (576915959 / 500000000000 : ℝ)
  frame := (619717065523 / 1000000000000 : ℝ)
  moment := (8626108387 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13142 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729665204389 / 500000000000 : ℝ)
    root := (2053183657 / 250000000000 : ℝ) }

noncomputable def scalar13142 : ScalarCertificate 13142 world13142 agent13142 where
  dimensionLo := 13142
  dimensionHi := 13142
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2341828499 / 1000000000000 : ℝ)
  frameLo := (619717065523 / 1000000000000 : ℝ)
  frameHi := (729665204389 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13142]
  agentFrame_pos := by norm_num only [agent13142]
  worldRadius := (2341828499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13142]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (501969731 / 500000000000 : ℝ)
  lowerTail := (608481743 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6746793987 / 1000000000000 : ℝ)
  ledger := by
    have h : (576915959 / 500000000000 : ℚ) +
        (8626108387 / 1000000000000000000 : ℚ) / (2341828499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (501969731 / 500000000000 : ℚ) + (608481743 / 500000000000 : ℚ) ≤
        (6746793987 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576915959 / 500000000000 : ℚ) +
        (8626108387 / 1000000000000000000 : ℚ) / (2341828499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (501969731 / 500000000000 : ℚ) + (608481743 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6746793987 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13142]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13142 :
    2 * 160 < 13142 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994391 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13142 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13143 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13143. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13143 : WorldParameters where
  hiddenCharge := (1153793051 / 1000000000000 : ℝ)
  frame := (24788166087 / 40000000000 : ℝ)
  moment := (8624395417 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13143 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459302207641 / 1000000000000 : ℝ)
    root := (8212133969 / 1000000000000 : ℝ) }

noncomputable def scalar13143 : ScalarCertificate 13143 world13143 agent13143 where
  dimensionLo := 13143
  dimensionHi := 13143
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2342193699 / 1000000000000 : ℝ)
  frameLo := (24788166087 / 40000000000 : ℝ)
  frameHi := (1459302207641 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13143]
  agentFrame_pos := by norm_num only [agent13143]
  worldRadius := (2342193699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13143]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (250782697 / 250000000000 : ℝ)
  lowerTail := (243210709 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6744233789 / 1000000000000 : ℝ)
  ledger := by
    have h : (1153793051 / 1000000000000 : ℚ) +
        (8624395417 / 1000000000000000000 : ℚ) / (2342193699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (250782697 / 250000000000 : ℚ) + (243210709 / 200000000000 : ℚ) ≤
        (6744233789 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1153793051 / 1000000000000 : ℚ) +
        (8624395417 / 1000000000000000000 : ℚ) / (2342193699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (250782697 / 250000000000 : ℚ) + (243210709 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6744233789 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13143]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13143 :
    2 * 160 < 13143 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998537 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13143 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13144 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13144. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13144 : WorldParameters where
  hiddenCharge := (576877097 / 500000000000 : ℝ)
  frame := (123938248163 / 200000000000 : ℝ)
  moment := (8622682923 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13144 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729637011737 / 500000000000 : ℝ)
    root := (8211533473 / 1000000000000 : ℝ) }

noncomputable def scalar13144 : ScalarCertificate 13144 world13144 agent13144 where
  dimensionLo := 13144
  dimensionHi := 13144
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2342558799 / 1000000000000 : ℝ)
  frameLo := (123938248163 / 200000000000 : ℝ)
  frameHi := (729637011737 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13144]
  agentFrame_pos := by norm_num only [agent13144]
  worldRadius := (2342558799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13144]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (100232281 / 100000000000 : ℝ)
  lowerTail := (1215144341 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6741675677 / 1000000000000 : ℝ)
  ledger := by
    have h : (576877097 / 500000000000 : ℚ) +
        (8622682923 / 1000000000000000000 : ℚ) / (2342558799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (100232281 / 100000000000 : ℚ) + (1215144341 / 1000000000000 : ℚ) ≤
        (6741675677 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576877097 / 500000000000 : ℚ) +
        (8622682923 / 1000000000000000000 : ℚ) / (2342558799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (100232281 / 100000000000 : ℚ) + (1215144341 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6741675677 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13144]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13144 :
    2 * 160 < 13144 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999609 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13144 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13145 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13145. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13145 : WorldParameters where
  hiddenCharge := (1153715347 / 1000000000000 : ℝ)
  frame := (309839165721 / 500000000000 : ℝ)
  moment := (1077621363 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13145 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459245856273 / 1000000000000 : ℝ)
    root := (4105466569 / 500000000000 : ℝ) }

noncomputable def scalar13145 : ScalarCertificate 13145 world13145 agent13145 where
  dimensionLo := 13145
  dimensionHi := 13145
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2342923999 / 1000000000000 : ℝ)
  frameLo := (309839165721 / 500000000000 : ℝ)
  frameHi := (1459245856273 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13145]
  agentFrame_pos := by norm_num only [agent13145]
  worldRadius := (2342923999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13145]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (500757827 / 500000000000 : ℝ)
  lowerTail := (607118007 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6739119651 / 1000000000000 : ℝ)
  ledger := by
    have h : (1153715347 / 1000000000000 : ℚ) +
        (1077621363 / 125000000000000000 : ℚ) / (2342923999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (500757827 / 500000000000 : ℚ) + (607118007 / 500000000000 : ℚ) ≤
        (6739119651 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1153715347 / 1000000000000 : ℚ) +
        (1077621363 / 125000000000000000 : ℚ) / (2342923999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (500757827 / 500000000000 : ℚ) + (607118007 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6739119651 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13145]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13145 :
    2 * 160 < 13145 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999517 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13145 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13146 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13146. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13146 : WorldParameters where
  hiddenCharge := (1153676511 / 1000000000000 : ℝ)
  frame := (123933084811 / 200000000000 : ℝ)
  moment := (53870371 / 6250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13146 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729608850103 / 500000000000 : ℝ)
    root := (2052583241 / 250000000000 : ℝ) }

noncomputable def scalar13146 : ScalarCertificate 13146 world13146 agent13146 where
  dimensionLo := 13146
  dimensionHi := 13146
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2343289099 / 1000000000000 : ℝ)
  frameLo := (123933084811 / 200000000000 : ℝ)
  frameHi := (729608850103 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13146]
  agentFrame_pos := by norm_num only [agent13146]
  worldRadius := (2343289099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13146]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (500354587 / 500000000000 : ℝ)
  lowerTail := (606664199 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3368282833 / 500000000000 : ℝ)
  ledger := by
    have h : (1153676511 / 1000000000000 : ℚ) +
        (53870371 / 6250000000000000 : ℚ) / (2343289099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (500354587 / 500000000000 : ℚ) + (606664199 / 500000000000 : ℚ) ≤
        (3368282833 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1153676511 / 1000000000000 : ℚ) +
        (53870371 / 6250000000000000 : ℚ) / (2343289099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (500354587 / 500000000000 : ℚ) + (606664199 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3368282833 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13146]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13146 :
    2 * 160 < 13146 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999067 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13146 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13147 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13147. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13147 : WorldParameters where
  hiddenCharge := (288409421 / 250000000000 : ℝ)
  frame := (123930503731 / 200000000000 : ℝ)
  moment := (8617548291 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13147 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364797390273 / 250000000000 : ℝ)
    root := (1026216619 / 125000000000 : ℝ) }

noncomputable def scalar13147 : ScalarCertificate 13147 world13147 agent13147 where
  dimensionLo := 13147
  dimensionHi := 13147
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2343654299 / 1000000000000 : ℝ)
  frameLo := (123930503731 / 200000000000 : ℝ)
  frameHi := (364797390273 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13147]
  agentFrame_pos := by norm_num only [agent13147]
  worldRadius := (2343654299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13147]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (999903513 / 1000000000000 : ℝ)
  lowerTail := (606210829 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6734013761 / 1000000000000 : ℝ)
  ledger := by
    have h : (288409421 / 250000000000 : ℚ) +
        (8617548291 / 1000000000000000000 : ℚ) / (2343654299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (999903513 / 1000000000000 : ℚ) + (606210829 / 500000000000 : ℚ) ≤
        (6734013761 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((288409421 / 250000000000 : ℚ) +
        (8617548291 / 1000000000000000000 : ℚ) / (2343654299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (999903513 / 1000000000000 : ℚ) + (606210829 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6734013761 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13147]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13147 :
    2 * 160 < 13147 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999109 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13147 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13148 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13148. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13148 : WorldParameters where
  hiddenCharge := (1153598867 / 1000000000000 : ℝ)
  frame := (15490990381 / 25000000000 : ℝ)
  moment := (525869 / 61035156250000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13148 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (14591614331 / 10000000000 : ℝ)
    root := (8209133101 / 1000000000000 : ℝ) }

noncomputable def scalar13148 : ScalarCertificate 13148 world13148 agent13148 where
  dimensionLo := 13148
  dimensionHi := 13148
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2344019399 / 1000000000000 : ℝ)
  frameLo := (15490990381 / 25000000000 : ℝ)
  frameHi := (14591614331 / 10000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13148]
  agentFrame_pos := by norm_num only [agent13148]
  worldRadius := (2344019399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13148]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (999098527 / 1000000000000 : ℝ)
  lowerTail := (1211515627 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6731463893 / 1000000000000 : ℝ)
  ledger := by
    have h : (1153598867 / 1000000000000 : ℚ) +
        (525869 / 61035156250000 : ℚ) / (2344019399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (999098527 / 1000000000000 : ℚ) + (1211515627 / 1000000000000 : ℚ) ≤
        (6731463893 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1153598867 / 1000000000000 : ℚ) +
        (525869 / 61035156250000 : ℚ) / (2344019399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (999098527 / 1000000000000 : ℚ) + (1211515627 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6731463893 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13148]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13148 :
    2 * 160 < 13148 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995491 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13148 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13149 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13149. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13149 : WorldParameters where
  hiddenCharge := (1153560059 / 1000000000000 : ℝ)
  frame := (61962671381 / 100000000000 : ℝ)
  moment := (1076765947 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13149 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (11399479033 / 7812500000 : ℝ)
    root := (8208533411 / 1000000000000 : ℝ) }

noncomputable def scalar13149 : ScalarCertificate 13149 world13149 agent13149 where
  dimensionLo := 13149
  dimensionHi := 13149
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2344384699 / 1000000000000 : ℝ)
  frameLo := (61962671381 / 100000000000 : ℝ)
  frameHi := (11399479033 / 7812500000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13149]
  agentFrame_pos := by norm_num only [agent13149]
  worldRadius := (2344384699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13149]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (499147201 / 500000000000 : ℝ)
  lowerTail := (605305259 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6728916059 / 1000000000000 : ℝ)
  ledger := by
    have h : (1153560059 / 1000000000000 : ℚ) +
        (1076765947 / 125000000000000000 : ℚ) / (2344384699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (499147201 / 500000000000 : ℚ) + (605305259 / 500000000000 : ℚ) ≤
        (6728916059 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1153560059 / 1000000000000 : ℚ) +
        (1076765947 / 125000000000000000 : ℚ) / (2344384699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (499147201 / 500000000000 : ℚ) + (605305259 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6728916059 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13149]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13149 :
    2 * 160 < 13149 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998977 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13149 {← IO.monoMsNow}" : IO Unit)
