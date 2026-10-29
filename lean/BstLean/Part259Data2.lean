import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12235 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12235. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12235 : WorldParameters where
  hiddenCharge := (119362927 / 100000000000 : ℝ)
  frame := (632313907913 / 1000000000000 : ℝ)
  moment := (2599732537 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12235 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1902654211 / 1000000000000 : ℝ)
    frame := (729813875087 / 500000000000 : ℝ)
    root := (8842398151 / 1000000000000 : ℝ) }

noncomputable def scalar12235 : ScalarCertificate 12235 world12235 agent12235 where
  dimensionLo := 12235
  dimensionHi := 12235
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2051996799 / 1000000000000 : ℝ)
  frameLo := (632313907913 / 1000000000000 : ℝ)
  frameHi := (729813875087 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12235]
  agentFrame_pos := by norm_num only [agent12235]
  worldRadius := (2051996799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12235]
  retainedCharge := (1902654211 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2041897219 / 1000000000000 : ℝ)
  lowerTail := (2329214439 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1242130691 / 125000000000 : ℝ)
  ledger := by
    have h : (119362927 / 100000000000 : ℚ) +
        (2599732537 / 250000000000000000 : ℚ) / (2051996799 / 1000000000000 : ℚ) ^ 2 +
        (1902654211 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2041897219 / 1000000000000 : ℚ) + (2329214439 / 1000000000000 : ℚ) ≤
        (1242130691 / 125000000000 : ℚ) := by norm_num only
    have hc : (((119362927 / 100000000000 : ℚ) +
        (2599732537 / 250000000000000000 : ℚ) / (2051996799 / 1000000000000 : ℚ) ^ 2 +
        (1902654211 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2041897219 / 1000000000000 : ℚ) + (2329214439 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1242130691 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12235]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12235 :
    2 * 160 < 12235 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995833 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12235 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12236 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12236. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12236 : WorldParameters where
  hiddenCharge := (1193579839 / 1000000000000 : ℝ)
  frame := (126459793607 / 200000000000 : ℝ)
  moment := (10396705957 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12236 : AgentParameters :=
  { agentLedgerParameters with
    charge := (76075907 / 40000000000 : ℝ)
    frame := (1459586352311 / 1000000000000 : ℝ)
    root := (1768331069 / 200000000000 : ℝ) }

noncomputable def scalar12236 : ScalarCertificate 12236 world12236 agent12236 where
  dimensionLo := 12236
  dimensionHi := 12236
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2052351099 / 1000000000000 : ℝ)
  frameLo := (126459793607 / 200000000000 : ℝ)
  frameHi := (1459586352311 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12236]
  agentFrame_pos := by norm_num only [agent12236]
  worldRadius := (2052351099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12236]
  retainedCharge := (76075907 / 40000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (408015929 / 200000000000 : ℝ)
  lowerTail := (290909627 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9931103919 / 1000000000000 : ℝ)
  ledger := by
    have h : (1193579839 / 1000000000000 : ℚ) +
        (10396705957 / 1000000000000000000 : ℚ) / (2052351099 / 1000000000000 : ℚ) ^ 2 +
        (76075907 / 40000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (408015929 / 200000000000 : ℚ) + (290909627 / 125000000000 : ℚ) ≤
        (9931103919 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1193579839 / 1000000000000 : ℚ) +
        (10396705957 / 1000000000000000000 : ℚ) / (2052351099 / 1000000000000 : ℚ) ^ 2 +
        (76075907 / 40000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (408015929 / 200000000000 : ℚ) + (290909627 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9931103919 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12236]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12236 :
    2 * 160 < 12236 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2749998679 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12236 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12237 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12237. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12237 : WorldParameters where
  hiddenCharge := (1193530421 / 1000000000000 : ℝ)
  frame := (126456806133 / 200000000000 : ℝ)
  moment := (10394482431 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12237 : AgentParameters :=
  { agentLedgerParameters with
    charge := (76045673 / 40000000000 : ℝ)
    frame := (364886242391 / 250000000000 : ℝ)
    root := (88409127 / 10000000000 : ℝ) }

noncomputable def scalar12237 : ScalarCertificate 12237 world12237 agent12237 where
  dimensionLo := 12237
  dimensionHi := 12237
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2052705499 / 1000000000000 : ℝ)
  frameLo := (126456806133 / 200000000000 : ℝ)
  frameHi := (364886242391 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12237]
  agentFrame_pos := by norm_num only [agent12237]
  worldRadius := (2052705499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12237]
  retainedCharge := (76045673 / 40000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2038263921 / 1000000000000 : ℝ)
  lowerTail := (2325341461 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1240645931 / 125000000000 : ℝ)
  ledger := by
    have h : (1193530421 / 1000000000000 : ℚ) +
        (10394482431 / 1000000000000000000 : ℚ) / (2052705499 / 1000000000000 : ℚ) ^ 2 +
        (76045673 / 40000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2038263921 / 1000000000000 : ℚ) + (2325341461 / 1000000000000 : ℚ) ≤
        (1240645931 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1193530421 / 1000000000000 : ℚ) +
        (10394482431 / 1000000000000000000 : ℚ) / (2052705499 / 1000000000000 : ℚ) ^ 2 +
        (76045673 / 40000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2038263921 / 1000000000000 : ℚ) + (2325341461 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1240645931 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12237]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12237 :
    2 * 160 < 12237 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998537 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12237 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12238 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12238. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12238 : WorldParameters where
  hiddenCharge := (1193481017 / 1000000000000 : ℝ)
  frame := (632269095803 / 1000000000000 : ℝ)
  moment := (10392259569 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12238 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1900386657 / 1000000000000 : ℝ)
    frame := (729751806843 / 500000000000 : ℝ)
    root := (8840170291 / 1000000000000 : ℝ) }

noncomputable def scalar12238 : ScalarCertificate 12238 world12238 agent12238 where
  dimensionLo := 12238
  dimensionHi := 12238
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2053059899 / 1000000000000 : ℝ)
  frameLo := (632269095803 / 1000000000000 : ℝ)
  frameHi := (729751806843 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12238]
  agentFrame_pos := by norm_num only [agent12238]
  worldRadius := (2053059899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12238]
  retainedCharge := (1900386657 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1018225041 / 500000000000 : ℝ)
  lowerTail := (464681563 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (619952277 / 62500000000 : ℝ)
  ledger := by
    have h : (1193481017 / 1000000000000 : ℚ) +
        (10392259569 / 1000000000000000000 : ℚ) / (2053059899 / 1000000000000 : ℚ) ^ 2 +
        (1900386657 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1018225041 / 500000000000 : ℚ) + (464681563 / 200000000000 : ℚ) ≤
        (619952277 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1193481017 / 1000000000000 : ℚ) +
        (10392259569 / 1000000000000000000 : ℚ) / (2053059899 / 1000000000000 : ℚ) ^ 2 +
        (1900386657 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1018225041 / 500000000000 : ℚ) + (464681563 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((619952277 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12238]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12238 :
    2 * 160 < 12238 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (687499709 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12238 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12239 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12239. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12239 : WorldParameters where
  hiddenCharge := (1193431627 / 1000000000000 : ℝ)
  frame := (316127081723 / 500000000000 : ℝ)
  moment := (10390037371 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12239 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1899632173 / 1000000000000 : ℝ)
    frame := (182432784113 / 125000000000 : ℝ)
    root := (8839428119 / 1000000000000 : ℝ) }

noncomputable def scalar12239 : ScalarCertificate 12239 world12239 agent12239 where
  dimensionLo := 12239
  dimensionHi := 12239
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2053414299 / 1000000000000 : ℝ)
  frameLo := (316127081723 / 500000000000 : ℝ)
  frameHi := (182432784113 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12239]
  agentFrame_pos := by norm_num only [agent12239]
  worldRadius := (2053414299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12239]
  retainedCharge := (1899632173 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2034638057 / 1000000000000 : ℝ)
  lowerTail := (2321475993 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9913310713 / 1000000000000 : ℝ)
  ledger := by
    have h : (1193431627 / 1000000000000 : ℚ) +
        (10390037371 / 1000000000000000000 : ℚ) / (2053414299 / 1000000000000 : ℚ) ^ 2 +
        (1899632173 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2034638057 / 1000000000000 : ℚ) + (2321475993 / 1000000000000 : ℚ) ≤
        (9913310713 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1193431627 / 1000000000000 : ℚ) +
        (10390037371 / 1000000000000000000 : ℚ) / (2053414299 / 1000000000000 : ℚ) ^ 2 +
        (1899632173 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2034638057 / 1000000000000 : ℚ) + (2321475993 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9913310713 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12239]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12239 :
    2 * 160 < 12239 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998517 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12239 {← IO.monoMsNow}" : IO Unit)
