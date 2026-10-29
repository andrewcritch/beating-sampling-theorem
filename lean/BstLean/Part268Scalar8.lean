import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12550 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12550. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12550 : WorldParameters where
  hiddenCharge := (147338329 / 125000000000 : ℝ)
  frame := (627728513821 / 1000000000000 : ℝ)
  moment := (1945981981 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12550 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (370563942751 / 250000000000 : ℝ)
    root := (8600058943 / 1000000000000 : ℝ) }

noncomputable def scalar12550 : ScalarCertificate 12550 world12550 agent12550 where
  dimensionLo := 12550
  dimensionHi := 12550
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2122186999 / 1000000000000 : ℝ)
  frameLo := (627728513821 / 1000000000000 : ℝ)
  frameHi := (370563942751 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12550]
  agentFrame_pos := by norm_num only [agent12550]
  worldRadius := (2122186999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12550]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1661386239 / 1000000000000 : ℝ)
  lowerTail := (389199357 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4372836109 / 500000000000 : ℝ)
  ledger := by
    have h : (147338329 / 125000000000 : ℚ) +
        (1945981981 / 200000000000000000 : ℚ) / (2122186999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1661386239 / 1000000000000 : ℚ) + (389199357 / 200000000000 : ℚ) ≤
        (4372836109 / 500000000000 : ℚ) := by norm_num only
    have hc : (((147338329 / 125000000000 : ℚ) +
        (1945981981 / 200000000000000000 : ℚ) / (2122186999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1661386239 / 1000000000000 : ℚ) + (389199357 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4372836109 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12550]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12550 :
    2 * 160 < 12550 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (274999997 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12550 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12551 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12551. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12551 : WorldParameters where
  hiddenCharge := (589330627 / 500000000000 : ℝ)
  frame := (627714332001 / 1000000000000 : ℝ)
  moment := (4863941527 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12551 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482221739377 / 1000000000000 : ℝ)
    root := (8599351387 / 1000000000000 : ℝ) }

noncomputable def scalar12551 : ScalarCertificate 12551 world12551 agent12551 where
  dimensionLo := 12551
  dimensionHi := 12551
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2122539999 / 1000000000000 : ℝ)
  frameLo := (627714332001 / 1000000000000 : ℝ)
  frameHi := (1482221739377 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12551]
  agentFrame_pos := by norm_num only [agent12551]
  worldRadius := (2122539999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12551]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1659958269 / 1000000000000 : ℝ)
  lowerTail := (1944442583 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2185369057 / 250000000000 : ℝ)
  ledger := by
    have h : (589330627 / 500000000000 : ℚ) +
        (4863941527 / 500000000000000000 : ℚ) / (2122539999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1659958269 / 1000000000000 : ℚ) + (1944442583 / 1000000000000 : ℚ) ≤
        (2185369057 / 250000000000 : ℚ) := by norm_num only
    have hc : (((589330627 / 500000000000 : ℚ) +
        (4863941527 / 500000000000000000 : ℚ) / (2122539999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1659958269 / 1000000000000 : ℚ) + (1944442583 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2185369057 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12551]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12551 :
    2 * 160 < 12551 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998633 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12551 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12552 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12552. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12552 : WorldParameters where
  hiddenCharge := (73663493 / 62500000000 : ℝ)
  frame := (78462519061 / 125000000000 : ℝ)
  moment := (9725856793 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12552 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (370546930877 / 250000000000 : ℝ)
    root := (8598644051 / 1000000000000 : ℝ) }

noncomputable def scalar12552 : ScalarCertificate 12552 world12552 agent12552 where
  dimensionLo := 12552
  dimensionHi := 12552
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2122892999 / 1000000000000 : ℝ)
  frameLo := (78462519061 / 125000000000 : ℝ)
  frameHi := (370546930877 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12552]
  agentFrame_pos := by norm_num only [agent12552]
  worldRadius := (2122892999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12552]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1658531703 / 1000000000000 : ℝ)
  lowerTail := (1942889821 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4368641941 / 500000000000 : ℝ)
  ledger := by
    have h : (73663493 / 62500000000 : ℚ) +
        (9725856793 / 1000000000000000000 : ℚ) / (2122892999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1658531703 / 1000000000000 : ℚ) + (1942889821 / 1000000000000 : ℚ) ≤
        (4368641941 / 500000000000 : ℚ) := by norm_num only
    have hc : (((73663493 / 62500000000 : ℚ) +
        (9725856793 / 1000000000000000000 : ℚ) / (2122892999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1658531703 / 1000000000000 : ℚ) + (1942889821 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4368641941 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12552]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12552 :
    2 * 160 < 12552 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998997 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12552 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12553 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12553. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12553 : WorldParameters where
  hiddenCharge := (1178570533 / 1000000000000 : ℝ)
  frame := (627685975283 / 1000000000000 : ℝ)
  moment := (9723831121 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12553 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (741076864669 / 500000000000 : ℝ)
    root := (1719587387 / 200000000000 : ℝ) }

noncomputable def scalar12553 : ScalarCertificate 12553 world12553 agent12553 where
  dimensionLo := 12553
  dimensionHi := 12553
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2123246099 / 1000000000000 : ℝ)
  frameLo := (627685975283 / 1000000000000 : ℝ)
  frameHi := (741076864669 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12553]
  agentFrame_pos := by norm_num only [agent12553]
  worldRadius := (2123246099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12553]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1657106667 / 1000000000000 : ℝ)
  lowerTail := (1941338637 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8733095243 / 1000000000000 : ℝ)
  ledger := by
    have h : (1178570533 / 1000000000000 : ℚ) +
        (9723831121 / 1000000000000000000 : ℚ) / (2123246099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1657106667 / 1000000000000 : ℚ) + (1941338637 / 1000000000000 : ℚ) ≤
        (8733095243 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1178570533 / 1000000000000 : ℚ) +
        (9723831121 / 1000000000000000000 : ℚ) / (2123246099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1657106667 / 1000000000000 : ℚ) + (1941338637 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8733095243 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12553]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12553 :
    2 * 160 < 12553 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999797 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12553 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12554 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12554. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12554 : WorldParameters where
  hiddenCharge := (1178525191 / 1000000000000 : ℝ)
  frame := (125534360077 / 200000000000 : ℝ)
  moment := (9721806039 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12554 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (741059878427 / 500000000000 : ℝ)
    root := (8597230037 / 1000000000000 : ℝ) }

noncomputable def scalar12554 : ScalarCertificate 12554 world12554 agent12554 where
  dimensionLo := 12554
  dimensionHi := 12554
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2123599099 / 1000000000000 : ℝ)
  frameLo := (125534360077 / 200000000000 : ℝ)
  frameHi := (741059878427 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12554]
  agentFrame_pos := by norm_num only [agent12554]
  worldRadius := (2123599099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12554]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1655682963 / 1000000000000 : ℝ)
  lowerTail := (1939788819 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (272778447 / 31250000000 : ℝ)
  ledger := by
    have h : (1178525191 / 1000000000000 : ℚ) +
        (9721806039 / 1000000000000000000 : ℚ) / (2123599099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1655682963 / 1000000000000 : ℚ) + (1939788819 / 1000000000000 : ℚ) ≤
        (272778447 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1178525191 / 1000000000000 : ℚ) +
        (9721806039 / 1000000000000000000 : ℚ) / (2123599099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1655682963 / 1000000000000 : ℚ) + (1939788819 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((272778447 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12554]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12554 :
    2 * 160 < 12554 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999301 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12554 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12555 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12555. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12555 : WorldParameters where
  hiddenCharge := (589239931 / 500000000000 : ℝ)
  frame := (313828813897 / 500000000000 : ℝ)
  moment := (4859890773 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12555 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296417160019 / 200000000000 : ℝ)
    root := (4298261679 / 500000000000 : ℝ) }

noncomputable def scalar12555 : ScalarCertificate 12555 world12555 agent12555 where
  dimensionLo := 12555
  dimensionHi := 12555
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2123952199 / 1000000000000 : ℝ)
  frameLo := (313828813897 / 500000000000 : ℝ)
  frameHi := (296417160019 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12555]
  agentFrame_pos := by norm_num only [agent12555]
  worldRadius := (2123952199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12555]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1654260757 / 1000000000000 : ℝ)
  lowerTail := (1938240541 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4362364499 / 500000000000 : ℝ)
  ledger := by
    have h : (589239931 / 500000000000 : ℚ) +
        (4859890773 / 500000000000000000 : ℚ) / (2123952199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1654260757 / 1000000000000 : ℚ) + (1938240541 / 1000000000000 : ℚ) ≤
        (4362364499 / 500000000000 : ℚ) := by norm_num only
    have hc : (((589239931 / 500000000000 : ℚ) +
        (4859890773 / 500000000000000000 : ℚ) / (2123952199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1654260757 / 1000000000000 : ℚ) + (1938240541 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4362364499 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12555]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12555 :
    2 * 160 < 12555 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999691 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12555 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12556 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12556. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12556 : WorldParameters where
  hiddenCharge := (73652159 / 62500000000 : ℝ)
  frame := (156910864377 / 250000000000 : ℝ)
  moment := (4858878821 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12556 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29641037419 / 20000000000 : ℝ)
    root := (4297908449 / 500000000000 : ℝ) }

noncomputable def scalar12556 : ScalarCertificate 12556 world12556 agent12556 where
  dimensionLo := 12556
  dimensionHi := 12556
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2124305299 / 1000000000000 : ℝ)
  frameLo := (156910864377 / 250000000000 : ℝ)
  frameHi := (29641037419 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12556]
  agentFrame_pos := by norm_num only [agent12556]
  worldRadius := (2124305299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12556]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1652840007 / 1000000000000 : ℝ)
  lowerTail := (1936693767 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8720551451 / 1000000000000 : ℝ)
  ledger := by
    have h : (73652159 / 62500000000 : ℚ) +
        (4858878821 / 500000000000000000 : ℚ) / (2124305299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1652840007 / 1000000000000 : ℚ) + (1936693767 / 1000000000000 : ℚ) ≤
        (8720551451 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((73652159 / 62500000000 : ℚ) +
        (4858878821 / 500000000000000000 : ℚ) / (2124305299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1652840007 / 1000000000000 : ℚ) + (1936693767 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8720551451 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12556]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12556 :
    2 * 160 < 12556 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199998857 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12556 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12557 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12557. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12557 : WorldParameters where
  hiddenCharge := (589194619 / 500000000000 : ℝ)
  frame := (627629289527 / 1000000000000 : ℝ)
  moment := (9715734327 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12557 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296403590311 / 200000000000 : ℝ)
    root := (33574651 / 3906250000 : ℝ) }

noncomputable def scalar12557 : ScalarCertificate 12557 world12557 agent12557 where
  dimensionLo := 12557
  dimensionHi := 12557
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2124658399 / 1000000000000 : ℝ)
  frameLo := (627629289527 / 1000000000000 : ℝ)
  frameHi := (296403590311 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12557]
  agentFrame_pos := by norm_num only [agent12557]
  worldRadius := (2124658399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12557]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1651420623 / 1000000000000 : ℝ)
  lowerTail := (483787097 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8716377463 / 1000000000000 : ℝ)
  ledger := by
    have h : (589194619 / 500000000000 : ℚ) +
        (9715734327 / 1000000000000000000 : ℚ) / (2124658399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1651420623 / 1000000000000 : ℚ) + (483787097 / 250000000000 : ℚ) ≤
        (8716377463 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((589194619 / 500000000000 : ℚ) +
        (9715734327 / 1000000000000000000 : ℚ) / (2124658399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1651420623 / 1000000000000 : ℚ) + (483787097 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8716377463 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12557]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12557 :
    2 * 160 < 12557 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (171874987 / 15625000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12557 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12558 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12558. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12558 : WorldParameters where
  hiddenCharge := (235668789 / 200000000000 : ℝ)
  frame := (627615123851 / 1000000000000 : ℝ)
  moment := (24284279 / 2500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12558 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1481984059751 / 1000000000000 : ℝ)
    root := (8594404633 / 1000000000000 : ℝ) }

noncomputable def scalar12558 : ScalarCertificate 12558 world12558 agent12558 where
  dimensionLo := 12558
  dimensionHi := 12558
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2125011399 / 1000000000000 : ℝ)
  frameLo := (627615123851 / 1000000000000 : ℝ)
  frameHi := (1481984059751 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12558]
  agentFrame_pos := by norm_num only [agent12558]
  worldRadius := (2125011399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12558]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (412500649 / 250000000000 : ℝ)
  lowerTail := (386720881 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8712207227 / 1000000000000 : ℝ)
  ledger := by
    have h : (235668789 / 200000000000 : ℚ) +
        (24284279 / 2500000000000000 : ℚ) / (2125011399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (412500649 / 250000000000 : ℚ) + (386720881 / 200000000000 : ℚ) ≤
        (8712207227 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((235668789 / 200000000000 : ℚ) +
        (24284279 / 2500000000000000 : ℚ) / (2125011399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (412500649 / 250000000000 : ℚ) + (386720881 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8712207227 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12558]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12558 :
    2 * 160 < 12558 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998051 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12558 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12559 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12559. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12559 : WorldParameters where
  hiddenCharge := (147287333 / 125000000000 : ℝ)
  frame := (627600960479 / 1000000000000 : ℝ)
  moment := (4855844731 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12559 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (11855601469 / 8000000000 : ℝ)
    root := (2148424707 / 250000000000 : ℝ) }

noncomputable def scalar12559 : ScalarCertificate 12559 world12559 agent12559 where
  dimensionLo := 12559
  dimensionHi := 12559
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2125364499 / 1000000000000 : ℝ)
  frameLo := (627600960479 / 1000000000000 : ℝ)
  frameHi := (11855601469 / 8000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12559]
  agentFrame_pos := by norm_num only [agent12559]
  worldRadius := (2125364499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12559]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1648586059 / 1000000000000 : ℝ)
  lowerTail := (386412391 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4354020303 / 500000000000 : ℝ)
  ledger := by
    have h : (147287333 / 125000000000 : ℚ) +
        (4855844731 / 500000000000000000 : ℚ) / (2125364499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1648586059 / 1000000000000 : ℚ) + (386412391 / 200000000000 : ℚ) ≤
        (4354020303 / 500000000000 : ℚ) := by norm_num only
    have hc : (((147287333 / 125000000000 : ℚ) +
        (4855844731 / 500000000000000000 : ℚ) / (2125364499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1648586059 / 1000000000000 : ℚ) + (386412391 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4354020303 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12559]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12559 :
    2 * 160 < 12559 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999301 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12559 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12560 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12560. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12560 : WorldParameters where
  hiddenCharge := (589126697 / 500000000000 : ℝ)
  frame := (627586799411 / 1000000000000 : ℝ)
  moment := (1213708489 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12560 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (370458329089 / 250000000000 : ℝ)
    root := (8592993241 / 1000000000000 : ℝ) }

noncomputable def scalar12560 : ScalarCertificate 12560 world12560 agent12560 where
  dimensionLo := 12560
  dimensionHi := 12560
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2125827899 / 1000000000000 : ℝ)
  frameLo := (627586799411 / 1000000000000 : ℝ)
  frameHi := (370458329089 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12560]
  agentFrame_pos := by norm_num only [agent12560]
  worldRadius := (2125827899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12560]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1646870551 / 1000000000000 : ℝ)
  lowerTail := (1930137821 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (543935697 / 62500000000 : ℝ)
  ledger := by
    have h : (589126697 / 500000000000 : ℚ) +
        (1213708489 / 125000000000000000 : ℚ) / (2125827899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1646870551 / 1000000000000 : ℚ) + (1930137821 / 1000000000000 : ℚ) ≤
        (543935697 / 62500000000 : ℚ) := by norm_num only
    have hc : (((589126697 / 500000000000 : ℚ) +
        (1213708489 / 125000000000000000 : ℚ) / (2125827899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1646870551 / 1000000000000 : ℚ) + (1930137821 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((543935697 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12560]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12560 :
    2 * 160 < 12560 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998187 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12560 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12561 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12561. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12561 : WorldParameters where
  hiddenCharge := (1178208137 / 1000000000000 : ℝ)
  frame := (125514528129 / 200000000000 : ℝ)
  moment := (194152939 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12561 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296359895701 / 200000000000 : ℝ)
    root := (8592287873 / 1000000000000 : ℝ) }

noncomputable def scalar12561 : ScalarCertificate 12561 world12561 agent12561 where
  dimensionLo := 12561
  dimensionHi := 12561
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2126181099 / 1000000000000 : ℝ)
  frameLo := (125514528129 / 200000000000 : ℝ)
  frameHi := (296359895701 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12561]
  agentFrame_pos := by norm_num only [agent12561]
  worldRadius := (2126181099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12561]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (411364283 / 250000000000 : ℝ)
  lowerTail := (1928598613 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8698812439 / 1000000000000 : ℝ)
  ledger := by
    have h : (1178208137 / 1000000000000 : ℚ) +
        (194152939 / 20000000000000000 : ℚ) / (2126181099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (411364283 / 250000000000 : ℚ) + (1928598613 / 1000000000000 : ℚ) ≤
        (8698812439 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1178208137 / 1000000000000 : ℚ) +
        (194152939 / 20000000000000000 : ℚ) / (2126181099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (411364283 / 250000000000 : ℚ) + (1928598613 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8698812439 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12561]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12561 :
    2 * 160 < 12561 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999933 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12561 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12562 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12562. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12562 : WorldParameters where
  hiddenCharge := (294540723 / 250000000000 : ℝ)
  frame := (627558484181 / 1000000000000 : ℝ)
  moment := (606601661 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12562 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1481765668197 / 1000000000000 : ℝ)
    root := (8591582653 / 1000000000000 : ℝ) }

noncomputable def scalar12562 : ScalarCertificate 12562 world12562 agent12562 where
  dimensionLo := 12562
  dimensionHi := 12562
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2126534199 / 1000000000000 : ℝ)
  frameLo := (627558484181 / 1000000000000 : ℝ)
  frameHi := (1481765668197 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12562]
  agentFrame_pos := by norm_num only [agent12562]
  worldRadius := (2126534199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12562]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1644044997 / 1000000000000 : ℝ)
  lowerTail := (1927060727 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (869465733 / 100000000000 : ℝ)
  ledger := by
    have h : (294540723 / 250000000000 : ℚ) +
        (606601661 / 62500000000000000 : ℚ) / (2126534199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1644044997 / 1000000000000 : ℚ) + (1927060727 / 1000000000000 : ℚ) ≤
        (869465733 / 100000000000 : ℚ) := by norm_num only
    have hc : (((294540723 / 250000000000 : ℚ) +
        (606601661 / 62500000000000000 : ℚ) / (2126534199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1644044997 / 1000000000000 : ℚ) + (1927060727 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((869465733 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12562]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12562 :
    2 * 160 < 12562 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994891 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12562 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12563 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12563. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12563 : WorldParameters where
  hiddenCharge := (58905883 / 50000000000 : ℝ)
  frame := (627544330019 / 1000000000000 : ℝ)
  moment := (9703606789 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12563 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (18521648419 / 12500000000 : ℝ)
    root := (214771943 / 25000000000 : ℝ) }

noncomputable def scalar12563 : ScalarCertificate 12563 world12563 agent12563 where
  dimensionLo := 12563
  dimensionHi := 12563
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2126887299 / 1000000000000 : ℝ)
  frameLo := (627544330019 / 1000000000000 : ℝ)
  frameHi := (18521648419 / 12500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12563]
  agentFrame_pos := by norm_num only [agent12563]
  worldRadius := (2126887299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12563]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1642634313 / 1000000000000 : ℝ)
  lowerTail := (1925524329 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (271578311 / 31250000000 : ℝ)
  ledger := by
    have h : (58905883 / 50000000000 : ℚ) +
        (9703606789 / 1000000000000000000 : ℚ) / (2126887299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1642634313 / 1000000000000 : ℚ) + (1925524329 / 1000000000000 : ℚ) ≤
        (271578311 / 31250000000 : ℚ) := by norm_num only
    have hc : (((58905883 / 50000000000 : ℚ) +
        (9703606789 / 1000000000000000000 : ℚ) / (2126887299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1642634313 / 1000000000000 : ℚ) + (1925524329 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((271578311 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12563]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12563 :
    2 * 160 < 12563 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199998837 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12563 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12564 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12564. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12564 : WorldParameters where
  hiddenCharge := (1178072439 / 1000000000000 : ℝ)
  frame := (313765089079 / 500000000000 : ℝ)
  moment := (9701587589 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12564 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296339618893 / 200000000000 : ℝ)
    root := (2147543251 / 250000000000 : ℝ) }

noncomputable def scalar12564 : ScalarCertificate 12564 world12564 agent12564 where
  dimensionLo := 12564
  dimensionHi := 12564
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2127240399 / 1000000000000 : ℝ)
  frameLo := (313765089079 / 500000000000 : ℝ)
  frameHi := (296339618893 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12564]
  agentFrame_pos := by norm_num only [agent12564]
  worldRadius := (2127240399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12564]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (328245003 / 200000000000 : ℝ)
  lowerTail := (38479787 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4343179087 / 500000000000 : ℝ)
  ledger := by
    have h : (1178072439 / 1000000000000 : ℚ) +
        (9701587589 / 1000000000000000000 : ℚ) / (2127240399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (328245003 / 200000000000 : ℚ) + (38479787 / 20000000000 : ℚ) ≤
        (4343179087 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1178072439 / 1000000000000 : ℚ) +
        (9701587589 / 1000000000000000000 : ℚ) / (2127240399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (328245003 / 200000000000 : ℚ) + (38479787 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4343179087 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12564]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12564 :
    2 * 160 < 12564 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998763 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12564 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12565 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12565. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12565 : WorldParameters where
  hiddenCharge := (117802723 / 100000000000 : ℝ)
  frame := (627516028597 / 1000000000000 : ℝ)
  moment := (9699568977 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12565 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185208042121 / 125000000000 : ℝ)
    root := (4294734253 / 500000000000 : ℝ) }

noncomputable def scalar12565 : ScalarCertificate 12565 world12565 agent12565 where
  dimensionLo := 12565
  dimensionHi := 12565
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2127593599 / 1000000000000 : ℝ)
  frameLo := (627516028597 / 1000000000000 : ℝ)
  frameHi := (185208042121 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12565]
  agentFrame_pos := by norm_num only [agent12565]
  worldRadius := (2127593599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12565]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (65592689 / 40000000000 : ℝ)
  lowerTail := (192245593 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8682214053 / 1000000000000 : ℝ)
  ledger := by
    have h : (117802723 / 100000000000 : ℚ) +
        (9699568977 / 1000000000000000000 : ℚ) / (2127593599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (65592689 / 40000000000 : ℚ) + (192245593 / 100000000000 : ℚ) ≤
        (8682214053 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((117802723 / 100000000000 : ℚ) +
        (9699568977 / 1000000000000000000 : ℚ) / (2127593599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (65592689 / 40000000000 : ℚ) + (192245593 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8682214053 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12565]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12565 :
    2 * 160 < 12565 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999701 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12565 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12566 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12566. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12566 : WorldParameters where
  hiddenCharge := (588991017 / 500000000000 : ℝ)
  frame := (78437735167 / 125000000000 : ℝ)
  moment := (9697550951 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12566 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1481630601017 / 1000000000000 : ℝ)
    root := (4294382113 / 500000000000 : ℝ) }

noncomputable def scalar12566 : ScalarCertificate 12566 world12566 agent12566 where
  dimensionLo := 12566
  dimensionHi := 12566
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2127946699 / 1000000000000 : ℝ)
  frameLo := (78437735167 / 125000000000 : ℝ)
  frameHi := (1481630601017 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12566]
  agentFrame_pos := by norm_num only [agent12566]
  worldRadius := (2127946699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12566]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (6553643 / 4000000000 : ℝ)
  lowerTail := (960461929 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4339036793 / 500000000000 : ℝ)
  ledger := by
    have h : (588991017 / 500000000000 : ℚ) +
        (9697550951 / 1000000000000000000 : ℚ) / (2127946699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (6553643 / 4000000000 : ℚ) + (960461929 / 500000000000 : ℚ) ≤
        (4339036793 / 500000000000 : ℚ) := by norm_num only
    have hc : (((588991017 / 500000000000 : ℚ) +
        (9697550951 / 1000000000000000000 : ℚ) / (2127946699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (6553643 / 4000000000 : ℚ) + (960461929 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4339036793 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12566]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12566 :
    2 * 160 < 12566 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997991 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12566 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12567 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12567. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12567 : WorldParameters where
  hiddenCharge := (1177936849 / 1000000000000 : ℝ)
  frame := (313743868187 / 500000000000 : ℝ)
  moment := (1211941689 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12567 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740798443301 / 500000000000 : ℝ)
    root := (4294030081 / 500000000000 : ℝ) }

noncomputable def scalar12567 : ScalarCertificate 12567 world12567 agent12567 where
  dimensionLo := 12567
  dimensionHi := 12567
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2128299899 / 1000000000000 : ℝ)
  frameLo := (313743868187 / 500000000000 : ℝ)
  frameHi := (740798443301 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12567]
  agentFrame_pos := by norm_num only [agent12567]
  worldRadius := (2128299899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12567]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1637005779 / 1000000000000 : ℝ)
  lowerTail := (95969667 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8673936771 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177936849 / 1000000000000 : ℚ) +
        (1211941689 / 125000000000000000 : ℚ) / (2128299899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1637005779 / 1000000000000 : ℚ) + (95969667 / 50000000000 : ℚ) ≤
        (8673936771 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177936849 / 1000000000000 : ℚ) +
        (1211941689 / 125000000000000000 : ℚ) / (2128299899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1637005779 / 1000000000000 : ℚ) + (95969667 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8673936771 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12567]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12567 :
    2 * 160 < 12567 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999753 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12567 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12568 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12568. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12568 : WorldParameters where
  hiddenCharge := (1177891677 / 1000000000000 : ℝ)
  frame := (627473593711 / 1000000000000 : ℝ)
  moment := (9693516659 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12568 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740781593881 / 500000000000 : ℝ)
    root := (2146839079 / 250000000000 : ℝ) }

noncomputable def scalar12568 : ScalarCertificate 12568 world12568 agent12568 where
  dimensionLo := 12568
  dimensionHi := 12568
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2128652999 / 1000000000000 : ℝ)
  frameLo := (627473593711 / 1000000000000 : ℝ)
  frameHi := (740781593881 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12568]
  agentFrame_pos := by norm_num only [agent12568]
  worldRadius := (2128652999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12568]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1635602091 / 1000000000000 : ℝ)
  lowerTail := (479466033 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8669803537 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177891677 / 1000000000000 : ℚ) +
        (9693516659 / 1000000000000000000 : ℚ) / (2128652999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1635602091 / 1000000000000 : ℚ) + (479466033 / 250000000000 : ℚ) ≤
        (8669803537 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177891677 / 1000000000000 : ℚ) +
        (9693516659 / 1000000000000000000 : ℚ) / (2128652999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1635602091 / 1000000000000 : ℚ) + (479466033 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8669803537 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12568]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12568 :
    2 * 160 < 12568 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998039 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12568 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12569 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12569. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12569 : WorldParameters where
  hiddenCharge := (1177846517 / 1000000000000 : ℝ)
  frame := (313729726673 / 500000000000 : ℝ)
  moment := (9691500393 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12569 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740764755217 / 500000000000 : ℝ)
    root := (4293326309 / 500000000000 : ℝ) }

noncomputable def scalar12569 : ScalarCertificate 12569 world12569 agent12569 where
  dimensionLo := 12569
  dimensionHi := 12569
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2129006099 / 1000000000000 : ℝ)
  frameLo := (313729726673 / 500000000000 : ℝ)
  frameHi := (740764755217 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12569]
  agentFrame_pos := by norm_num only [agent12569]
  worldRadius := (2129006099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12569]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (817099871 / 500000000000 : ℝ)
  lowerTail := (383267261 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8665673817 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177846517 / 1000000000000 : ℚ) +
        (9691500393 / 1000000000000000000 : ℚ) / (2129006099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (817099871 / 500000000000 : ℚ) + (383267261 / 200000000000 : ℚ) ≤
        (8665673817 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177846517 / 1000000000000 : ℚ) +
        (9691500393 / 1000000000000000000 : ℚ) / (2129006099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (817099871 / 500000000000 : ℚ) + (383267261 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8665673817 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12569]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12569 :
    2 * 160 < 12569 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994927 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12569 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12570 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12570. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12570 : WorldParameters where
  hiddenCharge := (1177801369 / 1000000000000 : ℝ)
  frame := (313722657639 / 500000000000 : ℝ)
  moment := (1211185589 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12570 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185176619673 / 125000000000 : ℝ)
    root := (1717189841 / 200000000000 : ℝ) }

noncomputable def scalar12570 : ScalarCertificate 12570 world12570 agent12570 where
  dimensionLo := 12570
  dimensionHi := 12570
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2129469799 / 1000000000000 : ℝ)
  frameLo := (313722657639 / 500000000000 : ℝ)
  frameHi := (185176619673 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12570]
  agentFrame_pos := by norm_num only [agent12570]
  worldRadius := (2129469799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12570]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (326500283 / 200000000000 : ℝ)
  lowerTail := (1914430321 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4330324387 / 500000000000 : ℝ)
  ledger := by
    have h : (1177801369 / 1000000000000 : ℚ) +
        (1211185589 / 125000000000000000 : ℚ) / (2129469799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (326500283 / 200000000000 : ℚ) + (1914430321 / 1000000000000 : ℚ) ≤
        (4330324387 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1177801369 / 1000000000000 : ℚ) +
        (1211185589 / 125000000000000000 : ℚ) / (2129469799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (326500283 / 200000000000 : ℚ) + (1914430321 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4330324387 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12570]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12570 :
    2 * 160 < 12570 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997677 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12570 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12571 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12571. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12571 : WorldParameters where
  hiddenCharge := (1177756233 / 1000000000000 : ℝ)
  frame := (156857794877 / 250000000000 : ℝ)
  moment := (9687469617 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12571 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296275863619 / 200000000000 : ℝ)
    root := (8585246009 / 1000000000000 : ℝ) }

noncomputable def scalar12571 : ScalarCertificate 12571 world12571 agent12571 where
  dimensionLo := 12571
  dimensionHi := 12571
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2129823099 / 1000000000000 : ℝ)
  frameLo := (156857794877 / 250000000000 : ℝ)
  frameHi := (296275863619 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12571]
  agentFrame_pos := by norm_num only [agent12571]
  worldRadius := (2129823099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12571]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (203887789 / 125000000000 : ℝ)
  lowerTail := (1912905871 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (270516469 / 31250000000 : ℝ)
  ledger := by
    have h : (1177756233 / 1000000000000 : ℚ) +
        (9687469617 / 1000000000000000000 : ℚ) / (2129823099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (203887789 / 125000000000 : ℚ) + (1912905871 / 1000000000000 : ℚ) ≤
        (270516469 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1177756233 / 1000000000000 : ℚ) +
        (9687469617 / 1000000000000000000 : ℚ) / (2129823099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (203887789 / 125000000000 : ℚ) + (1912905871 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((270516469 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12571]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12571 :
    2 * 160 < 12571 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998207 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12571 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12572 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12572. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12572 : WorldParameters where
  hiddenCharge := (1177711109 / 1000000000000 : ℝ)
  frame := (627417046033 / 1000000000000 : ℝ)
  moment := (2421363777 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12572 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740672850141 / 500000000000 : ℝ)
    root := (8584543029 / 1000000000000 : ℝ) }

noncomputable def scalar12572 : ScalarCertificate 12572 world12572 agent12572 where
  dimensionLo := 12572
  dimensionHi := 12572
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2130176299 / 1000000000000 : ℝ)
  frameLo := (627417046033 / 1000000000000 : ℝ)
  frameHi := (740672850141 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12572]
  agentFrame_pos := by norm_num only [agent12572]
  worldRadius := (2130176299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12572]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1629704513 / 1000000000000 : ℝ)
  lowerTail := (955691379 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8652408871 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177711109 / 1000000000000 : ℚ) +
        (2421363777 / 250000000000000000 : ℚ) / (2130176299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1629704513 / 1000000000000 : ℚ) + (955691379 / 500000000000 : ℚ) ≤
        (8652408871 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177711109 / 1000000000000 : ℚ) +
        (2421363777 / 250000000000000000 : ℚ) / (2130176299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1629704513 / 1000000000000 : ℚ) + (955691379 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8652408871 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12572]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12572 :
    2 * 160 < 12572 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996489 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12572 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12573 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12573. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12573 : WorldParameters where
  hiddenCharge := (1177665997 / 1000000000000 : ℝ)
  frame := (313701457427 / 500000000000 : ℝ)
  moment := (302607537 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12573 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1481312097989 / 1000000000000 : ℝ)
    root := (4291920133 / 500000000000 : ℝ) }

noncomputable def scalar12573 : ScalarCertificate 12573 world12573 agent12573 where
  dimensionLo := 12573
  dimensionHi := 12573
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2130529499 / 1000000000000 : ℝ)
  frameLo := (313701457427 / 500000000000 : ℝ)
  frameHi := (1481312097989 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12573]
  agentFrame_pos := by norm_num only [agent12573]
  worldRadius := (2130529499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12573]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (407077021 / 250000000000 : ℝ)
  lowerTail := (38197221 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8648294299 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177665997 / 1000000000000 : ℚ) +
        (302607537 / 31250000000000000 : ℚ) / (2130529499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (407077021 / 250000000000 : ℚ) + (38197221 / 20000000000 : ℚ) ≤
        (8648294299 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177665997 / 1000000000000 : ℚ) +
        (302607537 / 31250000000000000 : ℚ) / (2130529499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (407077021 / 250000000000 : ℚ) + (38197221 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8648294299 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12573]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12573 :
    2 * 160 < 12573 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998601 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12573 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12574 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12574. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12574 : WorldParameters where
  hiddenCharge := (1177620897 / 1000000000000 : ℝ)
  frame := (62738878597 / 100000000000 : ℝ)
  moment := (1936285569 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12574 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29625570343 / 20000000000 : ℝ)
    root := (8583137651 / 1000000000000 : ℝ) }

noncomputable def scalar12574 : ScalarCertificate 12574 world12574 agent12574 where
  dimensionLo := 12574
  dimensionHi := 12574
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2130882699 / 1000000000000 : ℝ)
  frameLo := (62738878597 / 100000000000 : ℝ)
  frameHi := (29625570343 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12574]
  agentFrame_pos := by norm_num only [agent12574]
  worldRadius := (2130882699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12574]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1626912987 / 1000000000000 : ℝ)
  lowerTail := (1908340717 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8644183221 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177620897 / 1000000000000 : ℚ) +
        (1936285569 / 200000000000000000 : ℚ) / (2130882699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1626912987 / 1000000000000 : ℚ) + (1908340717 / 1000000000000 : ℚ) ≤
        (8644183221 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177620897 / 1000000000000 : ℚ) +
        (1936285569 / 200000000000000000 : ℚ) / (2130882699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1626912987 / 1000000000000 : ℚ) + (1908340717 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8644183221 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12574]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12574 :
    2 * 160 < 12574 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499901 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12574 {← IO.monoMsNow}" : IO Unit)
