import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12900 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12900. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12900 : WorldParameters where
  hiddenCharge := (46541509 / 40000000000 : ℝ)
  frame := (311450864741 / 500000000000 : ℝ)
  moment := (2263759803 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12900 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367061627831 / 250000000000 : ℝ)
    root := (26134591 / 3125000000 : ℝ) }

noncomputable def scalar12900 : ScalarCertificate 12900 world12900 agent12900 where
  dimensionLo := 12900
  dimensionHi := 12900
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2251232399 / 1000000000000 : ℝ)
  frameLo := (311450864741 / 500000000000 : ℝ)
  frameHi := (367061627831 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12900]
  agentFrame_pos := by norm_num only [agent12900]
  worldRadius := (2251232399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12900]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (119967 / 97656250 : ℝ)
  lowerTail := (1468758521 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1489319249 / 200000000000 : ℝ)
  ledger := by
    have h : (46541509 / 40000000000 : ℚ) +
        (2263759803 / 250000000000000000 : ℚ) / (2251232399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119967 / 97656250 : ℚ) + (1468758521 / 1000000000000 : ℚ) ≤
        (1489319249 / 200000000000 : ℚ) := by norm_num only
    have hc : (((46541509 / 40000000000 : ℚ) +
        (2263759803 / 250000000000000000 : ℚ) / (2251232399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119967 / 97656250 : ℚ) + (1468758521 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1489319249 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12900]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12900 :
    2 * 160 < 12900 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998893 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12900 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12901 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12901. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12901 : WorldParameters where
  hiddenCharge := (232699271 / 200000000000 : ℝ)
  frame := (622888320373 / 1000000000000 : ℝ)
  moment := (2263301513 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12901 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734108163583 / 500000000000 : ℝ)
    root := (4181213263 / 500000000000 : ℝ) }

noncomputable def scalar12901 : ScalarCertificate 12901 world12901 agent12901 where
  dimensionLo := 12901
  dimensionHi := 12901
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2251592999 / 1000000000000 : ℝ)
  frameLo := (622888320373 / 1000000000000 : ℝ)
  frameHi := (734108163583 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12901]
  agentFrame_pos := by norm_num only [agent12901]
  worldRadius := (2251592999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12901]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (24548917 / 20000000000 : ℝ)
  lowerTail := (1467630397 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1488695337 / 200000000000 : ℝ)
  ledger := by
    have h : (232699271 / 200000000000 : ℚ) +
        (2263301513 / 250000000000000000 : ℚ) / (2251592999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (24548917 / 20000000000 : ℚ) + (1467630397 / 1000000000000 : ℚ) ≤
        (1488695337 / 200000000000 : ℚ) := by norm_num only
    have hc : (((232699271 / 200000000000 : ℚ) +
        (2263301513 / 250000000000000000 : ℚ) / (2251592999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (24548917 / 20000000000 : ℚ) + (1467630397 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1488695337 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12901]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12901 :
    2 * 160 < 12901 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999849 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12901 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12902 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12902. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12902 : WorldParameters where
  hiddenCharge := (232690999 / 200000000000 : ℝ)
  frame := (4982999307 / 8000000000 : ℝ)
  moment := (9051373411 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12902 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367046540381 / 250000000000 : ℝ)
    root := (4180892027 / 500000000000 : ℝ) }

noncomputable def scalar12902 : ScalarCertificate 12902 world12902 agent12902 where
  dimensionLo := 12902
  dimensionHi := 12902
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2251953599 / 1000000000000 : ℝ)
  frameLo := (4982999307 / 8000000000 : ℝ)
  frameHi := (367046540381 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12902]
  agentFrame_pos := by norm_num only [agent12902]
  worldRadius := (2251953599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12902]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (245286111 / 200000000000 : ℝ)
  lowerTail := (733251627 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3720179829 / 500000000000 : ℝ)
  ledger := by
    have h : (232690999 / 200000000000 : ℚ) +
        (9051373411 / 1000000000000000000 : ℚ) / (2251953599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (245286111 / 200000000000 : ℚ) + (733251627 / 500000000000 : ℚ) ≤
        (3720179829 / 500000000000 : ℚ) := by norm_num only
    have hc : (((232690999 / 200000000000 : ℚ) +
        (9051373411 / 1000000000000000000 : ℚ) / (2251953599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (245286111 / 200000000000 : ℚ) + (733251627 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3720179829 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12902]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12902 :
    2 * 160 < 12902 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999463 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12902 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12903 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12903. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12903 : WorldParameters where
  hiddenCharge := (581706823 / 500000000000 : ℝ)
  frame := (622861508487 / 1000000000000 : ℝ)
  moment := (9049541287 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12903 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146815600851 / 100000000000 : ℝ)
    root := (4180570917 / 500000000000 : ℝ) }

noncomputable def scalar12903 : ScalarCertificate 12903 world12903 agent12903 where
  dimensionLo := 12903
  dimensionHi := 12903
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2252314199 / 1000000000000 : ℝ)
  frameLo := (622861508487 / 1000000000000 : ℝ)
  frameHi := (146815600851 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12903]
  agentFrame_pos := by norm_num only [agent12903]
  worldRadius := (2252314199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12903]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1225416267 / 1000000000000 : ℝ)
  lowerTail := (1465377161 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (743724531 / 100000000000 : ℝ)
  ledger := by
    have h : (581706823 / 500000000000 : ℚ) +
        (9049541287 / 1000000000000000000 : ℚ) / (2252314199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1225416267 / 1000000000000 : ℚ) + (1465377161 / 1000000000000 : ℚ) ≤
        (743724531 / 100000000000 : ℚ) := by norm_num only
    have hc : (((581706823 / 500000000000 : ℚ) +
        (9049541287 / 1000000000000000000 : ℚ) / (2252314199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1225416267 / 1000000000000 : ℚ) + (1465377161 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((743724531 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12903]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12903 :
    2 * 160 < 12903 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999453 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12903 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12904 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12904. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12904 : WorldParameters where
  hiddenCharge := (290843077 / 250000000000 : ℝ)
  frame := (622848105709 / 1000000000000 : ℝ)
  moment := (4523854841 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12904 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468125868117 / 1000000000000 : ℝ)
    root := (41802499 / 5000000000 : ℝ) }

noncomputable def scalar12904 : ScalarCertificate 12904 world12904 agent12904 where
  dimensionLo := 12904
  dimensionHi := 12904
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2252674899 / 1000000000000 : ℝ)
  frameLo := (622848105709 / 1000000000000 : ℝ)
  frameHi := (1468125868117 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12904]
  agentFrame_pos := by norm_num only [agent12904]
  worldRadius := (2252674899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12904]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (306100753 / 250000000000 : ℝ)
  lowerTail := (183031519 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7434133537 / 1000000000000 : ℝ)
  ledger := by
    have h : (290843077 / 250000000000 : ℚ) +
        (4523854841 / 500000000000000000 : ℚ) / (2252674899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (306100753 / 250000000000 : ℚ) + (183031519 / 125000000000 : ℚ) ≤
        (7434133537 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((290843077 / 250000000000 : ℚ) +
        (4523854841 / 500000000000000000 : ℚ) / (2252674899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (306100753 / 250000000000 : ℚ) + (183031519 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7434133537 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12904]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12904 :
    2 * 160 < 12904 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999317 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12904 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12905 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12905. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12905 : WorldParameters where
  hiddenCharge := (1163330981 / 1000000000000 : ℝ)
  frame := (7785433813 / 12500000000 : ℝ)
  moment := (1809175719 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12905 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183511968277 / 125000000000 : ℝ)
    root := (261245559 / 31250000000 : ℝ) }

noncomputable def scalar12905 : ScalarCertificate 12905 world12905 agent12905 where
  dimensionLo := 12905
  dimensionHi := 12905
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2253035499 / 1000000000000 : ℝ)
  frameLo := (7785433813 / 12500000000 : ℝ)
  frameHi := (183511968277 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12905]
  agentFrame_pos := by norm_num only [agent12905]
  worldRadius := (2253035499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12905]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (611695307 / 500000000000 : ℝ)
  lowerTail := (1463128039 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7431024293 / 1000000000000 : ℝ)
  ledger := by
    have h : (1163330981 / 1000000000000 : ℚ) +
        (1809175719 / 200000000000000000 : ℚ) / (2253035499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (611695307 / 500000000000 : ℚ) + (1463128039 / 1000000000000 : ℚ) ≤
        (7431024293 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1163330981 / 1000000000000 : ℚ) +
        (1809175719 / 200000000000000000 : ℚ) / (2253035499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (611695307 / 500000000000 : ℚ) + (1463128039 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7431024293 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12905]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12905 :
    2 * 160 < 12905 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999719 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12905 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12906 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12906. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12906 : WorldParameters where
  hiddenCharge := (18176401 / 15625000000 : ℝ)
  frame := (7785266331 / 12500000000 : ℝ)
  moment := (4522024013 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12906 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734032818461 / 500000000000 : ℝ)
    root := (8359216227 / 1000000000000 : ℝ) }

noncomputable def scalar12906 : ScalarCertificate 12906 world12906 agent12906 where
  dimensionLo := 12906
  dimensionHi := 12906
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2253396199 / 1000000000000 : ℝ)
  frameLo := (7785266331 / 12500000000 : ℝ)
  frameHi := (734032818461 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12906]
  agentFrame_pos := by norm_num only [agent12906]
  worldRadius := (2253396199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12906]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (611189647 / 500000000000 : ℝ)
  lowerTail := (22843829 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7427917717 / 1000000000000 : ℝ)
  ledger := by
    have h : (18176401 / 15625000000 : ℚ) +
        (4522024013 / 500000000000000000 : ℚ) / (2253396199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (611189647 / 500000000000 : ℚ) + (22843829 / 15625000000 : ℚ) ≤
        (7427917717 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((18176401 / 15625000000 : ℚ) +
        (4522024013 / 500000000000000000 : ℚ) / (2253396199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (611189647 / 500000000000 : ℚ) + (22843829 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((7427917717 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12906]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12906 :
    2 * 160 < 12906 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999991 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12906 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12907 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12907. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12907 : WorldParameters where
  hiddenCharge := (581624179 / 500000000000 : ℝ)
  frame := (622807910027 / 1000000000000 : ℝ)
  moment := (361688719 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12907 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183504443263 / 125000000000 : ℝ)
    root := (261205459 / 31250000000 : ℝ) }

noncomputable def scalar12907 : ScalarCertificate 12907 world12907 agent12907 where
  dimensionLo := 12907
  dimensionHi := 12907
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2253756899 / 1000000000000 : ℝ)
  frameLo := (622807910027 / 1000000000000 : ℝ)
  frameHi := (183504443263 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12907]
  agentFrame_pos := by norm_num only [agent12907]
  worldRadius := (2253756899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12907]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (152671113 / 125000000000 : ℝ)
  lowerTail := (1460883049 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (232025427 / 31250000000 : ℝ)
  ledger := by
    have h : (581624179 / 500000000000 : ℚ) +
        (361688719 / 40000000000000000 : ℚ) / (2253756899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (152671113 / 125000000000 : ℚ) + (1460883049 / 1000000000000 : ℚ) ≤
        (232025427 / 31250000000 : ℚ) := by norm_num only
    have hc : (((581624179 / 500000000000 : ℚ) +
        (361688719 / 40000000000000000 : ℚ) / (2253756899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (152671113 / 125000000000 : ℚ) + (1460883049 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((232025427 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12907]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12907 :
    2 * 160 < 12907 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999771 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12907 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12908 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12908. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12908 : WorldParameters where
  hiddenCharge := (1163207063 / 1000000000000 : ℝ)
  frame := (622794515683 / 1000000000000 : ℝ)
  moment := (226009711 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12908 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293601094751 / 200000000000 : ℝ)
    root := (8357933399 / 1000000000000 : ℝ) }

noncomputable def scalar12908 : ScalarCertificate 12908 world12908 agent12908 where
  dimensionLo := 12908
  dimensionHi := 12908
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2254117499 / 1000000000000 : ℝ)
  frameLo := (622794515683 / 1000000000000 : ℝ)
  frameHi := (293601094751 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12908]
  agentFrame_pos := by norm_num only [agent12908]
  worldRadius := (2254117499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12908]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (610179731 / 500000000000 : ℝ)
  lowerTail := (91235127 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (296868493 / 40000000000 : ℝ)
  ledger := by
    have h : (1163207063 / 1000000000000 : ℚ) +
        (226009711 / 25000000000000000 : ℚ) / (2254117499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (610179731 / 500000000000 : ℚ) + (91235127 / 62500000000 : ℚ) ≤
        (296868493 / 40000000000 : ℚ) := by norm_num only
    have hc : (((1163207063 / 1000000000000 : ℚ) +
        (226009711 / 25000000000000000 : ℚ) / (2254117499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (610179731 / 500000000000 : ℚ) + (91235127 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((296868493 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12908]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12908 :
    2 * 160 < 12908 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996751 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12908 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12909 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12909. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12909 : WorldParameters where
  hiddenCharge := (1163165779 / 1000000000000 : ℝ)
  frame := (124556224689 / 200000000000 : ℝ)
  moment := (141227491 / 15625000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12909 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146797541399 / 100000000000 : ℝ)
    root := (8357292297 / 1000000000000 : ℝ) }

noncomputable def scalar12909 : ScalarCertificate 12909 world12909 agent12909 where
  dimensionLo := 12909
  dimensionHi := 12909
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2254478199 / 1000000000000 : ℝ)
  frameLo := (124556224689 / 200000000000 : ℝ)
  frameHi := (146797541399 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12909]
  agentFrame_pos := by norm_num only [agent12909]
  worldRadius := (2254478199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12909]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1219351049 / 1000000000000 : ℝ)
  lowerTail := (1458642093 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (148372271 / 20000000000 : ℝ)
  ledger := by
    have h : (1163165779 / 1000000000000 : ℚ) +
        (141227491 / 15625000000000000 : ℚ) / (2254478199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1219351049 / 1000000000000 : ℚ) + (1458642093 / 1000000000000 : ℚ) ≤
        (148372271 / 20000000000 : ℚ) := by norm_num only
    have hc : (((1163165779 / 1000000000000 : ℚ) +
        (141227491 / 15625000000000000 : ℚ) / (2254478199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1219351049 / 1000000000000 : ℚ) + (1458642093 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((148372271 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12909]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12909 :
    2 * 160 < 12909 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999117 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12909 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12910 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12910. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12910 : WorldParameters where
  hiddenCharge := (581562253 / 500000000000 : ℝ)
  frame := (311383866657 / 500000000000 : ℝ)
  moment := (2259182731 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12910 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146786638633 / 100000000000 : ℝ)
    root := (2089162829 / 250000000000 : ℝ) }

noncomputable def scalar12910 : ScalarCertificate 12910 world12910 agent12910 where
  dimensionLo := 12910
  dimensionHi := 12910
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2254953999 / 1000000000000 : ℝ)
  frameLo := (311383866657 / 500000000000 : ℝ)
  frameHi := (146786638633 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12910]
  agentFrame_pos := by norm_num only [agent12910]
  worldRadius := (2254953999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12910]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1218126737 / 1000000000000 : ℝ)
  lowerTail := (7286201 / 5000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3707418049 / 500000000000 : ℝ)
  ledger := by
    have h : (581562253 / 500000000000 : ℚ) +
        (2259182731 / 250000000000000000 : ℚ) / (2254953999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1218126737 / 1000000000000 : ℚ) + (7286201 / 5000000000 : ℚ) ≤
        (3707418049 / 500000000000 : ℚ) := by norm_num only
    have hc : (((581562253 / 500000000000 : ℚ) +
        (2259182731 / 250000000000000000 : ℚ) / (2254953999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1218126737 / 1000000000000 : ℚ) + (7286201 / 5000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3707418049 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12910]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12910 :
    2 * 160 < 12910 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999863 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12910 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12911 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12911. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12911 : WorldParameters where
  hiddenCharge := (1163083243 / 1000000000000 : ℝ)
  frame := (622754345289 / 1000000000000 : ℝ)
  moment := (9034902941 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12911 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733918179243 / 500000000000 : ℝ)
    root := (1671202117 / 200000000000 : ℝ) }

noncomputable def scalar12911 : ScalarCertificate 12911 world12911 agent12911 where
  dimensionLo := 12911
  dimensionHi := 12911
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2255314799 / 1000000000000 : ℝ)
  frameLo := (622754345289 / 1000000000000 : ℝ)
  frameHi := (733918179243 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12911]
  agentFrame_pos := by norm_num only [agent12911]
  worldRadius := (2255314799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12911]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1217120471 / 1000000000000 : ℝ)
  lowerTail := (728061269 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3705871473 / 500000000000 : ℝ)
  ledger := by
    have h : (1163083243 / 1000000000000 : ℚ) +
        (9034902941 / 1000000000000000000 : ℚ) / (2255314799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1217120471 / 1000000000000 : ℚ) + (728061269 / 500000000000 : ℚ) ≤
        (3705871473 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1163083243 / 1000000000000 : ℚ) +
        (9034902941 / 1000000000000000000 : ℚ) / (2255314799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1217120471 / 1000000000000 : ℚ) + (728061269 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3705871473 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12911]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12911 :
    2 * 160 < 12911 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999599 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12911 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12912 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12912. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12912 : WorldParameters where
  hiddenCharge := (1163041991 / 1000000000000 : ℝ)
  frame := (62274095937 / 100000000000 : ℝ)
  moment := (4516537737 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12912 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467806349079 / 1000000000000 : ℝ)
    root := (334214799 / 40000000000 : ℝ) }

noncomputable def scalar12912 : ScalarCertificate 12912 world12912 agent12912 where
  dimensionLo := 12912
  dimensionHi := 12912
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2255675499 / 1000000000000 : ℝ)
  frameLo := (62274095937 / 100000000000 : ℝ)
  frameHi := (1467806349079 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12912]
  agentFrame_pos := by norm_num only [agent12912]
  worldRadius := (2255675499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12912]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (243223011 / 200000000000 : ℝ)
  lowerTail := (291001153 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (463040769 / 62500000000 : ℝ)
  ledger := by
    have h : (1163041991 / 1000000000000 : ℚ) +
        (4516537737 / 500000000000000000 : ℚ) / (2255675499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (243223011 / 200000000000 : ℚ) + (291001153 / 200000000000 : ℚ) ≤
        (463040769 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1163041991 / 1000000000000 : ℚ) +
        (4516537737 / 500000000000000000 : ℚ) / (2255675499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (243223011 / 200000000000 : ℚ) + (291001153 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((463040769 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12912]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12912 :
    2 * 160 < 12912 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997461 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12912 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12913 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12913. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12913 : WorldParameters where
  hiddenCharge := (1163000749 / 1000000000000 : ℝ)
  frame := (155681893889 / 250000000000 : ℝ)
  moment := (361249941 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12913 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467776346349 / 1000000000000 : ℝ)
    root := (1670945923 / 200000000000 : ℝ) }

noncomputable def scalar12913 : ScalarCertificate 12913 world12913 agent12913 where
  dimensionLo := 12913
  dimensionHi := 12913
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2256036299 / 1000000000000 : ℝ)
  frameLo := (155681893889 / 250000000000 : ℝ)
  frameHi := (1467776346349 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12913]
  agentFrame_pos := by norm_num only [agent12913]
  worldRadius := (2256036299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12913]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (607555343 / 500000000000 : ℝ)
  lowerTail := (290778017 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (370278213 / 50000000000 : ℝ)
  ledger := by
    have h : (1163000749 / 1000000000000 : ℚ) +
        (361249941 / 40000000000000000 : ℚ) / (2256036299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (607555343 / 500000000000 : ℚ) + (290778017 / 200000000000 : ℚ) ≤
        (370278213 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1163000749 / 1000000000000 : ℚ) +
        (361249941 / 40000000000000000 : ℚ) / (2256036299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (607555343 / 500000000000 : ℚ) + (290778017 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((370278213 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12913]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12913 :
    2 * 160 < 12913 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999939 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12913 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12914 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12914. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12914 : WorldParameters where
  hiddenCharge := (1162959519 / 1000000000000 : ℝ)
  frame := (124542838769 / 200000000000 : ℝ)
  moment := (9029422091 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12914 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467746367919 / 1000000000000 : ℝ)
    root := (8354089377 / 1000000000000 : ℝ) }

noncomputable def scalar12914 : ScalarCertificate 12914 world12914 agent12914 where
  dimensionLo := 12914
  dimensionHi := 12914
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2256396999 / 1000000000000 : ℝ)
  frameLo := (124542838769 / 200000000000 : ℝ)
  frameHi := (1467746367919 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12914]
  agentFrame_pos := by norm_num only [agent12914]
  worldRadius := (2256396999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12914]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (303526797 / 250000000000 : ℝ)
  lowerTail := (36319383 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7402478773 / 1000000000000 : ℝ)
  ledger := by
    have h : (1162959519 / 1000000000000 : ℚ) +
        (9029422091 / 1000000000000000000 : ℚ) / (2256396999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (303526797 / 250000000000 : ℚ) + (36319383 / 25000000000 : ℚ) ≤
        (7402478773 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1162959519 / 1000000000000 : ℚ) +
        (9029422091 / 1000000000000000000 : ℚ) / (2256396999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (303526797 / 250000000000 : ℚ) + (36319383 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7402478773 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12914]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12914 :
    2 * 160 < 12914 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997967 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12914 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12915 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12915. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12915 : WorldParameters where
  hiddenCharge := (1162918299 / 1000000000000 : ℝ)
  frame := (622700814239 / 1000000000000 : ℝ)
  moment := (4513798087 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12915 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467716402027 / 1000000000000 : ℝ)
    root := (8353449387 / 1000000000000 : ℝ) }

noncomputable def scalar12915 : ScalarCertificate 12915 world12915 agent12915 where
  dimensionLo := 12915
  dimensionHi := 12915
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2256757699 / 1000000000000 : ℝ)
  frameLo := (622700814239 / 1000000000000 : ℝ)
  frameHi := (1467716402027 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12915]
  agentFrame_pos := by norm_num only [agent12915]
  worldRadius := (2256757699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12915]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1213104683 / 1000000000000 : ℝ)
  lowerTail := (181457699 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7399395929 / 1000000000000 : ℝ)
  ledger := by
    have h : (1162918299 / 1000000000000 : ℚ) +
        (4513798087 / 500000000000000000 : ℚ) / (2256757699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1213104683 / 1000000000000 : ℚ) + (181457699 / 125000000000 : ℚ) ≤
        (7399395929 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1162918299 / 1000000000000 : ℚ) +
        (4513798087 / 500000000000000000 : ℚ) / (2256757699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1213104683 / 1000000000000 : ℚ) + (181457699 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7399395929 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12915]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12915 :
    2 * 160 < 12915 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994733 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12915 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12916 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12916. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12916 : WorldParameters where
  hiddenCharge := (116287709 / 100000000000 : ℝ)
  frame := (622687436737 / 1000000000000 : ℝ)
  moment := (2256442693 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12916 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467686448667 / 1000000000000 : ℝ)
    root := (8352809519 / 1000000000000 : ℝ) }

noncomputable def scalar12916 : ScalarCertificate 12916 world12916 agent12916 where
  dimensionLo := 12916
  dimensionHi := 12916
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2257118499 / 1000000000000 : ℝ)
  frameLo := (622687436737 / 1000000000000 : ℝ)
  frameHi := (1467686448667 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12916]
  agentFrame_pos := by norm_num only [agent12916]
  worldRadius := (2257118499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12916]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (24242063 / 20000000000 : ℝ)
  lowerTail := (290109777 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1479263107 / 200000000000 : ℝ)
  ledger := by
    have h : (116287709 / 100000000000 : ℚ) +
        (2256442693 / 250000000000000000 : ℚ) / (2257118499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (24242063 / 20000000000 : ℚ) + (290109777 / 200000000000 : ℚ) ≤
        (1479263107 / 200000000000 : ℚ) := by norm_num only
    have hc : (((116287709 / 100000000000 : ℚ) +
        (2256442693 / 250000000000000000 : ℚ) / (2257118499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (24242063 / 20000000000 : ℚ) + (290109777 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1479263107 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12916]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12916 :
    2 * 160 < 12916 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999227 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12916 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12917 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12917. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12917 : WorldParameters where
  hiddenCharge := (1162835891 / 1000000000000 : ℝ)
  frame := (622674061337 / 1000000000000 : ℝ)
  moment := (9023945887 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12917 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733828256853 / 500000000000 : ℝ)
    root := (8352169901 / 1000000000000 : ℝ) }

noncomputable def scalar12917 : ScalarCertificate 12917 world12917 agent12917 where
  dimensionLo := 12917
  dimensionHi := 12917
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2257479199 / 1000000000000 : ℝ)
  frameLo := (622674061337 / 1000000000000 : ℝ)
  frameHi := (733828256853 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12917]
  agentFrame_pos := by norm_num only [agent12917]
  worldRadius := (2257479199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12917]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1211102557 / 1000000000000 : ℝ)
  lowerTail := (1449437159 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7393237831 / 1000000000000 : ℝ)
  ledger := by
    have h : (1162835891 / 1000000000000 : ℚ) +
        (9023945887 / 1000000000000000000 : ℚ) / (2257479199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1211102557 / 1000000000000 : ℚ) + (1449437159 / 1000000000000 : ℚ) ≤
        (7393237831 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1162835891 / 1000000000000 : ℚ) +
        (9023945887 / 1000000000000000000 : ℚ) / (2257479199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1211102557 / 1000000000000 : ℚ) + (1449437159 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7393237831 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12917]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12917 :
    2 * 160 < 12917 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994467 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12917 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12918 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12918. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12918 : WorldParameters where
  hiddenCharge := (72674669 / 62500000000 : ℝ)
  frame := (622660688039 / 1000000000000 : ℝ)
  moment := (9022121517 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12918 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467626591263 / 1000000000000 : ℝ)
    root := (8351530403 / 1000000000000 : ℝ) }

noncomputable def scalar12918 : ScalarCertificate 12918 world12918 agent12918 where
  dimensionLo := 12918
  dimensionHi := 12918
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2257839999 / 1000000000000 : ℝ)
  frameLo := (622660688039 / 1000000000000 : ℝ)
  frameHi := (1467626591263 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12918]
  agentFrame_pos := by norm_num only [agent12918]
  worldRadius := (2257839999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12918]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (605051467 / 500000000000 : ℝ)
  lowerTail := (1448326453 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7390162571 / 1000000000000 : ℝ)
  ledger := by
    have h : (72674669 / 62500000000 : ℚ) +
        (9022121517 / 1000000000000000000 : ℚ) / (2257839999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (605051467 / 500000000000 : ℚ) + (1448326453 / 1000000000000 : ℚ) ≤
        (7390162571 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((72674669 / 62500000000 : ℚ) +
        (9022121517 / 1000000000000000000 : ℚ) / (2257839999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (605051467 / 500000000000 : ℚ) + (1448326453 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7390162571 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12918]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12918 :
    2 * 160 < 12918 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995363 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12918 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12919 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12919. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12919 : WorldParameters where
  hiddenCharge := (1162753527 / 1000000000000 : ℝ)
  frame := (622647316843 / 1000000000000 : ℝ)
  moment := (4510148831 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12919 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467596681329 / 1000000000000 : ℝ)
    root := (4175445577 / 500000000000 : ℝ) }

noncomputable def scalar12919 : ScalarCertificate 12919 world12919 agent12919 where
  dimensionLo := 12919
  dimensionHi := 12919
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2258200799 / 1000000000000 : ℝ)
  frameLo := (622647316843 / 1000000000000 : ℝ)
  frameHi := (1467596681329 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12919]
  agentFrame_pos := by norm_num only [agent12919]
  worldRadius := (2258200799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12919]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (12091043 / 10000000000 : ℝ)
  lowerTail := (1447216779 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1477417989 / 200000000000 : ℝ)
  ledger := by
    have h : (1162753527 / 1000000000000 : ℚ) +
        (4510148831 / 500000000000000000 : ℚ) / (2258200799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (12091043 / 10000000000 : ℚ) + (1447216779 / 1000000000000 : ℚ) ≤
        (1477417989 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1162753527 / 1000000000000 : ℚ) +
        (4510148831 / 500000000000000000 : ℚ) / (2258200799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (12091043 / 10000000000 : ℚ) + (1447216779 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1477417989 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12919]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12919 :
    2 * 160 < 12919 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998807 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12919 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12920 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12920. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12920 : WorldParameters where
  hiddenCharge := (29067809 / 25000000000 : ℝ)
  frame := (622633947749 / 1000000000000 : ℝ)
  moment := (4509237161 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12920 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467487921297 / 1000000000000 : ℝ)
    root := (334010081 / 40000000000 : ℝ) }

noncomputable def scalar12920 : ScalarCertificate 12920 world12920 agent12920 where
  dimensionLo := 12920
  dimensionHi := 12920
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2258676799 / 1000000000000 : ℝ)
  frameLo := (622633947749 / 1000000000000 : ℝ)
  frameHi := (1467487921297 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12920]
  agentFrame_pos := by norm_num only [agent12920]
  worldRadius := (2258676799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12920]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1207891749 / 1000000000000 : ℝ)
  lowerTail := (1445827561 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7383344131 / 1000000000000 : ℝ)
  ledger := by
    have h : (29067809 / 25000000000 : ℚ) +
        (4509237161 / 500000000000000000 : ℚ) / (2258676799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1207891749 / 1000000000000 : ℚ) + (1445827561 / 1000000000000 : ℚ) ≤
        (7383344131 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((29067809 / 25000000000 : ℚ) +
        (4509237161 / 500000000000000000 : ℚ) / (2258676799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1207891749 / 1000000000000 : ℚ) + (1445827561 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7383344131 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12920]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12920 :
    2 * 160 < 12920 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (124999989 / 12500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12920 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12921 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12921. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12921 : WorldParameters where
  hiddenCharge := (232534241 / 200000000000 : ℝ)
  frame := (124524116151 / 200000000000 : ℝ)
  moment := (4508325749 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12921 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733729024501 / 500000000000 : ℝ)
    root := (1669922629 / 200000000000 : ℝ) }

noncomputable def scalar12921 : ScalarCertificate 12921 world12921 agent12921 where
  dimensionLo := 12921
  dimensionHi := 12921
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2259037599 / 1000000000000 : ℝ)
  frameLo := (124524116151 / 200000000000 : ℝ)
  frameHi := (733729024501 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12921]
  agentFrame_pos := by norm_num only [agent12921]
  worldRadius := (2259037599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12921]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1206895187 / 1000000000000 : ℝ)
  lowerTail := (1444720087 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3690138561 / 500000000000 : ℝ)
  ledger := by
    have h : (232534241 / 200000000000 : ℚ) +
        (4508325749 / 500000000000000000 : ℚ) / (2259037599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1206895187 / 1000000000000 : ℚ) + (1444720087 / 1000000000000 : ℚ) ≤
        (3690138561 / 500000000000 : ℚ) := by norm_num only
    have hc : (((232534241 / 200000000000 : ℚ) +
        (4508325749 / 500000000000000000 : ℚ) / (2259037599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1206895187 / 1000000000000 : ℚ) + (1444720087 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3690138561 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12921]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12921 :
    2 * 160 < 12921 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (249999907 / 25000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12921 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12922 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12922. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12922 : WorldParameters where
  hiddenCharge := (58131503 / 50000000000 : ℝ)
  frame := (622607215861 / 1000000000000 : ℝ)
  moment := (2253707297 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12922 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733714094597 / 500000000000 : ℝ)
    root := (4174487193 / 500000000000 : ℝ) }

noncomputable def scalar12922 : ScalarCertificate 12922 world12922 agent12922 where
  dimensionLo := 12922
  dimensionHi := 12922
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2259398399 / 1000000000000 : ℝ)
  frameLo := (622607215861 / 1000000000000 : ℝ)
  frameHi := (733714094597 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12922]
  agentFrame_pos := by norm_num only [agent12922]
  worldRadius := (2259398399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12922]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (602949759 / 500000000000 : ℝ)
  lowerTail := (288722709 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7377212547 / 1000000000000 : ℝ)
  ledger := by
    have h : (58131503 / 50000000000 : ℚ) +
        (2253707297 / 250000000000000000 : ℚ) / (2259398399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (602949759 / 500000000000 : ℚ) + (288722709 / 200000000000 : ℚ) ≤
        (7377212547 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((58131503 / 50000000000 : ℚ) +
        (2253707297 / 250000000000000000 : ℚ) / (2259398399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (602949759 / 500000000000 : ℚ) + (288722709 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7377212547 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12922]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12922 :
    2 * 160 < 12922 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999491 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12922 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12923 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12923. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12923 : WorldParameters where
  hiddenCharge := (581294463 / 500000000000 : ℝ)
  frame := (622593853067 / 1000000000000 : ℝ)
  moment := (9013007393 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12923 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467398341867 / 1000000000000 : ℝ)
    root := (66786687 / 8000000000 : ℝ) }

noncomputable def scalar12923 : ScalarCertificate 12923 world12923 agent12923 where
  dimensionLo := 12923
  dimensionHi := 12923
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2259759199 / 1000000000000 : ℝ)
  frameLo := (622593853067 / 1000000000000 : ℝ)
  frameHi := (1467398341867 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12923]
  agentFrame_pos := by norm_num only [agent12923]
  worldRadius := (2259759199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12923]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1204904833 / 1000000000000 : ℝ)
  lowerTail := (5634797 / 3906250000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1474830119 / 200000000000 : ℝ)
  ledger := by
    have h : (581294463 / 500000000000 : ℚ) +
        (9013007393 / 1000000000000000000 : ℚ) / (2259759199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1204904833 / 1000000000000 : ℚ) + (5634797 / 3906250000 : ℚ) ≤
        (1474830119 / 200000000000 : ℚ) := by norm_num only
    have hc : (((581294463 / 500000000000 : ℚ) +
        (9013007393 / 1000000000000000000 : ℚ) / (2259759199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1204904833 / 1000000000000 : ℚ) + (5634797 / 3906250000 : ℚ) : ℚ) : ℝ) ≤
        ((1474830119 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12923]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12923 :
    2 * 160 < 12923 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (312499939 / 31250000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12923 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12924 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12924. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12924 : WorldParameters where
  hiddenCharge := (581273901 / 500000000000 : ℝ)
  frame := (622580492373 / 1000000000000 : ℝ)
  moment := (140799783 / 15625000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12924 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733684256443 / 500000000000 : ℝ)
    root := (1669539497 / 200000000000 : ℝ) }

noncomputable def scalar12924 : ScalarCertificate 12924 world12924 agent12924 where
  dimensionLo := 12924
  dimensionHi := 12924
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2260120099 / 1000000000000 : ℝ)
  frameLo := (622580492373 / 1000000000000 : ℝ)
  frameHi := (733684256443 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12924]
  agentFrame_pos := by norm_num only [agent12924]
  worldRadius := (2260120099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12924]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (601955567 / 500000000000 : ℝ)
  lowerTail := (1441403559 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7371091123 / 1000000000000 : ℝ)
  ledger := by
    have h : (581273901 / 500000000000 : ℚ) +
        (140799783 / 15625000000000000 : ℚ) / (2260120099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (601955567 / 500000000000 : ℚ) + (1441403559 / 1000000000000 : ℚ) ≤
        (7371091123 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((581273901 / 500000000000 : ℚ) +
        (140799783 / 15625000000000000 : ℚ) / (2260120099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (601955567 / 500000000000 : ℚ) + (1441403559 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7371091123 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12924]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12924 :
    2 * 160 < 12924 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998477 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12924 {← IO.monoMsNow}" : IO Unit)
