import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13025 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13025. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13025 : WorldParameters where
  hiddenCharge := (579224387 / 500000000000 : ℝ)
  frame := (310620891347 / 500000000000 : ℝ)
  moment := (2207463507 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13025 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146360414081 / 100000000000 : ℝ)
    root := (8284150571 / 1000000000000 : ℝ) }

noncomputable def scalar13025 : ScalarCertificate 13025 world13025 agent13025 where
  dimensionLo := 13025
  dimensionHi := 13025
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2297836499 / 1000000000000 : ℝ)
  frameLo := (310620891347 / 500000000000 : ℝ)
  frameHi := (146360414081 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13025]
  agentFrame_pos := by norm_num only [agent13025]
  worldRadius := (2297836499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13025]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (553091441 / 500000000000 : ℝ)
  lowerTail := (1332066489 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7068148327 / 1000000000000 : ℝ)
  ledger := by
    have h : (579224387 / 500000000000 : ℚ) +
        (2207463507 / 250000000000000000 : ℚ) / (2297836499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (553091441 / 500000000000 : ℚ) + (1332066489 / 1000000000000 : ℚ) ≤
        (7068148327 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((579224387 / 500000000000 : ℚ) +
        (2207463507 / 250000000000000000 : ℚ) / (2297836499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (553091441 / 500000000000 : ℚ) + (1332066489 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7068148327 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13025]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13025 :
    2 * 160 < 13025 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999787 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13025 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13026 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13026. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13026 : WorldParameters where
  hiddenCharge := (579204361 / 500000000000 : ℝ)
  frame := (621228633381 / 1000000000000 : ℝ)
  moment := (1765616851 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13026 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731787451091 / 500000000000 : ℝ)
    root := (4141765199 / 500000000000 : ℝ) }

noncomputable def scalar13026 : ScalarCertificate 13026 world13026 agent13026 where
  dimensionLo := 13026
  dimensionHi := 13026
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2298199499 / 1000000000000 : ℝ)
  frameLo := (621228633381 / 1000000000000 : ℝ)
  frameHi := (731787451091 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13026]
  agentFrame_pos := by norm_num only [agent13026]
  worldRadius := (2298199499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13026]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (138160013 / 125000000000 : ℝ)
  lowerTail := (665528583 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7065332859 / 1000000000000 : ℝ)
  ledger := by
    have h : (579204361 / 500000000000 : ℚ) +
        (1765616851 / 200000000000000000 : ℚ) / (2298199499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (138160013 / 125000000000 : ℚ) + (665528583 / 500000000000 : ℚ) ≤
        (7065332859 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((579204361 / 500000000000 : ℚ) +
        (1765616851 / 200000000000000000 : ℚ) / (2298199499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (138160013 / 125000000000 : ℚ) + (665528583 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7065332859 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13026]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13026 :
    2 * 160 < 13026 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999007 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13026 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13027 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13027. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13027 : WorldParameters where
  hiddenCharge := (1158368681 / 1000000000000 : ℝ)
  frame := (621215486113 / 1000000000000 : ℝ)
  moment := (4413157489 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13027 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731772837687 / 500000000000 : ℝ)
    root := (1656582067 / 200000000000 : ℝ) }

noncomputable def scalar13027 : ScalarCertificate 13027 world13027 agent13027 where
  dimensionLo := 13027
  dimensionHi := 13027
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2298562699 / 1000000000000 : ℝ)
  frameLo := (621215486113 / 1000000000000 : ℝ)
  frameHi := (731772837687 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13027]
  agentFrame_pos := by norm_num only [agent13027]
  worldRadius := (2298562699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13027]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (55218913 / 50000000000 : ℝ)
  lowerTail := (665024417 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3531259797 / 500000000000 : ℝ)
  ledger := by
    have h : (1158368681 / 1000000000000 : ℚ) +
        (4413157489 / 500000000000000000 : ℚ) / (2298562699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (55218913 / 50000000000 : ℚ) + (665024417 / 500000000000 : ℚ) ≤
        (3531259797 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1158368681 / 1000000000000 : ℚ) +
        (4413157489 / 500000000000000000 : ℚ) / (2298562699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (55218913 / 50000000000 : ℚ) + (665024417 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3531259797 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13027]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13027 :
    2 * 160 < 13027 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999981 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13027 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13028 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13028. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13028 : WorldParameters where
  hiddenCharge := (23166573 / 20000000000 : ℝ)
  frame := (621202340891 / 1000000000000 : ℝ)
  moment := (2206136549 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13028 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146351646623 / 100000000000 : ℝ)
    root := (2070572627 / 250000000000 : ℝ) }

noncomputable def scalar13028 : ScalarCertificate 13028 world13028 agent13028 where
  dimensionLo := 13028
  dimensionHi := 13028
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2298925699 / 1000000000000 : ℝ)
  frameLo := (621202340891 / 1000000000000 : ℝ)
  frameHi := (146351646623 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13028]
  agentFrame_pos := by norm_num only [agent13028]
  worldRadius := (2298925699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13028]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1103477179 / 1000000000000 : ℝ)
  lowerTail := (13290413 / 10000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3529854373 / 500000000000 : ℝ)
  ledger := by
    have h : (23166573 / 20000000000 : ℚ) +
        (2206136549 / 250000000000000000 : ℚ) / (2298925699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1103477179 / 1000000000000 : ℚ) + (13290413 / 10000000000 : ℚ) ≤
        (3529854373 / 500000000000 : ℚ) := by norm_num only
    have hc : (((23166573 / 20000000000 : ℚ) +
        (2206136549 / 250000000000000000 : ℚ) / (2298925699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1103477179 / 1000000000000 : ℚ) + (13290413 / 10000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3529854373 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13028]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13028 :
    2 * 160 < 13028 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (49999997 / 5000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13028 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13029 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13029. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13029 : WorldParameters where
  hiddenCharge := (1158288629 / 1000000000000 : ℝ)
  frame := (310594598857 / 500000000000 : ℝ)
  moment := (8822777909 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13029 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463487274743 / 1000000000000 : ℝ)
    root := (8281670853 / 1000000000000 : ℝ) }

noncomputable def scalar13029 : ScalarCertificate 13029 world13029 agent13029 where
  dimensionLo := 13029
  dimensionHi := 13029
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2299288999 / 1000000000000 : ℝ)
  frameLo := (310594598857 / 500000000000 : ℝ)
  frameHi := (1463487274743 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13029]
  agentFrame_pos := by norm_num only [agent13029]
  worldRadius := (2299288999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13029]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1102577163 / 1000000000000 : ℝ)
  lowerTail := (1328034901 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7056900227 / 1000000000000 : ℝ)
  ledger := by
    have h : (1158288629 / 1000000000000 : ℚ) +
        (8822777909 / 1000000000000000000 : ℚ) / (2299288999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1102577163 / 1000000000000 : ℚ) + (1328034901 / 1000000000000 : ℚ) ≤
        (7056900227 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1158288629 / 1000000000000 : ℚ) +
        (8822777909 / 1000000000000000000 : ℚ) / (2299288999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1102577163 / 1000000000000 : ℚ) + (1328034901 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7056900227 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13029]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13029 :
    2 * 160 < 13029 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998123 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13029 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13030 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13030. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13030 : WorldParameters where
  hiddenCharge := (1158248619 / 1000000000000 : ℝ)
  frame := (621176056581 / 1000000000000 : ℝ)
  moment := (4410505059 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13030 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463380442299 / 1000000000000 : ℝ)
    root := (2070262843 / 250000000000 : ℝ) }

noncomputable def scalar13030 : ScalarCertificate 13030 world13030 agent13030 where
  dimensionLo := 13030
  dimensionHi := 13030
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2299768699 / 1000000000000 : ℝ)
  frameLo := (621176056581 / 1000000000000 : ℝ)
  frameHi := (1463380442299 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13030]
  agentFrame_pos := by norm_num only [agent13030]
  worldRadius := (2299768699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13030]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (550741831 / 500000000000 : ℝ)
  lowerTail := (1326773887 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1763368833 / 250000000000 : ℝ)
  ledger := by
    have h : (1158248619 / 1000000000000 : ℚ) +
        (4410505059 / 500000000000000000 : ℚ) / (2299768699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (550741831 / 500000000000 : ℚ) + (1326773887 / 1000000000000 : ℚ) ≤
        (1763368833 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1158248619 / 1000000000000 : ℚ) +
        (4410505059 / 500000000000000000 : ℚ) / (2299768699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (550741831 / 500000000000 : ℚ) + (1326773887 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1763368833 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13030]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13030 :
    2 * 160 < 13030 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996131 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13030 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13031 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13031. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13031 : WorldParameters where
  hiddenCharge := (1158208619 / 1000000000000 : ℝ)
  frame := (155290729373 / 250000000000 : ℝ)
  moment := (4409621411 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13031 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731675637641 / 500000000000 : ℝ)
    root := (517527 / 62500000 : ℝ) }

noncomputable def scalar13031 : ScalarCertificate 13031 world13031 agent13031 where
  dimensionLo := 13031
  dimensionHi := 13031
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2300131799 / 1000000000000 : ℝ)
  frameLo := (155290729373 / 250000000000 : ℝ)
  frameHi := (731675637641 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13031]
  agentFrame_pos := by norm_num only [agent13031]
  worldRadius := (2300131799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13031]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (275146317 / 250000000000 : ℝ)
  lowerTail := (132576921 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7050671691 / 1000000000000 : ℝ)
  ledger := by
    have h : (1158208619 / 1000000000000 : ℚ) +
        (4409621411 / 500000000000000000 : ℚ) / (2300131799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (275146317 / 250000000000 : ℚ) + (132576921 / 100000000000 : ℚ) ≤
        (7050671691 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1158208619 / 1000000000000 : ℚ) +
        (4409621411 / 500000000000000000 : ℚ) / (2300131799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (275146317 / 250000000000 : ℚ) + (132576921 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7050671691 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13031]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13031 :
    2 * 160 < 13031 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999037 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13031 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13032 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13032. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13032 : WorldParameters where
  hiddenCharge := (1158168629 / 1000000000000 : ℝ)
  frame := (310574890223 / 500000000000 : ℝ)
  moment := (440873801 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13032 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463322125901 / 1000000000000 : ℝ)
    root := (32343019 / 3906250000 : ℝ) }

noncomputable def scalar13032 : ScalarCertificate 13032 world13032 agent13032 where
  dimensionLo := 13032
  dimensionHi := 13032
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2300494899 / 1000000000000 : ℝ)
  frameLo := (310574890223 / 500000000000 : ℝ)
  frameHi := (1463322125901 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13032]
  agentFrame_pos := by norm_num only [agent13032]
  worldRadius := (2300494899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13032]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (274921943 / 250000000000 : ℝ)
  lowerTail := (1324765479 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7047870459 / 1000000000000 : ℝ)
  ledger := by
    have h : (1158168629 / 1000000000000 : ℚ) +
        (440873801 / 50000000000000000 : ℚ) / (2300494899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (274921943 / 250000000000 : ℚ) + (1324765479 / 1000000000000 : ℚ) ≤
        (7047870459 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1158168629 / 1000000000000 : ℚ) +
        (440873801 / 50000000000000000 : ℚ) / (2300494899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (274921943 / 250000000000 : ℚ) + (1324765479 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7047870459 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13032]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13032 :
    2 * 160 < 13032 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999861 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13032 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13033 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13033. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13033 : WorldParameters where
  hiddenCharge := (23162573 / 20000000000 : ℝ)
  frame := (621136645443 / 1000000000000 : ℝ)
  moment := (8815709713 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13033 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29265859883 / 20000000000 : ℝ)
    root := (82791939 / 10000000000 : ℝ) }

noncomputable def scalar13033 : ScalarCertificate 13033 world13033 agent13033 where
  dimensionLo := 13033
  dimensionHi := 13033
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2300858199 / 1000000000000 : ℝ)
  frameLo := (621136645443 / 1000000000000 : ℝ)
  frameHi := (29265859883 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13033]
  agentFrame_pos := by norm_num only [agent13033]
  worldRadius := (2300858199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13033]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (549395633 / 500000000000 : ℝ)
  lowerTail := (330940701 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3522535773 / 500000000000 : ℝ)
  ledger := by
    have h : (23162573 / 20000000000 : ℚ) +
        (8815709713 / 1000000000000000000 : ℚ) / (2300858199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (549395633 / 500000000000 : ℚ) + (330940701 / 250000000000 : ℚ) ≤
        (3522535773 / 500000000000 : ℚ) := by norm_num only
    have hc : (((23162573 / 20000000000 : ℚ) +
        (8815709713 / 1000000000000000000 : ℚ) / (2300858199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (549395633 / 500000000000 : ℚ) + (330940701 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3522535773 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13033]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13033 :
    2 * 160 < 13033 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999807 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13033 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13034 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13034. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13034 : WorldParameters where
  hiddenCharge := (1158088681 / 1000000000000 : ℝ)
  frame := (621123512483 / 1000000000000 : ℝ)
  moment := (8813943901 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13034 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365815968543 / 250000000000 : ℝ)
    root := (2069643777 / 250000000000 : ℝ) }

noncomputable def scalar13034 : ScalarCertificate 13034 world13034 agent13034 where
  dimensionLo := 13034
  dimensionHi := 13034
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2301221299 / 1000000000000 : ℝ)
  frameLo := (621123512483 / 1000000000000 : ℝ)
  frameHi := (365815968543 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13034]
  agentFrame_pos := by norm_num only [agent13034]
  worldRadius := (2301221299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13034]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (34309233 / 31250000000 : ℝ)
  lowerTail := (1322760851 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1408454981 / 200000000000 : ℝ)
  ledger := by
    have h : (1158088681 / 1000000000000 : ℚ) +
        (8813943901 / 1000000000000000000 : ℚ) / (2301221299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (34309233 / 31250000000 : ℚ) + (1322760851 / 1000000000000 : ℚ) ≤
        (1408454981 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1158088681 / 1000000000000 : ℚ) +
        (8813943901 / 1000000000000000000 : ℚ) / (2301221299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (34309233 / 31250000000 : ℚ) + (1322760851 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1408454981 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13034]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13034 :
    2 * 160 < 13034 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997477 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13034 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13035 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13035. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13035 : WorldParameters where
  hiddenCharge := (579024361 / 500000000000 : ℝ)
  frame := (155277595391 / 250000000000 : ℝ)
  moment := (4406089291 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13035 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463234771811 / 1000000000000 : ℝ)
    root := (8277956427 / 1000000000000 : ℝ) }

noncomputable def scalar13035 : ScalarCertificate 13035 world13035 agent13035 where
  dimensionLo := 13035
  dimensionHi := 13035
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2301584399 / 1000000000000 : ℝ)
  frameLo := (155277595391 / 250000000000 : ℝ)
  frameHi := (1463234771811 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13035]
  agentFrame_pos := by norm_num only [agent13035]
  worldRadius := (2301584399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13035]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (219400091 / 200000000000 : ℝ)
  lowerTail := (330439939 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7039480493 / 1000000000000 : ℝ)
  ledger := by
    have h : (579024361 / 500000000000 : ℚ) +
        (4406089291 / 500000000000000000 : ℚ) / (2301584399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (219400091 / 200000000000 : ℚ) + (330439939 / 250000000000 : ℚ) ≤
        (7039480493 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((579024361 / 500000000000 : ℚ) +
        (4406089291 / 500000000000000000 : ℚ) / (2301584399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (219400091 / 200000000000 : ℚ) + (330439939 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7039480493 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13035]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13035 :
    2 * 160 < 13035 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995337 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13035 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13036 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13036. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13036 : WorldParameters where
  hiddenCharge := (579004387 / 500000000000 : ℝ)
  frame := (621097252687 / 1000000000000 : ℝ)
  moment := (4405206879 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13036 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463205681211 / 1000000000000 : ℝ)
    root := (413866899 / 50000000000 : ℝ) }

noncomputable def scalar13036 : ScalarCertificate 13036 world13036 agent13036 where
  dimensionLo := 13036
  dimensionHi := 13036
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2301947799 / 1000000000000 : ℝ)
  frameLo := (621097252687 / 1000000000000 : ℝ)
  frameHi := (1463205681211 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13036]
  agentFrame_pos := by norm_num only [agent13036]
  worldRadius := (2301947799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13036]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (274026633 / 250000000000 : ℝ)
  lowerTail := (660379903 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7036688433 / 1000000000000 : ℝ)
  ledger := by
    have h : (579004387 / 500000000000 : ℚ) +
        (4405206879 / 500000000000000000 : ℚ) / (2301947799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (274026633 / 250000000000 : ℚ) + (660379903 / 500000000000 : ℚ) ≤
        (7036688433 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((579004387 / 500000000000 : ℚ) +
        (4405206879 / 500000000000000000 : ℚ) / (2301947799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (274026633 / 250000000000 : ℚ) + (660379903 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7036688433 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13036]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13036 :
    2 * 160 < 13036 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999223 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13036 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13037 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13037. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13037 : WorldParameters where
  hiddenCharge := (231593767 / 200000000000 : ℝ)
  frame := (12421682517 / 20000000000 : ℝ)
  moment := (2202162357 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13037 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365794150591 / 250000000000 : ℝ)
    root := (1655343941 / 200000000000 : ℝ) }

noncomputable def scalar13037 : ScalarCertificate 13037 world13037 agent13037 where
  dimensionLo := 13037
  dimensionHi := 13037
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2302310899 / 1000000000000 : ℝ)
  frameLo := (12421682517 / 20000000000 : ℝ)
  frameHi := (365794150591 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13037]
  agentFrame_pos := by norm_num only [agent13037]
  worldRadius := (2302310899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13037]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (547606617 / 500000000000 : ℝ)
  lowerTail := (1319760501 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3516949319 / 500000000000 : ℝ)
  ledger := by
    have h : (231593767 / 200000000000 : ℚ) +
        (2202162357 / 250000000000000000 : ℚ) / (2302310899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (547606617 / 500000000000 : ℚ) + (1319760501 / 1000000000000 : ℚ) ≤
        (3516949319 / 500000000000 : ℚ) := by norm_num only
    have hc : (((231593767 / 200000000000 : ℚ) +
        (2202162357 / 250000000000000000 : ℚ) / (2302310899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (547606617 / 500000000000 : ℚ) + (1319760501 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3516949319 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13037]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13037 :
    2 * 160 < 13037 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999987 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13037 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13038 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13038. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13038 : WorldParameters where
  hiddenCharge := (1157928907 / 1000000000000 : ℝ)
  frame := (310535500527 / 500000000000 : ℝ)
  moment := (8806885591 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13038 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365786886741 / 250000000000 : ℝ)
    root := (4138050801 / 500000000000 : ℝ) }

noncomputable def scalar13038 : ScalarCertificate 13038 world13038 agent13038 where
  dimensionLo := 13038
  dimensionHi := 13038
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2302674099 / 1000000000000 : ℝ)
  frameLo := (310535500527 / 500000000000 : ℝ)
  frameHi := (365786886741 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13038]
  agentFrame_pos := by norm_num only [agent13038]
  worldRadius := (2302674099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13038]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (547160437 / 500000000000 : ℝ)
  lowerTail := (263752439 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3515555599 / 500000000000 : ℝ)
  ledger := by
    have h : (1157928907 / 1000000000000 : ℚ) +
        (8806885591 / 1000000000000000000 : ℚ) / (2302674099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (547160437 / 500000000000 : ℚ) + (263752439 / 200000000000 : ℚ) ≤
        (3515555599 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1157928907 / 1000000000000 : ℚ) +
        (8806885591 / 1000000000000000000 : ℚ) / (2302674099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (547160437 / 500000000000 : ℚ) + (263752439 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3515555599 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13038]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13038 :
    2 * 160 < 13038 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (199999901 / 20000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13038 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13039 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13039. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13039 : WorldParameters where
  hiddenCharge := (115788899 / 100000000000 : ℝ)
  frame := (621057878297 / 1000000000000 : ℝ)
  moment := (1100640281 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13039 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292623699491 / 200000000000 : ℝ)
    root := (1034435451 / 125000000000 : ℝ) }

noncomputable def scalar13039 : ScalarCertificate 13039 world13039 agent13039 where
  dimensionLo := 13039
  dimensionHi := 13039
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2303037299 / 1000000000000 : ℝ)
  frameLo := (621057878297 / 1000000000000 : ℝ)
  frameHi := (292623699491 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13039]
  agentFrame_pos := by norm_num only [agent13039]
  worldRadius := (2303037299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13039]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1093429279 / 1000000000000 : ℝ)
  lowerTail := (1317764691 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1405665177 / 200000000000 : ℝ)
  ledger := by
    have h : (115788899 / 100000000000 : ℚ) +
        (1100640281 / 125000000000000000 : ℚ) / (2303037299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1093429279 / 1000000000000 : ℚ) + (1317764691 / 1000000000000 : ℚ) ≤
        (1405665177 / 200000000000 : ℚ) := by norm_num only
    have hc : (((115788899 / 100000000000 : ℚ) +
        (1100640281 / 125000000000000000 : ℚ) / (2303037299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1093429279 / 1000000000000 : ℚ) + (1317764691 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1405665177 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13039]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13039 :
    2 * 160 < 13039 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (312499963 / 31250000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13039 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13040 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13040. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13040 : WorldParameters where
  hiddenCharge := (1157849083 / 1000000000000 : ℝ)
  frame := (31052237879 / 50000000000 : ℝ)
  moment := (4401679699 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13040 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463011921839 / 1000000000000 : ℝ)
    root := (8274865849 / 1000000000000 : ℝ) }

noncomputable def scalar13040 : ScalarCertificate 13040 world13040 agent13040 where
  dimensionLo := 13040
  dimensionHi := 13040
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2303517299 / 1000000000000 : ℝ)
  frameLo := (31052237879 / 50000000000 : ℝ)
  frameHi := (1463011921839 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13040]
  agentFrame_pos := by norm_num only [agent13040]
  worldRadius := (2303517299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13040]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1092346211 / 1000000000000 : ℝ)
  lowerTail := (658257503 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7024929219 / 1000000000000 : ℝ)
  ledger := by
    have h : (1157849083 / 1000000000000 : ℚ) +
        (4401679699 / 500000000000000000 : ℚ) / (2303517299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1092346211 / 1000000000000 : ℚ) + (658257503 / 500000000000 : ℚ) ≤
        (7024929219 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1157849083 / 1000000000000 : ℚ) +
        (4401679699 / 500000000000000000 : ℚ) / (2303517299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1092346211 / 1000000000000 : ℚ) + (658257503 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7024929219 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13040]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13040 :
    2 * 160 < 13040 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999977 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13040 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13041 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13041. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13041 : WorldParameters where
  hiddenCharge := (231561837 / 200000000000 : ℝ)
  frame := (310515819451 / 500000000000 : ℝ)
  moment := (4400798521 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13041 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731491454181 / 500000000000 : ℝ)
    root := (8274248261 / 1000000000000 : ℝ) }

noncomputable def scalar13041 : ScalarCertificate 13041 world13041 agent13041 where
  dimensionLo := 13041
  dimensionHi := 13041
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2303880499 / 1000000000000 : ℝ)
  frameLo := (310515819451 / 500000000000 : ℝ)
  frameHi := (731491454181 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13041]
  agentFrame_pos := by norm_num only [agent13041]
  worldRadius := (2303880499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13041]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (545728241 / 500000000000 : ℝ)
  lowerTail := (263103899 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7022149 / 1000000000 : ℝ)
  ledger := by
    have h : (231561837 / 200000000000 : ℚ) +
        (4400798521 / 500000000000000000 : ℚ) / (2303880499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (545728241 / 500000000000 : ℚ) + (263103899 / 200000000000 : ℚ) ≤
        (7022149 / 1000000000 : ℚ) := by norm_num only
    have hc : (((231561837 / 200000000000 : ℚ) +
        (4400798521 / 500000000000000000 : ℚ) / (2303880499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (545728241 / 500000000000 : ℚ) + (263103899 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7022149 / 1000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13041]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13041 :
    2 * 160 < 13041 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (156249967 / 15625000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13041 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13042 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13042. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13042 : WorldParameters where
  hiddenCharge := (1157769299 / 1000000000000 : ℝ)
  frame := (310509261131 / 500000000000 : ℝ)
  moment := (4399917589 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13042 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462953906607 / 1000000000000 : ℝ)
    root := (1654726169 / 200000000000 : ℝ) }

noncomputable def scalar13042 : ScalarCertificate 13042 world13042 agent13042 where
  dimensionLo := 13042
  dimensionHi := 13042
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2304243699 / 1000000000000 : ℝ)
  frameLo := (310509261131 / 500000000000 : ℝ)
  frameHi := (1462953906607 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13042]
  agentFrame_pos := by norm_num only [agent13042]
  worldRadius := (2304243699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13042]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1090567579 / 1000000000000 : ℝ)
  lowerTail := (328631213 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3509685517 / 500000000000 : ℝ)
  ledger := by
    have h : (1157769299 / 1000000000000 : ℚ) +
        (4399917589 / 500000000000000000 : ℚ) / (2304243699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1090567579 / 1000000000000 : ℚ) + (328631213 / 250000000000 : ℚ) ≤
        (3509685517 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1157769299 / 1000000000000 : ℚ) +
        (4399917589 / 500000000000000000 : ℚ) / (2304243699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1090567579 / 1000000000000 : ℚ) + (328631213 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3509685517 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13042]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13042 :
    2 * 160 < 13042 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999701 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13042 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13043 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13043. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13043 : WorldParameters where
  hiddenCharge := (578864711 / 500000000000 : ℝ)
  frame := (31050270383 / 50000000000 : ℝ)
  moment := (8798073807 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13043 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292584984483 / 200000000000 : ℝ)
    root := (4136506769 / 500000000000 : ℝ) }

noncomputable def scalar13043 : ScalarCertificate 13043 world13043 agent13043 where
  dimensionLo := 13043
  dimensionHi := 13043
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2304606999 / 1000000000000 : ℝ)
  frameLo := (31050270383 / 50000000000 : ℝ)
  frameHi := (292584984483 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13043]
  agentFrame_pos := by norm_num only [agent13043]
  worldRadius := (2304606999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13043]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (544839773 / 500000000000 : ℝ)
  lowerTail := (262706227 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7016595281 / 1000000000000 : ℝ)
  ledger := by
    have h : (578864711 / 500000000000 : ℚ) +
        (8798073807 / 1000000000000000000 : ℚ) / (2304606999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (544839773 / 500000000000 : ℚ) + (262706227 / 200000000000 : ℚ) ≤
        (7016595281 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578864711 / 500000000000 : ℚ) +
        (8798073807 / 1000000000000000000 : ℚ) / (2304606999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (544839773 / 500000000000 : ℚ) + (262706227 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7016595281 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13043]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13043 :
    2 * 160 < 13043 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996841 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13043 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13044 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13044. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13044 : WorldParameters where
  hiddenCharge := (289422389 / 250000000000 : ℝ)
  frame := (124198459019 / 200000000000 : ℝ)
  moment := (8796312929 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13044 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365723987483 / 250000000000 : ℝ)
    root := (517024779 / 62500000000 : ℝ) }

noncomputable def scalar13044 : ScalarCertificate 13044 world13044 agent13044 where
  dimensionLo := 13044
  dimensionHi := 13044
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2304970299 / 1000000000000 : ℝ)
  frameLo := (124198459019 / 200000000000 : ℝ)
  frameHi := (365723987483 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13044]
  agentFrame_pos := by norm_num only [agent13044]
  worldRadius := (2304970299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13044]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (544396189 / 500000000000 : ℝ)
  lowerTail := (1312538327 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7013821861 / 1000000000000 : ℝ)
  ledger := by
    have h : (289422389 / 250000000000 : ℚ) +
        (8796312929 / 1000000000000000000 : ℚ) / (2304970299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (544396189 / 500000000000 : ℚ) + (1312538327 / 1000000000000 : ℚ) ≤
        (7013821861 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((289422389 / 250000000000 : ℚ) +
        (8796312929 / 1000000000000000000 : ℚ) / (2304970299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (544396189 / 500000000000 : ℚ) + (1312538327 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7013821861 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13044]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13044 :
    2 * 160 < 13044 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997637 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13044 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13045 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13045. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13045 : WorldParameters where
  hiddenCharge := (11576497 / 10000000000 : ℝ)
  frame := (310489592283 / 500000000000 : ℝ)
  moment := (8794552543 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13045 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462866994999 / 1000000000000 : ℝ)
    root := (4135889781 / 500000000000 : ℝ) }

noncomputable def scalar13045 : ScalarCertificate 13045 world13045 agent13045 where
  dimensionLo := 13045
  dimensionHi := 13045
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2305333599 / 1000000000000 : ℝ)
  frameLo := (310489592283 / 500000000000 : ℝ)
  frameHi := (1462866994999 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13045]
  agentFrame_pos := by norm_num only [agent13045]
  worldRadius := (2305333599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13045]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (271976513 / 250000000000 : ℝ)
  lowerTail := (131154641 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1752762683 / 250000000000 : ℝ)
  ledger := by
    have h : (11576497 / 10000000000 : ℚ) +
        (8794552543 / 1000000000000000000 : ℚ) / (2305333599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (271976513 / 250000000000 : ℚ) + (131154641 / 100000000000 : ℚ) ≤
        (1752762683 / 250000000000 : ℚ) := by norm_num only
    have hc : (((11576497 / 10000000000 : ℚ) +
        (8794552543 / 1000000000000000000 : ℚ) / (2305333599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (271976513 / 250000000000 : ℚ) + (131154641 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1752762683 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13045]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13045 :
    2 * 160 < 13045 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999551 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13045 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13046 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13046. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13046 : WorldParameters where
  hiddenCharge := (578804927 / 500000000000 : ℝ)
  frame := (310483038037 / 500000000000 : ℝ)
  moment := (175855853 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13046 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731419025881 / 500000000000 : ℝ)
    root := (8271162769 / 1000000000000 : ℝ) }

noncomputable def scalar13046 : ScalarCertificate 13046 world13046 agent13046 where
  dimensionLo := 13046
  dimensionHi := 13046
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2305696899 / 1000000000000 : ℝ)
  frameLo := (310483038037 / 500000000000 : ℝ)
  frameHi := (731419025881 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13046]
  agentFrame_pos := by norm_num only [agent13046]
  worldRadius := (2305696899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13046]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1087020507 / 1000000000000 : ℝ)
  lowerTail := (262111063 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7008281763 / 1000000000000 : ℝ)
  ledger := by
    have h : (578804927 / 500000000000 : ℚ) +
        (175855853 / 20000000000000000 : ℚ) / (2305696899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1087020507 / 1000000000000 : ℚ) + (262111063 / 200000000000 : ℚ) ≤
        (7008281763 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578804927 / 500000000000 : ℚ) +
        (175855853 / 20000000000000000 : ℚ) / (2305696899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1087020507 / 1000000000000 : ℚ) + (262111063 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7008281763 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13046]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13046 :
    2 * 160 < 13046 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996103 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13046 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13047 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13047. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13047 : WorldParameters where
  hiddenCharge := (1157570019 / 1000000000000 : ℝ)
  frame := (310476484809 / 500000000000 : ℝ)
  moment := (8791033249 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13047 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292561824043 / 200000000000 : ℝ)
    root := (8270546209 / 1000000000000 : ℝ) }

noncomputable def scalar13047 : ScalarCertificate 13047 world13047 agent13047 where
  dimensionLo := 13047
  dimensionHi := 13047
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2306060199 / 1000000000000 : ℝ)
  frameLo := (310476484809 / 500000000000 : ℝ)
  frameHi := (292561824043 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13047]
  agentFrame_pos := by norm_num only [agent13047]
  worldRadius := (2306060199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13047]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1086135823 / 1000000000000 : ℝ)
  lowerTail := (1309565127 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3502757561 / 500000000000 : ℝ)
  ledger := by
    have h : (1157570019 / 1000000000000 : ℚ) +
        (8791033249 / 1000000000000000000 : ℚ) / (2306060199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1086135823 / 1000000000000 : ℚ) + (1309565127 / 1000000000000 : ℚ) ≤
        (3502757561 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1157570019 / 1000000000000 : ℚ) +
        (8791033249 / 1000000000000000000 : ℚ) / (2306060199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1086135823 / 1000000000000 : ℚ) + (1309565127 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3502757561 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13047]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13047 :
    2 * 160 < 13047 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999699 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13047 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13048 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13048. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13048 : WorldParameters where
  hiddenCharge := (1157530193 / 1000000000000 : ℝ)
  frame := (620939865197 / 1000000000000 : ℝ)
  moment := (8789274339 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13048 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462780206199 / 1000000000000 : ℝ)
    root := (413496491 / 50000000000 : ℝ) }

noncomputable def scalar13048 : ScalarCertificate 13048 world13048 agent13048 where
  dimensionLo := 13048
  dimensionHi := 13048
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2306423399 / 1000000000000 : ℝ)
  frameLo := (620939865197 / 1000000000000 : ℝ)
  frameHi := (1462780206199 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13048]
  agentFrame_pos := by norm_num only [agent13048]
  worldRadius := (2306423399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13048]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (135656489 / 125000000000 : ℝ)
  lowerTail := (163571969 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3501375383 / 500000000000 : ℝ)
  ledger := by
    have h : (1157530193 / 1000000000000 : ℚ) +
        (8789274339 / 1000000000000000000 : ℚ) / (2306423399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (135656489 / 125000000000 : ℚ) + (163571969 / 125000000000 : ℚ) ≤
        (3501375383 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1157530193 / 1000000000000 : ℚ) +
        (8789274339 / 1000000000000000000 : ℚ) / (2306423399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (135656489 / 125000000000 : ℚ) + (163571969 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3501375383 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13048]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13048 :
    2 * 160 < 13048 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999709 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13048 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13049 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13049. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13049 : WorldParameters where
  hiddenCharge := (578745189 / 500000000000 : ℝ)
  frame := (620926762811 / 1000000000000 : ℝ)
  moment := (4393757961 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13049 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1462751309707 / 1000000000000 : ℝ)
    root := (413465677 / 50000000000 : ℝ) }

noncomputable def scalar13049 : ScalarCertificate 13049 world13049 agent13049 where
  dimensionLo := 13049
  dimensionHi := 13049
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2306786699 / 1000000000000 : ℝ)
  frameLo := (620926762811 / 1000000000000 : ℝ)
  frameHi := (1462751309707 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13049]
  agentFrame_pos := by norm_num only [agent13049]
  worldRadius := (2306786699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13049]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (542184433 / 500000000000 : ℝ)
  lowerTail := (40862103 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6999988609 / 1000000000000 : ℝ)
  ledger := by
    have h : (578745189 / 500000000000 : ℚ) +
        (4393757961 / 500000000000000000 : ℚ) / (2306786699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (542184433 / 500000000000 : ℚ) + (40862103 / 31250000000 : ℚ) ≤
        (6999988609 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((578745189 / 500000000000 : ℚ) +
        (4393757961 / 500000000000000000 : ℚ) / (2306786699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (542184433 / 500000000000 : ℚ) + (40862103 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((6999988609 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13049]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13049 :
    2 * 160 < 13049 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997011 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13049 {← IO.monoMsNow}" : IO Unit)
