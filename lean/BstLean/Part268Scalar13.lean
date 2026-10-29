import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12675 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12675. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12675 : WorldParameters where
  hiddenCharge := (586563613 / 500000000000 : ℝ)
  frame := (39123342887 / 62500000000 : ℝ)
  moment := (1516969 / 160000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12675 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46160141787 / 31250000000 : ℝ)
    root := (4256317329 / 500000000000 : ℝ) }

noncomputable def scalar12675 : ScalarCertificate 12675 world12675 agent12675 where
  dimensionLo := 12675
  dimensionHi := 12675
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2167927399 / 1000000000000 : ℝ)
  frameLo := (39123342887 / 62500000000 : ℝ)
  frameHi := (46160141787 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12675]
  agentFrame_pos := by norm_num only [agent12675]
  worldRadius := (2167927399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12675]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1489657981 / 1000000000000 : ℝ)
  lowerTail := (351569413 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4118531623 / 500000000000 : ℝ)
  ledger := by
    have h : (586563613 / 500000000000 : ℚ) +
        (1516969 / 160000000000000 : ℚ) / (2167927399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1489657981 / 1000000000000 : ℚ) + (351569413 / 200000000000 : ℚ) ≤
        (4118531623 / 500000000000 : ℚ) := by norm_num only
    have hc : (((586563613 / 500000000000 : ℚ) +
        (1516969 / 160000000000000 : ℚ) / (2167927399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1489657981 / 1000000000000 : ℚ) + (351569413 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4118531623 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12675]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12675 :
    2 * 160 < 12675 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (21999999 / 2000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12675 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12676 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12676. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12676 : WorldParameters where
  hiddenCharge := (146635417 / 125000000000 : ℝ)
  frame := (125191917663 / 200000000000 : ℝ)
  moment := (9479101461 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12676 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477092208977 / 1000000000000 : ℝ)
    root := (4255973447 / 500000000000 : ℝ) }

noncomputable def scalar12676 : ScalarCertificate 12676 world12676 agent12676 where
  dimensionLo := 12676
  dimensionHi := 12676
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2168284199 / 1000000000000 : ℝ)
  frameLo := (125191917663 / 200000000000 : ℝ)
  frameHi := (1477092208977 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12676]
  agentFrame_pos := by norm_num only [agent12676]
  worldRadius := (2168284199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12676]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1488393091 / 1000000000000 : ℝ)
  lowerTail := (439115251 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8233288771 / 1000000000000 : ℝ)
  ledger := by
    have h : (146635417 / 125000000000 : ℚ) +
        (9479101461 / 1000000000000000000 : ℚ) / (2168284199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1488393091 / 1000000000000 : ℚ) + (439115251 / 250000000000 : ℚ) ≤
        (8233288771 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((146635417 / 125000000000 : ℚ) +
        (9479101461 / 1000000000000000000 : ℚ) / (2168284199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1488393091 / 1000000000000 : ℚ) + (439115251 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8233288771 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12676]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12676 :
    2 * 160 < 12676 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999993987 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12676 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12677 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12677. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12677 : WorldParameters where
  hiddenCharge := (36657483 / 31250000000 : ℝ)
  frame := (625945692673 / 1000000000000 : ℝ)
  moment := (2369286809 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12677 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369264972329 / 250000000000 : ℝ)
    root := (4255629673 / 500000000000 : ℝ) }

noncomputable def scalar12677 : ScalarCertificate 12677 world12677 agent12677 where
  dimensionLo := 12677
  dimensionHi := 12677
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2168640799 / 1000000000000 : ℝ)
  frameLo := (625945692673 / 1000000000000 : ℝ)
  frameHi := (369264972329 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12677]
  agentFrame_pos := by norm_num only [agent12677]
  worldRadius := (2168640799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12677]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1487129231 / 1000000000000 : ℝ)
  lowerTail := (175507599 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (329180699 / 40000000000 : ℝ)
  ledger := by
    have h : (36657483 / 31250000000 : ℚ) +
        (2369286809 / 250000000000000000 : ℚ) / (2168640799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1487129231 / 1000000000000 : ℚ) + (175507599 / 100000000000 : ℚ) ≤
        (329180699 / 40000000000 : ℚ) := by norm_num only
    have hc : (((36657483 / 31250000000 : ℚ) +
        (2369286809 / 250000000000000000 : ℚ) / (2168640799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1487129231 / 1000000000000 : ℚ) + (175507599 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((329180699 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12677]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12677 :
    2 * 160 < 12677 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999609 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12677 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12678 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12678. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12678 : WorldParameters where
  hiddenCharge := (1172995589 / 1000000000000 : ℝ)
  frame := (125186359853 / 200000000000 : ℝ)
  moment := (9475193573 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12678 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477027590033 / 1000000000000 : ℝ)
    root := (4255286007 / 500000000000 : ℝ) }

noncomputable def scalar12678 : ScalarCertificate 12678 world12678 agent12678 where
  dimensionLo := 12678
  dimensionHi := 12678
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2168997599 / 1000000000000 : ℝ)
  frameLo := (125186359853 / 200000000000 : ℝ)
  frameHi := (1477027590033 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12678]
  agentFrame_pos := by norm_num only [agent12678]
  worldRadius := (2168997599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12678]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1485866809 / 1000000000000 : ℝ)
  lowerTail := (876846237 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8225749477 / 1000000000000 : ℝ)
  ledger := by
    have h : (1172995589 / 1000000000000 : ℚ) +
        (9475193573 / 1000000000000000000 : ℚ) / (2168997599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1485866809 / 1000000000000 : ℚ) + (876846237 / 500000000000 : ℚ) ≤
        (8225749477 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1172995589 / 1000000000000 : ℚ) +
        (9475193573 / 1000000000000000000 : ℚ) / (2168997599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1485866809 / 1000000000000 : ℚ) + (876846237 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8225749477 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12678]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12678 :
    2 * 160 < 12678 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499959 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12678 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12679 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12679. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12679 : WorldParameters where
  hiddenCharge := (1172951733 / 1000000000000 : ℝ)
  frame := (156479477023 / 250000000000 : ℝ)
  moment := (9473240473 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12679 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476995311119 / 1000000000000 : ℝ)
    root := (4254942483 / 500000000000 : ℝ) }

noncomputable def scalar12679 : ScalarCertificate 12679 world12679 agent12679 where
  dimensionLo := 12679
  dimensionHi := 12679
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2169354299 / 1000000000000 : ℝ)
  frameLo := (156479477023 / 250000000000 : ℝ)
  frameHi := (1476995311119 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12679]
  agentFrame_pos := by norm_num only [agent12679]
  worldRadius := (2169354299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12679]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (92787851 / 62500000000 : ℝ)
  lowerTail := (109519389 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8221984891 / 1000000000000 : ℝ)
  ledger := by
    have h : (1172951733 / 1000000000000 : ℚ) +
        (9473240473 / 1000000000000000000 : ℚ) / (2169354299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (92787851 / 62500000000 : ℚ) + (109519389 / 62500000000 : ℚ) ≤
        (8221984891 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1172951733 / 1000000000000 : ℚ) +
        (9473240473 / 1000000000000000000 : ℚ) / (2169354299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (92787851 / 62500000000 : ℚ) + (109519389 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((8221984891 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12679]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12679 :
    2 * 160 < 12679 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997859 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12679 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12680 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12680. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12680 : WorldParameters where
  hiddenCharge := (73306743 / 62500000000 : ℝ)
  frame := (625904019151 / 1000000000000 : ℝ)
  moment := (73994437 / 7812500000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12680 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369220368157 / 250000000000 : ℝ)
    root := (4254599033 / 500000000000 : ℝ) }

noncomputable def scalar12680 : ScalarCertificate 12680 world12680 agent12680 where
  dimensionLo := 12680
  dimensionHi := 12680
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2169822999 / 1000000000000 : ℝ)
  frameLo := (625904019151 / 1000000000000 : ℝ)
  frameHi := (369220368157 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12680]
  agentFrame_pos := by norm_num only [agent12680]
  worldRadius := (2169822999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12680]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1483077307 / 1000000000000 : ℝ)
  lowerTail := (43764607 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4108701267 / 500000000000 : ℝ)
  ledger := by
    have h : (73306743 / 62500000000 : ℚ) +
        (73994437 / 7812500000000000 : ℚ) / (2169822999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1483077307 / 1000000000000 : ℚ) + (43764607 / 25000000000 : ℚ) ≤
        (4108701267 / 500000000000 : ℚ) := by norm_num only
    have hc : (((73306743 / 62500000000 : ℚ) +
        (73994437 / 7812500000000000 : ℚ) / (2169822999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1483077307 / 1000000000000 : ℚ) + (43764607 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4108701267 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12680]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12680 :
    2 * 160 < 12680 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999989 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12680 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12681 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12681. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12681 : WorldParameters where
  hiddenCharge := (234572811 / 200000000000 : ℝ)
  frame := (625890132443 / 1000000000000 : ℝ)
  moment := (9469335961 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12681 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476849229457 / 1000000000000 : ℝ)
    root := (4254255691 / 500000000000 : ℝ) }

noncomputable def scalar12681 : ScalarCertificate 12681 world12681 agent12681 where
  dimensionLo := 12681
  dimensionHi := 12681
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2170179799 / 1000000000000 : ℝ)
  frameLo := (625890132443 / 1000000000000 : ℝ)
  frameHi := (1476849229457 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12681]
  agentFrame_pos := by norm_num only [agent12681]
  worldRadius := (2170179799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12681]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (740909409 / 500000000000 : ℝ)
  lowerTail := (1749204859 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8213644901 / 1000000000000 : ℝ)
  ledger := by
    have h : (234572811 / 200000000000 : ℚ) +
        (9469335961 / 1000000000000000000 : ℚ) / (2170179799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (740909409 / 500000000000 : ℚ) + (1749204859 / 1000000000000 : ℚ) ≤
        (8213644901 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((234572811 / 200000000000 : ℚ) +
        (9469335961 / 1000000000000000000 : ℚ) / (2170179799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (740909409 / 500000000000 : ℚ) + (1749204859 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8213644901 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12681]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12681 :
    2 * 160 < 12681 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999379 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12681 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12682 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12682. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12682 : WorldParameters where
  hiddenCharge := (586410117 / 500000000000 : ℝ)
  frame := (625876247967 / 1000000000000 : ℝ)
  moment := (2366846137 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12682 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46150531457 / 31250000000 : ℝ)
    root := (8507824913 / 1000000000000 : ℝ) }

noncomputable def scalar12682 : ScalarCertificate 12682 world12682 agent12682 where
  dimensionLo := 12682
  dimensionHi := 12682
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2170536499 / 1000000000000 : ℝ)
  frameLo := (625876247967 / 1000000000000 : ℝ)
  frameHi := (46150531457 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12682]
  agentFrame_pos := by norm_num only [agent12682]
  worldRadius := (2170536499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12682]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (296112299 / 200000000000 : ℝ)
  lowerTail := (1747826641 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1026236319 / 125000000000 : ℝ)
  ledger := by
    have h : (586410117 / 500000000000 : ℚ) +
        (2366846137 / 250000000000000000 : ℚ) / (2170536499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296112299 / 200000000000 : ℚ) + (1747826641 / 1000000000000 : ℚ) ≤
        (1026236319 / 125000000000 : ℚ) := by norm_num only
    have hc : (((586410117 / 500000000000 : ℚ) +
        (2366846137 / 250000000000000000 : ℚ) / (2170536499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296112299 / 200000000000 : ℚ) + (1747826641 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1026236319 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12682]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12682 :
    2 * 160 < 12682 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998733 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12682 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12683 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12683. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12683 : WorldParameters where
  hiddenCharge := (46911057 / 40000000000 : ℝ)
  frame := (312931182861 / 500000000000 : ℝ)
  moment := (9465433697 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12683 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476784798199 / 1000000000000 : ℝ)
    root := (425356933 / 50000000000 : ℝ) }

noncomputable def scalar12683 : ScalarCertificate 12683 world12683 agent12683 where
  dimensionLo := 12683
  dimensionHi := 12683
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2170893199 / 1000000000000 : ℝ)
  frameLo := (312931182861 / 500000000000 : ℝ)
  frameHi := (1476784798199 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12683]
  agentFrame_pos := by norm_num only [agent12683]
  worldRadius := (2170893199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12683]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1479305399 / 1000000000000 : ℝ)
  lowerTail := (1746449687 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4103069711 / 500000000000 : ℝ)
  ledger := by
    have h : (46911057 / 40000000000 : ℚ) +
        (9465433697 / 1000000000000000000 : ℚ) / (2170893199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1479305399 / 1000000000000 : ℚ) + (1746449687 / 1000000000000 : ℚ) ≤
        (4103069711 / 500000000000 : ℚ) := by norm_num only
    have hc : (((46911057 / 40000000000 : ℚ) +
        (9465433697 / 1000000000000000000 : ℚ) / (2170893199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1479305399 / 1000000000000 : ℚ) + (1746449687 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4103069711 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12683]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12683 :
    2 * 160 < 12683 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998597 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12683 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12684 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12684. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12684 : WorldParameters where
  hiddenCharge := (1172732627 / 1000000000000 : ℝ)
  frame := (156462121427 / 250000000000 : ℝ)
  moment := (9463483407 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12684 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476752604171 / 1000000000000 : ℝ)
    root := (4253226311 / 500000000000 : ℝ) }

noncomputable def scalar12684 : ScalarCertificate 12684 world12684 agent12684 where
  dimensionLo := 12684
  dimensionHi := 12684
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2171249999 / 1000000000000 : ℝ)
  frameLo := (156462121427 / 250000000000 : ℝ)
  frameHi := (1476752604171 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12684]
  agentFrame_pos := by norm_num only [agent12684]
  worldRadius := (2171249999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12684]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (184756327 / 125000000000 : ℝ)
  lowerTail := (872537047 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (820239151 / 100000000000 : ℝ)
  ledger := by
    have h : (1172732627 / 1000000000000 : ℚ) +
        (9463483407 / 1000000000000000000 : ℚ) / (2171249999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (184756327 / 125000000000 : ℚ) + (872537047 / 500000000000 : ℚ) ≤
        (820239151 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1172732627 / 1000000000000 : ℚ) +
        (9463483407 / 1000000000000000000 : ℚ) / (2171249999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (184756327 / 125000000000 : ℚ) + (872537047 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((820239151 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12684]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12684 :
    2 * 160 < 12684 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997107 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12684 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12685 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12685. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12685 : WorldParameters where
  hiddenCharge := (29317221 / 25000000000 : ℝ)
  frame := (25033384317 / 40000000000 : ℝ)
  moment := (9461533679 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12685 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369180107613 / 250000000000 : ℝ)
    root := (8505766799 / 1000000000000 : ℝ) }

noncomputable def scalar12685 : ScalarCertificate 12685 world12685 agent12685 where
  dimensionLo := 12685
  dimensionHi := 12685
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2171606699 / 1000000000000 : ℝ)
  frameLo := (25033384317 / 40000000000 : ℝ)
  frameHi := (369180107613 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12685]
  agentFrame_pos := by norm_num only [agent12685]
  worldRadius := (2171606699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12685]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (295359399 / 200000000000 : ℝ)
  lowerTail := (871849849 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (819864687 / 100000000000 : ℝ)
  ledger := by
    have h : (29317221 / 25000000000 : ℚ) +
        (9461533679 / 1000000000000000000 : ℚ) / (2171606699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (295359399 / 200000000000 : ℚ) + (871849849 / 500000000000 : ℚ) ≤
        (819864687 / 100000000000 : ℚ) := by norm_num only
    have hc : (((29317221 / 25000000000 : ℚ) +
        (9461533679 / 1000000000000000000 : ℚ) / (2171606699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (295359399 / 200000000000 : ℚ) + (871849849 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((819864687 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12685]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12685 :
    2 * 160 < 12685 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996897 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12685 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12686 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12686. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12686 : WorldParameters where
  hiddenCharge := (586322533 / 500000000000 : ℝ)
  frame := (625820732371 / 1000000000000 : ℝ)
  moment := (18475751 / 1953125000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12686 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476688271111 / 1000000000000 : ℝ)
    root := (8505081191 / 1000000000000 : ℝ) }

noncomputable def scalar12686 : ScalarCertificate 12686 world12686 agent12686 where
  dimensionLo := 12686
  dimensionHi := 12686
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2171963399 / 1000000000000 : ℝ)
  frameLo := (625820732371 / 1000000000000 : ℝ)
  frameHi := (1476688271111 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12686]
  agentFrame_pos := by norm_num only [agent12686]
  worldRadius := (2171963399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12686]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (368886149 / 250000000000 : ℝ)
  lowerTail := (871163281 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4097452719 / 500000000000 : ℝ)
  ledger := by
    have h : (586322533 / 500000000000 : ℚ) +
        (18475751 / 1953125000000000 : ℚ) / (2171963399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (368886149 / 250000000000 : ℚ) + (871163281 / 500000000000 : ℚ) ≤
        (4097452719 / 500000000000 : ℚ) := by norm_num only
    have hc : (((586322533 / 500000000000 : ℚ) +
        (18475751 / 1953125000000000 : ℚ) / (2171963399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (368886149 / 250000000000 : ℚ) + (871163281 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4097452719 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12686]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12686 :
    2 * 160 < 12686 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999981 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12686 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12687 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12687. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12687 : WorldParameters where
  hiddenCharge := (1172601303 / 1000000000000 : ℝ)
  frame := (625806859047 / 1000000000000 : ℝ)
  moment := (9457635907 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12687 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476656132059 / 1000000000000 : ℝ)
    root := (4252197899 / 500000000000 : ℝ) }

noncomputable def scalar12687 : ScalarCertificate 12687 world12687 agent12687 where
  dimensionLo := 12687
  dimensionHi := 12687
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2172320299 / 1000000000000 : ℝ)
  frameLo := (625806859047 / 1000000000000 : ℝ)
  frameHi := (1476656132059 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12687]
  agentFrame_pos := by norm_num only [agent12687]
  worldRadius := (2172320299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12687]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1474293621 / 1000000000000 : ℝ)
  lowerTail := (54404841 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8191167273 / 1000000000000 : ℝ)
  ledger := by
    have h : (1172601303 / 1000000000000 : ℚ) +
        (9457635907 / 1000000000000000000 : ℚ) / (2172320299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1474293621 / 1000000000000 : ℚ) + (54404841 / 31250000000 : ℚ) ≤
        (8191167273 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1172601303 / 1000000000000 : ℚ) +
        (9457635907 / 1000000000000000000 : ℚ) / (2172320299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1474293621 / 1000000000000 : ℚ) + (54404841 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((8191167273 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12687]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12687 :
    2 * 160 < 12687 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999937 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12687 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12688 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12688. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12688 : WorldParameters where
  hiddenCharge := (1172557551 / 1000000000000 : ℝ)
  frame := (625792987951 / 1000000000000 : ℝ)
  moment := (4727843931 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12688 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295324802657 / 200000000000 : ℝ)
    root := (8503710619 / 1000000000000 : ℝ) }

noncomputable def scalar12688 : ScalarCertificate 12688 world12688 agent12688 where
  dimensionLo := 12688
  dimensionHi := 12688
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2172676999 / 1000000000000 : ℝ)
  frameLo := (625792987951 / 1000000000000 : ℝ)
  frameHi := (295324802657 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12688]
  agentFrame_pos := by norm_num only [agent12688]
  worldRadius := (2172676999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12688]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (294608743 / 200000000000 : ℝ)
  lowerTail := (1739584359 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (818743237 / 100000000000 : ℝ)
  ledger := by
    have h : (1172557551 / 1000000000000 : ℚ) +
        (4727843931 / 500000000000000000 : ℚ) / (2172676999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (294608743 / 200000000000 : ℚ) + (1739584359 / 1000000000000 : ℚ) ≤
        (818743237 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1172557551 / 1000000000000 : ℚ) +
        (4727843931 / 500000000000000000 : ℚ) / (2172676999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (294608743 / 200000000000 : ℚ) + (1739584359 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((818743237 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12688]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12688 :
    2 * 160 < 12688 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999621 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12688 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12689 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12689. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12689 : WorldParameters where
  hiddenCharge := (1172513811 / 1000000000000 : ℝ)
  frame := (625779119083 / 1000000000000 : ℝ)
  moment := (4726870189 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12689 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (73829595443 / 50000000000 : ℝ)
    root := (1700605131 / 200000000000 : ℝ) }

noncomputable def scalar12689 : ScalarCertificate 12689 world12689 agent12689 where
  dimensionLo := 12689
  dimensionHi := 12689
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2173033799 / 1000000000000 : ℝ)
  frameLo := (625779119083 / 1000000000000 : ℝ)
  frameHi := (73829595443 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12689]
  agentFrame_pos := by norm_num only [agent12689]
  worldRadius := (2173033799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12689]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (294359023 / 200000000000 : ℝ)
  lowerTail := (869107579 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8183700667 / 1000000000000 : ℝ)
  ledger := by
    have h : (1172513811 / 1000000000000 : ℚ) +
        (4726870189 / 500000000000000000 : ℚ) / (2173033799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (294359023 / 200000000000 : ℚ) + (869107579 / 500000000000 : ℚ) ≤
        (8183700667 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1172513811 / 1000000000000 : ℚ) +
        (4726870189 / 500000000000000000 : ℚ) / (2173033799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (294359023 / 200000000000 : ℚ) + (869107579 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8183700667 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12689]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12689 :
    2 * 160 < 12689 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997149 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12689 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12690 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12690. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12690 : WorldParameters where
  hiddenCharge := (1172470083 / 1000000000000 : ℝ)
  frame := (312882626221 / 500000000000 : ℝ)
  moment := (4725896727 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12690 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476478368681 / 1000000000000 : ℝ)
    root := (4251170453 / 500000000000 : ℝ) }

noncomputable def scalar12690 : ScalarCertificate 12690 world12690 agent12690 where
  dimensionLo := 12690
  dimensionHi := 12690
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2173502799 / 1000000000000 : ℝ)
  frameLo := (312882626221 / 500000000000 : ℝ)
  frameHi := (1476478368681 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12690]
  agentFrame_pos := by norm_num only [agent12690]
  worldRadius := (2173502799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12690]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1470282027 / 1000000000000 : ℝ)
  lowerTail := (347301079 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1022394757 / 125000000000 : ℝ)
  ledger := by
    have h : (1172470083 / 1000000000000 : ℚ) +
        (4725896727 / 500000000000000000 : ℚ) / (2173502799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1470282027 / 1000000000000 : ℚ) + (347301079 / 200000000000 : ℚ) ≤
        (1022394757 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1172470083 / 1000000000000 : ℚ) +
        (4725896727 / 500000000000000000 : ℚ) / (2173502799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1470282027 / 1000000000000 : ℚ) + (347301079 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1022394757 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12690]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12690 :
    2 * 160 < 12690 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997141 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12690 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12691 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12691. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12691 : WorldParameters where
  hiddenCharge := (586213183 / 500000000000 : ℝ)
  frame := (625751388029 / 1000000000000 : ℝ)
  moment := (944984709 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12691 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295289194859 / 200000000000 : ℝ)
    root := (850165637 / 100000000000 : ℝ) }

noncomputable def scalar12691 : ScalarCertificate 12691 world12691 agent12691 where
  dimensionLo := 12691
  dimensionHi := 12691
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2173859899 / 1000000000000 : ℝ)
  frameLo := (625751388029 / 1000000000000 : ℝ)
  frameHi := (295289194859 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12691]
  agentFrame_pos := by norm_num only [agent12691]
  worldRadius := (2173859899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12691]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2295367 / 1562500000 : ℝ)
  lowerTail := (216892181 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4087715051 / 500000000000 : ℝ)
  ledger := by
    have h : (586213183 / 500000000000 : ℚ) +
        (944984709 / 100000000000000000 : ℚ) / (2173859899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2295367 / 1562500000 : ℚ) + (216892181 / 125000000000 : ℚ) ≤
        (4087715051 / 500000000000 : ℚ) := by norm_num only
    have hc : (((586213183 / 500000000000 : ℚ) +
        (944984709 / 100000000000000000 : ℚ) / (2173859899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2295367 / 1562500000 : ℚ) + (216892181 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4087715051 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12691]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12691 :
    2 * 160 < 12691 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998221 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12691 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12692 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12692. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12692 : WorldParameters where
  hiddenCharge := (1172382661 / 1000000000000 : ℝ)
  frame := (312868762921 / 500000000000 : ℝ)
  moment := (9447901287 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12692 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147641360017 / 100000000000 : ℝ)
    root := (8500972049 / 1000000000000 : ℝ) }

noncomputable def scalar12692 : ScalarCertificate 12692 world12692 agent12692 where
  dimensionLo := 12692
  dimensionHi := 12692
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2174217199 / 1000000000000 : ℝ)
  frameLo := (312868762921 / 500000000000 : ℝ)
  frameHi := (147641360017 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12692]
  agentFrame_pos := by norm_num only [agent12692]
  worldRadius := (2174217199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12692]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1467789149 / 1000000000000 : ℝ)
  lowerTail := (86688549 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8171705399 / 1000000000000 : ℝ)
  ledger := by
    have h : (1172382661 / 1000000000000 : ℚ) +
        (9447901287 / 1000000000000000000 : ℚ) / (2174217199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1467789149 / 1000000000000 : ℚ) + (86688549 / 50000000000 : ℚ) ≤
        (8171705399 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1172382661 / 1000000000000 : ℚ) +
        (9447901287 / 1000000000000000000 : ℚ) / (2174217199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1467789149 / 1000000000000 : ℚ) + (86688549 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8171705399 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12692]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12692 :
    2 * 160 < 12692 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999993939 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12692 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12693 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12693. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12693 : WorldParameters where
  hiddenCharge := (1172338967 / 1000000000000 : ℝ)
  frame := (15643091647 / 25000000000 : ℝ)
  moment := (9445956043 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12693 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184547655047 / 125000000000 : ℝ)
    root := (4250143971 / 500000000000 : ℝ) }

noncomputable def scalar12693 : ScalarCertificate 12693 world12693 agent12693 where
  dimensionLo := 12693
  dimensionHi := 12693
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2174574399 / 1000000000000 : ℝ)
  frameLo := (15643091647 / 25000000000 : ℝ)
  frameHi := (184547655047 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12693]
  agentFrame_pos := by norm_num only [agent12693]
  worldRadius := (2174574399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12693]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (293308909 / 200000000000 : ℝ)
  lowerTail := (1732405669 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4083991943 / 500000000000 : ℝ)
  ledger := by
    have h : (1172338967 / 1000000000000 : ℚ) +
        (9445956043 / 1000000000000000000 : ℚ) / (2174574399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (293308909 / 200000000000 : ℚ) + (1732405669 / 1000000000000 : ℚ) ≤
        (4083991943 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1172338967 / 1000000000000 : ℚ) +
        (9445956043 / 1000000000000000000 : ℚ) / (2174574399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (293308909 / 200000000000 : ℚ) + (1732405669 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4083991943 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12693]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12693 :
    2 * 160 < 12693 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995503 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12693 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12694 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12694. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12694 : WorldParameters where
  hiddenCharge := (234459057 / 200000000000 : ℝ)
  frame := (39106863009 / 62500000000 : ℝ)
  moment := (9444011359 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12694 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476348900823 / 1000000000000 : ℝ)
    root := (531225253 / 62500000000 : ℝ) }

noncomputable def scalar12694 : ScalarCertificate 12694 world12694 agent12694 where
  dimensionLo := 12694
  dimensionHi := 12694
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2174931699 / 1000000000000 : ℝ)
  frameLo := (39106863009 / 62500000000 : ℝ)
  frameHi := (1476348900823 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12694]
  agentFrame_pos := by norm_num only [agent12694]
  worldRadius := (2174931699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12694]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1465301267 / 1000000000000 : ℝ)
  lowerTail := (1731041737 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4082132809 / 500000000000 : ℝ)
  ledger := by
    have h : (234459057 / 200000000000 : ℚ) +
        (9444011359 / 1000000000000000000 : ℚ) / (2174931699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1465301267 / 1000000000000 : ℚ) + (1731041737 / 1000000000000 : ℚ) ≤
        (4082132809 / 500000000000 : ℚ) := by norm_num only
    have hc : (((234459057 / 200000000000 : ℚ) +
        (9444011359 / 1000000000000000000 : ℚ) / (2174931699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1465301267 / 1000000000000 : ℚ) + (1731041737 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4082132809 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12694]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12694 :
    2 * 160 < 12694 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995003 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12694 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12695 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12695. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12695 : WorldParameters where
  hiddenCharge := (234450323 / 200000000000 : ℝ)
  frame := (78211994079 / 125000000000 : ℝ)
  moment := (4721033617 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12695 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476316575583 / 1000000000000 : ℝ)
    root := (531182523 / 62500000000 : ℝ) }

noncomputable def scalar12695 : ScalarCertificate 12695 world12695 agent12695 where
  dimensionLo := 12695
  dimensionHi := 12695
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2175288999 / 1000000000000 : ℝ)
  frameLo := (78211994079 / 125000000000 : ℝ)
  frameHi := (1476316575583 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12695]
  agentFrame_pos := by norm_num only [agent12695]
  worldRadius := (2175288999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12695]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (915037 / 625000000 : ℝ)
  lowerTail := (864839527 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1020068817 / 125000000000 : ℝ)
  ledger := by
    have h : (234450323 / 200000000000 : ℚ) +
        (4721033617 / 500000000000000000 : ℚ) / (2175288999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (915037 / 625000000 : ℚ) + (864839527 / 500000000000 : ℚ) ≤
        (1020068817 / 125000000000 : ℚ) := by norm_num only
    have hc : (((234450323 / 200000000000 : ℚ) +
        (4721033617 / 500000000000000000 : ℚ) / (2175288999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (915037 / 625000000 : ℚ) + (864839527 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1020068817 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12695]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12695 :
    2 * 160 < 12695 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999261 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12695 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12696 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12696. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12696 : WorldParameters where
  hiddenCharge := (293051989 / 250000000000 : ℝ)
  frame := (39105131209 / 62500000000 : ℝ)
  moment := (2360030917 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12696 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369071067641 / 250000000000 : ℝ)
    root := (4249118451 / 500000000000 : ℝ) }

noncomputable def scalar12696 : ScalarCertificate 12696 world12696 agent12696 where
  dimensionLo := 12696
  dimensionHi := 12696
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2175646299 / 1000000000000 : ℝ)
  frameLo := (39105131209 / 62500000000 : ℝ)
  frameHi := (369071067641 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12696]
  agentFrame_pos := by norm_num only [agent12696]
  worldRadius := (2175646299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12696]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1462818369 / 1000000000000 : ℝ)
  lowerTail := (432079413 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8156838693 / 1000000000000 : ℝ)
  ledger := by
    have h : (293051989 / 250000000000 : ℚ) +
        (2360030917 / 250000000000000000 : ℚ) / (2175646299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1462818369 / 1000000000000 : ℚ) + (432079413 / 250000000000 : ℚ) ≤
        (8156838693 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((293051989 / 250000000000 : ℚ) +
        (2360030917 / 250000000000000000 : ℚ) / (2175646299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1462818369 / 1000000000000 : ℚ) + (432079413 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8156838693 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12696]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12696 :
    2 * 160 < 12696 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999997 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12696 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12697 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12697. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12697 : WorldParameters where
  hiddenCharge := (1172164309 / 1000000000000 : ℝ)
  frame := (15641706207 / 25000000000 : ℝ)
  moment := (4719090331 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12697 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369062996439 / 250000000000 : ℝ)
    root := (8497553649 / 1000000000000 : ℝ) }

noncomputable def scalar12697 : ScalarCertificate 12697 world12697 agent12697 where
  dimensionLo := 12697
  dimensionHi := 12697
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2176003499 / 1000000000000 : ℝ)
  frameLo := (15641706207 / 25000000000 : ℝ)
  frameHi := (369062996439 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12697]
  agentFrame_pos := by norm_num only [agent12697]
  worldRadius := (2176003499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12697]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (365394671 / 250000000000 : ℝ)
  lowerTail := (863478717 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2038282521 / 250000000000 : ℝ)
  ledger := by
    have h : (1172164309 / 1000000000000 : ℚ) +
        (4719090331 / 500000000000000000 : ℚ) / (2176003499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (365394671 / 250000000000 : ℚ) + (863478717 / 500000000000 : ℚ) ≤
        (2038282521 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1172164309 / 1000000000000 : ℚ) +
        (4719090331 / 500000000000000000 : ℚ) / (2176003499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (365394671 / 250000000000 : ℚ) + (863478717 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2038282521 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12697]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12697 :
    2 * 160 < 12697 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999837 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12697 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12698 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12698. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12698 : WorldParameters where
  hiddenCharge := (1172120673 / 1000000000000 : ℝ)
  frame := (312827199719 / 500000000000 : ℝ)
  moment := (4718119107 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12698 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369054930287 / 250000000000 : ℝ)
    root := (8496870609 / 1000000000000 : ℝ) }

noncomputable def scalar12698 : ScalarCertificate 12698 world12698 agent12698 where
  dimensionLo := 12698
  dimensionHi := 12698
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2176360799 / 1000000000000 : ℝ)
  frameLo := (312827199719 / 500000000000 : ℝ)
  frameHi := (369054930287 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12698]
  agentFrame_pos := by norm_num only [agent12698]
  worldRadius := (2176360799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12698]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (9127127 / 6250000000 : ℝ)
  lowerTail := (172559859 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8149424709 / 1000000000000 : ℝ)
  ledger := by
    have h : (1172120673 / 1000000000000 : ℚ) +
        (4718119107 / 500000000000000000 : ℚ) / (2176360799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (9127127 / 6250000000 : ℚ) + (172559859 / 100000000000 : ℚ) ≤
        (8149424709 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1172120673 / 1000000000000 : ℚ) +
        (4718119107 / 500000000000000000 : ℚ) / (2176360799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (9127127 / 6250000000 : ℚ) + (172559859 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8149424709 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12698]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12698 :
    2 * 160 < 12698 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996273 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12698 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12699 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12699. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12699 : WorldParameters where
  hiddenCharge := (1172077049 / 1000000000000 : ℝ)
  frame := (625640552819 / 1000000000000 : ℝ)
  moment := (377371853 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12699 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295237494163 / 200000000000 : ℝ)
    root := (8496187783 / 1000000000000 : ℝ) }

noncomputable def scalar12699 : ScalarCertificate 12699 world12699 agent12699 where
  dimensionLo := 12699
  dimensionHi := 12699
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2176718099 / 1000000000000 : ℝ)
  frameLo := (625640552819 / 1000000000000 : ℝ)
  frameHi := (295237494163 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12699]
  agentFrame_pos := by norm_num only [agent12699]
  worldRadius := (2176718099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12699]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1459103161 / 1000000000000 : ℝ)
  lowerTail := (172424099 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8145722503 / 1000000000000 : ℝ)
  ledger := by
    have h : (1172077049 / 1000000000000 : ℚ) +
        (377371853 / 40000000000000000 : ℚ) / (2176718099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1459103161 / 1000000000000 : ℚ) + (172424099 / 100000000000 : ℚ) ≤
        (8145722503 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1172077049 / 1000000000000 : ℚ) +
        (377371853 / 40000000000000000 : ℚ) / (2176718099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1459103161 / 1000000000000 : ℚ) + (172424099 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8145722503 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12699]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12699 :
    2 * 160 < 12699 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998641 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12699 {← IO.monoMsNow}" : IO Unit)
