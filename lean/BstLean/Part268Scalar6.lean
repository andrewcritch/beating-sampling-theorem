import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12500 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12500. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12500 : WorldParameters where
  hiddenCharge := (590495577 / 500000000000 : ℝ)
  frame := (628440561077 / 1000000000000 : ℝ)
  moment := (1966401901 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12500 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1484383362979 / 1000000000000 : ℝ)
    root := (4317859493 / 500000000000 : ℝ) }

noncomputable def scalar12500 : ScalarCertificate 12500 world12500 agent12500 where
  dimensionLo := 12500
  dimensionHi := 12500
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2104016999 / 1000000000000 : ℝ)
  frameLo := (628440561077 / 1000000000000 : ℝ)
  frameHi := (1484383362979 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12500]
  agentFrame_pos := by norm_num only [agent12500]
  worldRadius := (2104016999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12500]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (69446423 / 40000000000 : ℝ)
  lowerTail := (202754309 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8964816483 / 1000000000000 : ℝ)
  ledger := by
    have h : (590495577 / 500000000000 : ℚ) +
        (1966401901 / 200000000000000000 : ℚ) / (2104016999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (69446423 / 40000000000 : ℚ) + (202754309 / 100000000000 : ℚ) ≤
        (8964816483 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((590495577 / 500000000000 : ℚ) +
        (1966401901 / 200000000000000000 : ℚ) / (2104016999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (69446423 / 40000000000 : ℚ) + (202754309 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8964816483 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12500]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12500 :
    2 * 160 < 12500 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997547 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12500 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12501 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12501. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12501 : WorldParameters where
  hiddenCharge := (590472581 / 500000000000 : ℝ)
  frame := (628426263079 / 1000000000000 : ℝ)
  moment := (78639623 / 8000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12501 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (371087248789 / 250000000000 : ℝ)
    root := (4317500143 / 500000000000 : ℝ) }

noncomputable def scalar12501 : ScalarCertificate 12501 world12501 agent12501 where
  dimensionLo := 12501
  dimensionHi := 12501
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2104368799 / 1000000000000 : ℝ)
  frameLo := (628426263079 / 1000000000000 : ℝ)
  frameHi := (371087248789 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12501]
  agentFrame_pos := by norm_num only [agent12501]
  worldRadius := (2104368799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12501]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1734660401 / 1000000000000 : ℝ)
  lowerTail := (2025915251 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8960435531 / 1000000000000 : ℝ)
  ledger := by
    have h : (590472581 / 500000000000 : ℚ) +
        (78639623 / 8000000000000000 : ℚ) / (2104368799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1734660401 / 1000000000000 : ℚ) + (2025915251 / 1000000000000 : ℚ) ≤
        (8960435531 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((590472581 / 500000000000 : ℚ) +
        (78639623 / 8000000000000000 : ℚ) / (2104368799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1734660401 / 1000000000000 : ℚ) + (2025915251 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8960435531 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12501]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12501 :
    2 * 160 < 12501 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996489 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12501 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12502 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12502. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12502 : WorldParameters where
  hiddenCharge := (1180899183 / 1000000000000 : ℝ)
  frame := (31420598371 / 50000000000 : ℝ)
  moment := (4913948423 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12502 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185539293929 / 125000000000 : ℝ)
    root := (8634281883 / 1000000000000 : ℝ) }

noncomputable def scalar12502 : ScalarCertificate 12502 world12502 agent12502 where
  dimensionLo := 12502
  dimensionHi := 12502
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2104720999 / 1000000000000 : ℝ)
  frameLo := (31420598371 / 50000000000 : ℝ)
  frameHi := (185539293929 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12502]
  agentFrame_pos := by norm_num only [agent12502]
  worldRadius := (2104720999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12502]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (866580347 / 500000000000 : ℝ)
  lowerTail := (2024287613 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8956055233 / 1000000000000 : ℝ)
  ledger := by
    have h : (1180899183 / 1000000000000 : ℚ) +
        (4913948423 / 500000000000000000 : ℚ) / (2104720999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (866580347 / 500000000000 : ℚ) + (2024287613 / 1000000000000 : ℚ) ≤
        (8956055233 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1180899183 / 1000000000000 : ℚ) +
        (4913948423 / 500000000000000000 : ℚ) / (2104720999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (866580347 / 500000000000 : ℚ) + (2024287613 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8956055233 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12502]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12502 :
    2 * 160 < 12502 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999131 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12502 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12503 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12503. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12503 : WorldParameters where
  hiddenCharge := (36901663 / 31250000000 : ℝ)
  frame := (314198837049 / 500000000000 : ℝ)
  moment := (4912920709 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12503 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (11595935111 / 7812500000 : ℝ)
    root := (1726712727 / 200000000000 : ℝ) }

noncomputable def scalar12503 : ScalarCertificate 12503 world12503 agent12503 where
  dimensionLo := 12503
  dimensionHi := 12503
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2105073099 / 1000000000000 : ℝ)
  frameLo := (314198837049 / 500000000000 : ℝ)
  frameHi := (11595935111 / 7812500000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12503]
  agentFrame_pos := by norm_num only [agent12503]
  worldRadius := (2105073099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12503]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1731662149 / 1000000000000 : ℝ)
  lowerTail := (2022661127 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8951678293 / 1000000000000 : ℝ)
  ledger := by
    have h : (36901663 / 31250000000 : ℚ) +
        (4912920709 / 500000000000000000 : ℚ) / (2105073099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1731662149 / 1000000000000 : ℚ) + (2022661127 / 1000000000000 : ℚ) ≤
        (8951678293 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((36901663 / 31250000000 : ℚ) +
        (4912920709 / 500000000000000000 : ℚ) / (2105073099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1731662149 / 1000000000000 : ℚ) + (2022661127 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8951678293 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12503]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12503 :
    2 * 160 < 12503 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199998801 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12503 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12504 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12504. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12504 : WorldParameters where
  hiddenCharge := (1180807261 / 1000000000000 : ℝ)
  frame := (628383383113 / 1000000000000 : ℝ)
  moment := (982378659 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12504 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1484245047327 / 1000000000000 : ℝ)
    root := (4316422807 / 500000000000 : ℝ) }

noncomputable def scalar12504 : ScalarCertificate 12504 world12504 agent12504 where
  dimensionLo := 12504
  dimensionHi := 12504
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2105425499 / 1000000000000 : ℝ)
  frameLo := (628383383113 / 1000000000000 : ℝ)
  frameHi := (1484245047327 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12504]
  agentFrame_pos := by norm_num only [agent12504]
  worldRadius := (2105425499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12504]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (865082681 / 500000000000 : ℝ)
  lowerTail := (40420729 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8947305119 / 1000000000000 : ℝ)
  ledger := by
    have h : (1180807261 / 1000000000000 : ℚ) +
        (982378659 / 100000000000000000 : ℚ) / (2105425499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (865082681 / 500000000000 : ℚ) + (40420729 / 20000000000 : ℚ) ≤
        (8947305119 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1180807261 / 1000000000000 : ℚ) +
        (982378659 / 100000000000000000 : ℚ) / (2105425499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (865082681 / 500000000000 : ℚ) + (40420729 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8947305119 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12504]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12504 :
    2 * 160 < 12504 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999401 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12504 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12505 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12505. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12505 : WorldParameters where
  hiddenCharge := (590380659 / 500000000000 : ℝ)
  frame := (125673818893 / 200000000000 : ℝ)
  moment := (9821732363 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12505 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742105214333 / 500000000000 : ℝ)
    root := (8632127819 / 1000000000000 : ℝ) }

noncomputable def scalar12505 : ScalarCertificate 12505 world12505 agent12505 where
  dimensionLo := 12505
  dimensionHi := 12505
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2105777699 / 1000000000000 : ℝ)
  frameLo := (125673818893 / 200000000000 : ℝ)
  frameHi := (742105214333 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12505]
  agentFrame_pos := by norm_num only [agent12505]
  worldRadius := (2105777699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12505]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (432167479 / 250000000000 : ℝ)
  lowerTail := (252426643 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8942935907 / 1000000000000 : ℝ)
  ledger := by
    have h : (590380659 / 500000000000 : ℚ) +
        (9821732363 / 1000000000000000000 : ℚ) / (2105777699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (432167479 / 250000000000 : ℚ) + (252426643 / 125000000000 : ℚ) ≤
        (8942935907 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((590380659 / 500000000000 : ℚ) +
        (9821732363 / 1000000000000000000 : ℚ) / (2105777699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (432167479 / 250000000000 : ℚ) + (252426643 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8942935907 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12505]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12505 :
    2 * 160 < 12505 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998583 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12505 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12506 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12506. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12506 : WorldParameters where
  hiddenCharge := (295178847 / 250000000000 : ℝ)
  frame := (628354808153 / 1000000000000 : ℝ)
  moment := (613729921 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12506 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742087913143 / 500000000000 : ℝ)
    root := (8631410319 / 1000000000000 : ℝ) }

noncomputable def scalar12506 : ScalarCertificate 12506 world12506 agent12506 where
  dimensionLo := 12506
  dimensionHi := 12506
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2106129899 / 1000000000000 : ℝ)
  frameLo := (628354808153 / 1000000000000 : ℝ)
  frameHi := (742087913143 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12506]
  agentFrame_pos := by norm_num only [agent12506]
  worldRadius := (2106129899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12506]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (86358801 / 50000000000 : ℝ)
  lowerTail := (100889571 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4469285329 / 500000000000 : ℝ)
  ledger := by
    have h : (295178847 / 250000000000 : ℚ) +
        (613729921 / 62500000000000000 : ℚ) / (2106129899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (86358801 / 50000000000 : ℚ) + (100889571 / 50000000000 : ℚ) ≤
        (4469285329 / 500000000000 : ℚ) := by norm_num only
    have hc : (((295178847 / 250000000000 : ℚ) +
        (613729921 / 62500000000000000 : ℚ) / (2106129899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (86358801 / 50000000000 : ℚ) + (100889571 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4469285329 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12506]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12506 :
    2 * 160 < 12506 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999361 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12506 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12507 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12507. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12507 : WorldParameters where
  hiddenCharge := (118066947 / 100000000000 : ℝ)
  frame := (628340524177 / 1000000000000 : ℝ)
  moment := (9817625709 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12507 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1484141246139 / 1000000000000 : ℝ)
    root := (539418311 / 62500000000 : ℝ) }

noncomputable def scalar12507 : ScalarCertificate 12507 world12507 agent12507 where
  dimensionLo := 12507
  dimensionHi := 12507
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2106482199 / 1000000000000 : ℝ)
  frameLo := (628340524177 / 1000000000000 : ℝ)
  frameHi := (1484141246139 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12507]
  agentFrame_pos := by norm_num only [agent12507]
  worldRadius := (2106482199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12507]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (862841833 / 500000000000 : ℝ)
  lowerTail := (1008085643 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4467104579 / 500000000000 : ℝ)
  ledger := by
    have h : (118066947 / 100000000000 : ℚ) +
        (9817625709 / 1000000000000000000 : ℚ) / (2106482199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (862841833 / 500000000000 : ℚ) + (1008085643 / 500000000000 : ℚ) ≤
        (4467104579 / 500000000000 : ℚ) := by norm_num only
    have hc : (((118066947 / 100000000000 : ℚ) +
        (9817625709 / 1000000000000000000 : ℚ) / (2106482199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (862841833 / 500000000000 : ℚ) + (1008085643 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4467104579 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12507]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12507 :
    2 * 160 < 12507 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999913 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12507 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12508 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12508. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12508 : WorldParameters where
  hiddenCharge := (236124713 / 200000000000 : ℝ)
  frame := (125665248507 / 200000000000 : ℝ)
  moment := (4907786641 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12508 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1484106688211 / 1000000000000 : ℝ)
    root := (4314987929 / 500000000000 : ℝ) }

noncomputable def scalar12508 : ScalarCertificate 12508 world12508 agent12508 where
  dimensionLo := 12508
  dimensionHi := 12508
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2106834499 / 1000000000000 : ℝ)
  frameLo := (125665248507 / 200000000000 : ℝ)
  frameHi := (1484106688211 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12508]
  agentFrame_pos := by norm_num only [agent12508]
  worldRadius := (2106834499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12508]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (86209641 / 50000000000 : ℝ)
  lowerTail := (2014552699 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4464925771 / 500000000000 : ℝ)
  ledger := by
    have h : (236124713 / 200000000000 : ℚ) +
        (4907786641 / 500000000000000000 : ℚ) / (2106834499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (86209641 / 50000000000 : ℚ) + (2014552699 / 1000000000000 : ℚ) ≤
        (4464925771 / 500000000000 : ℚ) := by norm_num only
    have hc : (((236124713 / 200000000000 : ℚ) +
        (4907786641 / 500000000000000000 : ℚ) / (2106834499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (86209641 / 50000000000 : ℚ) + (2014552699 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4464925771 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12508]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12508 :
    2 * 160 < 12508 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999397 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12508 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12509 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12509. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12509 : WorldParameters where
  hiddenCharge := (147572209 / 125000000000 : ℝ)
  frame := (628311963227 / 1000000000000 : ℝ)
  moment := (4906760727 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12509 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148407215249 / 100000000000 : ℝ)
    root := (1725851793 / 200000000000 : ℝ) }

noncomputable def scalar12509 : ScalarCertificate 12509 world12509 agent12509 where
  dimensionLo := 12509
  dimensionHi := 12509
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2107186699 / 1000000000000 : ℝ)
  frameLo := (628311963227 / 1000000000000 : ℝ)
  frameHi := (148407215249 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12509]
  agentFrame_pos := by norm_num only [agent12509]
  worldRadius := (2107186699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12509]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1722703379 / 1000000000000 : ℝ)
  lowerTail := (503233887 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2231374451 / 250000000000 : ℝ)
  ledger := by
    have h : (147572209 / 125000000000 : ℚ) +
        (4906760727 / 500000000000000000 : ℚ) / (2107186699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1722703379 / 1000000000000 : ℚ) + (503233887 / 250000000000 : ℚ) ≤
        (2231374451 / 250000000000 : ℚ) := by norm_num only
    have hc : (((147572209 / 125000000000 : ℚ) +
        (4906760727 / 500000000000000000 : ℚ) / (2107186699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1722703379 / 1000000000000 : ℚ) + (503233887 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2231374451 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12509]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12509 :
    2 * 160 < 12509 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999839 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12509 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12510 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12510. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12510 : WorldParameters where
  hiddenCharge := (1180531791 / 1000000000000 : ℝ)
  frame := (628297686253 / 1000000000000 : ℝ)
  moment := (392458809 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12510 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483954008581 / 1000000000000 : ℝ)
    root := (8628542367 / 1000000000000 : ℝ) }

noncomputable def scalar12510 : ScalarCertificate 12510 world12510 agent12510 where
  dimensionLo := 12510
  dimensionHi := 12510
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2107648599 / 1000000000000 : ℝ)
  frameLo := (628297686253 / 1000000000000 : ℝ)
  frameHi := (1483954008581 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12510]
  agentFrame_pos := by norm_num only [agent12510]
  worldRadius := (2107648599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12510]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1720900673 / 1000000000000 : ℝ)
  lowerTail := (2010919729 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8920203023 / 1000000000000 : ℝ)
  ledger := by
    have h : (1180531791 / 1000000000000 : ℚ) +
        (392458809 / 40000000000000000 : ℚ) / (2107648599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1720900673 / 1000000000000 : ℚ) + (2010919729 / 1000000000000 : ℚ) ≤
        (8920203023 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1180531791 / 1000000000000 : ℚ) +
        (392458809 / 40000000000000000 : ℚ) / (2107648599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1720900673 / 1000000000000 : ℚ) + (2010919729 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8920203023 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12510]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12510 :
    2 * 160 < 12510 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997483 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12510 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12511 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12511. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12511 : WorldParameters where
  hiddenCharge := (1180485923 / 1000000000000 : ℝ)
  frame := (157070852903 / 250000000000 : ℝ)
  moment := (2452354899 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12511 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296783902459 / 200000000000 : ℝ)
    root := (345113037 / 40000000000 : ℝ) }

noncomputable def scalar12511 : ScalarCertificate 12511 world12511 agent12511 where
  dimensionLo := 12511
  dimensionHi := 12511
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2108000999 / 1000000000000 : ℝ)
  frameLo := (157070852903 / 250000000000 : ℝ)
  frameHi := (296783902459 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12511]
  agentFrame_pos := by norm_num only [agent12511]
  worldRadius := (2108000999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12511]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1719414633 / 1000000000000 : ℝ)
  lowerTail := (2009306107 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2228964403 / 250000000000 : ℝ)
  ledger := by
    have h : (1180485923 / 1000000000000 : ℚ) +
        (2452354899 / 250000000000000000 : ℚ) / (2108000999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1719414633 / 1000000000000 : ℚ) + (2009306107 / 1000000000000 : ℚ) ≤
        (2228964403 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1180485923 / 1000000000000 : ℚ) +
        (2452354899 / 250000000000000000 : ℚ) / (2108000999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1719414633 / 1000000000000 : ℚ) + (2009306107 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2228964403 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12511]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12511 :
    2 * 160 < 12511 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997239 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12511 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12512 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12512. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12512 : WorldParameters where
  hiddenCharge := (1180440067 / 1000000000000 : ℝ)
  frame := (628269139303 / 1000000000000 : ℝ)
  moment := (1961473913 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12512 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483885038179 / 1000000000000 : ℝ)
    root := (2156777427 / 250000000000 : ℝ) }

noncomputable def scalar12512 : ScalarCertificate 12512 world12512 agent12512 where
  dimensionLo := 12512
  dimensionHi := 12512
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2108353299 / 1000000000000 : ℝ)
  frameLo := (628269139303 / 1000000000000 : ℝ)
  frameHi := (1483885038179 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12512]
  agentFrame_pos := by norm_num only [agent12512]
  worldRadius := (2108353299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12512]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1717929993 / 1000000000000 : ℝ)
  lowerTail := (2007693917 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2227879017 / 250000000000 : ℝ)
  ledger := by
    have h : (1180440067 / 1000000000000 : ℚ) +
        (1961473913 / 200000000000000000 : ℚ) / (2108353299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1717929993 / 1000000000000 : ℚ) + (2007693917 / 1000000000000 : ℚ) ≤
        (2227879017 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1180440067 / 1000000000000 : ℚ) +
        (1961473913 / 200000000000000000 : ℚ) / (2108353299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1717929993 / 1000000000000 : ℚ) + (2007693917 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2227879017 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12512]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12512 :
    2 * 160 < 12512 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997607 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12512 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12513 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12513. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12513 : WorldParameters where
  hiddenCharge := (1180394223 / 1000000000000 : ℝ)
  frame := (25130194773 / 40000000000 : ℝ)
  moment := (9805320133 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12513 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (741925290129 / 500000000000 : ℝ)
    root := (1725278743 / 200000000000 : ℝ) }

noncomputable def scalar12513 : ScalarCertificate 12513 world12513 agent12513 where
  dimensionLo := 12513
  dimensionHi := 12513
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2108705599 / 1000000000000 : ℝ)
  frameLo := (25130194773 / 40000000000 : ℝ)
  frameHi := (741925290129 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12513]
  agentFrame_pos := by norm_num only [agent12513]
  worldRadius := (2108705599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12513]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1716446821 / 1000000000000 : ℝ)
  lowerTail := (501520807 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4453589159 / 500000000000 : ℝ)
  ledger := by
    have h : (1180394223 / 1000000000000 : ℚ) +
        (9805320133 / 1000000000000000000 : ℚ) / (2108705599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1716446821 / 1000000000000 : ℚ) + (501520807 / 250000000000 : ℚ) ≤
        (4453589159 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1180394223 / 1000000000000 : ℚ) +
        (9805320133 / 1000000000000000000 : ℚ) / (2108705599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1716446821 / 1000000000000 : ℚ) + (501520807 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4453589159 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12513]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12513 :
    2 * 160 < 12513 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997441 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12513 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12514 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12514. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12514 : WorldParameters where
  hiddenCharge := (147543549 / 125000000000 : ℝ)
  frame := (628240601679 / 1000000000000 : ℝ)
  moment := (9803271299 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12514 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483816144483 / 1000000000000 : ℝ)
    root := (2156419487 / 250000000000 : ℝ) }

noncomputable def scalar12514 : ScalarCertificate 12514 world12514 agent12514 where
  dimensionLo := 12514
  dimensionHi := 12514
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2109057899 / 1000000000000 : ℝ)
  frameLo := (628240601679 / 1000000000000 : ℝ)
  frameHi := (1483816144483 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12514]
  agentFrame_pos := by norm_num only [agent12514]
  worldRadius := (2109057899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12514]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1714965147 / 1000000000000 : ℝ)
  lowerTail := (501118519 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8902844427 / 1000000000000 : ℝ)
  ledger := by
    have h : (147543549 / 125000000000 : ℚ) +
        (9803271299 / 1000000000000000000 : ℚ) / (2109057899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1714965147 / 1000000000000 : ℚ) + (501118519 / 250000000000 : ℚ) ≤
        (8902844427 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((147543549 / 125000000000 : ℚ) +
        (9803271299 / 1000000000000000000 : ℚ) / (2109057899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1714965147 / 1000000000000 : ℚ) + (501118519 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8902844427 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12514]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12514 :
    2 * 160 < 12514 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998917 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12514 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12515 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12515. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12515 : WorldParameters where
  hiddenCharge := (1180302573 / 1000000000000 : ℝ)
  frame := (628226336363 / 1000000000000 : ℝ)
  moment := (1225152883 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12515 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37094543271 / 25000000000 : ℝ)
    root := (4312481237 / 500000000000 : ℝ) }

noncomputable def scalar12515 : ScalarCertificate 12515 world12515 agent12515 where
  dimensionLo := 12515
  dimensionHi := 12515
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2109410199 / 1000000000000 : ℝ)
  frameLo := (628226336363 / 1000000000000 : ℝ)
  frameHi := (37094543271 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12515]
  agentFrame_pos := by norm_num only [agent12515]
  worldRadius := (2109410199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12515]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1713485037 / 1000000000000 : ℝ)
  lowerTail := (62589579 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (278078579 / 31250000000 : ℝ)
  ledger := by
    have h : (1180302573 / 1000000000000 : ℚ) +
        (1225152883 / 125000000000000000 : ℚ) / (2109410199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1713485037 / 1000000000000 : ℚ) + (62589579 / 31250000000 : ℚ) ≤
        (278078579 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1180302573 / 1000000000000 : ℚ) +
        (1225152883 / 125000000000000000 : ℚ) / (2109410199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1713485037 / 1000000000000 : ℚ) + (62589579 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((278078579 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12515]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12515 :
    2 * 160 < 12515 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998183 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12515 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12516 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12516. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12516 : WorldParameters where
  hiddenCharge := (590128383 / 500000000000 : ℝ)
  frame := (314106036689 / 500000000000 : ℝ)
  moment := (4899587713 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12516 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (741873666679 / 500000000000 : ℝ)
    root := (1724849431 / 200000000000 : ℝ) }

noncomputable def scalar12516 : ScalarCertificate 12516 world12516 agent12516 where
  dimensionLo := 12516
  dimensionHi := 12516
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2109762499 / 1000000000000 : ℝ)
  frameLo := (314106036689 / 500000000000 : ℝ)
  frameHi := (741873666679 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12516]
  agentFrame_pos := by norm_num only [agent12516]
  worldRadius := (2109762499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12516]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (856003161 / 500000000000 : ℝ)
  lowerTail := (250157551 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4447094137 / 500000000000 : ℝ)
  ledger := by
    have h : (590128383 / 500000000000 : ℚ) +
        (4899587713 / 500000000000000000 : ℚ) / (2109762499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (856003161 / 500000000000 : ℚ) + (250157551 / 125000000000 : ℚ) ≤
        (4447094137 / 500000000000 : ℚ) := by norm_num only
    have hc : (((590128383 / 500000000000 : ℚ) +
        (4899587713 / 500000000000000000 : ℚ) / (2109762499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (856003161 / 500000000000 : ℚ) + (250157551 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4447094137 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12516]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12516 :
    2 * 160 < 12516 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999769 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12516 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12517 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12517. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12517 : WorldParameters where
  hiddenCharge := (1180210971 / 1000000000000 : ℝ)
  frame := (628197812721 / 1000000000000 : ℝ)
  moment := (4898564193 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12517 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483712957983 / 1000000000000 : ℝ)
    root := (431176603 / 50000000000 : ℝ) }

noncomputable def scalar12517 : ScalarCertificate 12517 world12517 agent12517 where
  dimensionLo := 12517
  dimensionHi := 12517
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2110114899 / 1000000000000 : ℝ)
  frameLo := (628197812721 / 1000000000000 : ℝ)
  frameHi := (1483712957983 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12517]
  agentFrame_pos := by norm_num only [agent12517]
  worldRadius := (2110114899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12517]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1710529199 / 1000000000000 : ℝ)
  lowerTail := (1999655927 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8889865867 / 1000000000000 : ℝ)
  ledger := by
    have h : (1180210971 / 1000000000000 : ℚ) +
        (4898564193 / 500000000000000000 : ℚ) / (2110114899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1710529199 / 1000000000000 : ℚ) + (1999655927 / 1000000000000 : ℚ) ≤
        (8889865867 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1180210971 / 1000000000000 : ℚ) +
        (4898564193 / 500000000000000000 : ℚ) / (2110114899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1710529199 / 1000000000000 : ℚ) + (1999655927 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8889865867 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12517]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12517 :
    2 * 160 < 12517 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (85937499 / 7812500000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12517 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12518 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12518. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12518 : WorldParameters where
  hiddenCharge := (1180165189 / 1000000000000 : ℝ)
  frame := (628183554393 / 1000000000000 : ℝ)
  moment := (9795081943 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12518 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46364956397 / 31250000000 : ℝ)
    root := (862281719 / 100000000000 : ℝ) }

noncomputable def scalar12518 : ScalarCertificate 12518 world12518 agent12518 where
  dimensionLo := 12518
  dimensionHi := 12518
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2110467099 / 1000000000000 : ℝ)
  frameLo := (628183554393 / 1000000000000 : ℝ)
  frameHi := (46364956397 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12518]
  agentFrame_pos := by norm_num only [agent12518]
  worldRadius := (2110467099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12518]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (341810673 / 200000000000 : ℝ)
  lowerTail := (1998052761 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (88855473 / 10000000000 : ℝ)
  ledger := by
    have h : (1180165189 / 1000000000000 : ℚ) +
        (9795081943 / 1000000000000000000 : ℚ) / (2110467099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (341810673 / 200000000000 : ℚ) + (1998052761 / 1000000000000 : ℚ) ≤
        (88855473 / 10000000000 : ℚ) := by norm_num only
    have hc : (((1180165189 / 1000000000000 : ℚ) +
        (9795081943 / 1000000000000000000 : ℚ) / (2110467099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (341810673 / 200000000000 : ℚ) + (1998052761 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((88855473 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12518]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12518 :
    2 * 160 < 12518 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998727 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12518 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12519 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12519. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12519 : WorldParameters where
  hiddenCharge := (1180119419 / 1000000000000 : ℝ)
  frame := (314084649197 / 500000000000 : ℝ)
  moment := (4896518049 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12519 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483644273509 / 1000000000000 : ℝ)
    root := (8622102543 / 1000000000000 : ℝ) }

noncomputable def scalar12519 : ScalarCertificate 12519 world12519 agent12519 where
  dimensionLo := 12519
  dimensionHi := 12519
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2110819499 / 1000000000000 : ℝ)
  frameLo := (314084649197 / 500000000000 : ℝ)
  frameHi := (1483644273509 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12519]
  agentFrame_pos := by norm_num only [agent12519]
  worldRadius := (2110819499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12519]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1707579221 / 1000000000000 : ℝ)
  lowerTail := (1996451339 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8881232571 / 1000000000000 : ℝ)
  ledger := by
    have h : (1180119419 / 1000000000000 : ℚ) +
        (4896518049 / 500000000000000000 : ℚ) / (2110819499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1707579221 / 1000000000000 : ℚ) + (1996451339 / 1000000000000 : ℚ) ≤
        (8881232571 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1180119419 / 1000000000000 : ℚ) +
        (4896518049 / 500000000000000000 : ℚ) / (2110819499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1707579221 / 1000000000000 : ℚ) + (1996451339 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8881232571 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12519]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12519 :
    2 * 160 < 12519 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998903 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12519 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12520 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12520. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12520 : WorldParameters where
  hiddenCharge := (590036831 / 500000000000 : ℝ)
  frame := (628155044721 / 1000000000000 : ℝ)
  moment := (9790990849 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12520 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483526456953 / 1000000000000 : ℝ)
    root := (862138819 / 100000000000 : ℝ) }

noncomputable def scalar12520 : ScalarCertificate 12520 world12520 agent12520 where
  dimensionLo := 12520
  dimensionHi := 12520
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2111281599 / 1000000000000 : ℝ)
  frameLo := (628155044721 / 1000000000000 : ℝ)
  frameHi := (1483526456953 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12520]
  agentFrame_pos := by norm_num only [agent12520]
  worldRadius := (2111281599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12520]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (341158923 / 200000000000 : ℝ)
  lowerTail := (398890917 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1775196919 / 200000000000 : ℝ)
  ledger := by
    have h : (590036831 / 500000000000 : ℚ) +
        (9790990849 / 1000000000000000000 : ℚ) / (2111281599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (341158923 / 200000000000 : ℚ) + (398890917 / 200000000000 : ℚ) ≤
        (1775196919 / 200000000000 : ℚ) := by norm_num only
    have hc : (((590036831 / 500000000000 : ℚ) +
        (9790990849 / 1000000000000000000 : ℚ) / (2111281599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (341158923 / 200000000000 : ℚ) + (398890917 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1775196919 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12520]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12520 :
    2 * 160 < 12520 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999863 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12520 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12521 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12521. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12521 : WorldParameters where
  hiddenCharge := (1180027917 / 1000000000000 : ℝ)
  frame := (19629399793 / 31250000000 : ℝ)
  moment := (4894473099 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12521 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483492164941 / 1000000000000 : ℝ)
    root := (8620673991 / 1000000000000 : ℝ) }

noncomputable def scalar12521 : ScalarCertificate 12521 world12521 agent12521 where
  dimensionLo := 12521
  dimensionHi := 12521
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2111633999 / 1000000000000 : ℝ)
  frameLo := (19629399793 / 31250000000 : ℝ)
  frameHi := (1483492164941 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12521]
  agentFrame_pos := by norm_num only [agent12521]
  worldRadius := (2111633999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12521]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1704323633 / 1000000000000 : ℝ)
  lowerTail := (1992856437 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1108959763 / 125000000000 : ℝ)
  ledger := by
    have h : (1180027917 / 1000000000000 : ℚ) +
        (4894473099 / 500000000000000000 : ℚ) / (2111633999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1704323633 / 1000000000000 : ℚ) + (1992856437 / 1000000000000 : ℚ) ≤
        (1108959763 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1180027917 / 1000000000000 : ℚ) +
        (4894473099 / 500000000000000000 : ℚ) / (2111633999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1704323633 / 1000000000000 : ℚ) + (1992856437 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1108959763 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12521]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12521 :
    2 * 160 < 12521 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995517 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12521 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12522 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12522. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12522 : WorldParameters where
  hiddenCharge := (147497773 / 125000000000 : ℝ)
  frame := (628126544357 / 1000000000000 : ℝ)
  moment := (9786902143 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12522 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483457889017 / 1000000000000 : ℝ)
    root := (538747501 / 62500000000 : ℝ) }

noncomputable def scalar12522 : ScalarCertificate 12522 world12522 agent12522 where
  dimensionLo := 12522
  dimensionHi := 12522
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2111986399 / 1000000000000 : ℝ)
  frameLo := (628126544357 / 1000000000000 : ℝ)
  frameHi := (1483457889017 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12522]
  agentFrame_pos := by norm_num only [agent12522]
  worldRadius := (2111986399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12522]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (212856763 / 125000000000 : ℝ)
  lowerTail := (15556717 / 7812500000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8867375373 / 1000000000000 : ℝ)
  ledger := by
    have h : (147497773 / 125000000000 : ℚ) +
        (9786902143 / 1000000000000000000 : ℚ) / (2111986399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (212856763 / 125000000000 : ℚ) + (15556717 / 7812500000 : ℚ) ≤
        (8867375373 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((147497773 / 125000000000 : ℚ) +
        (9786902143 / 1000000000000000000 : ℚ) / (2111986399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (212856763 / 125000000000 : ℚ) + (15556717 / 7812500000 : ℚ) : ℚ) : ℝ) ≤
        ((8867375373 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12522]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12522 :
    2 * 160 < 12522 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999849 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12522 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12523 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12523. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12523 : WorldParameters where
  hiddenCharge := (1179936463 / 1000000000000 : ℝ)
  frame := (628112297663 / 1000000000000 : ℝ)
  moment := (2446214671 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12523 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483423635127 / 1000000000000 : ℝ)
    root := (8619246263 / 1000000000000 : ℝ) }

noncomputable def scalar12523 : ScalarCertificate 12523 world12523 agent12523 where
  dimensionLo := 12523
  dimensionHi := 12523
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2112338699 / 1000000000000 : ℝ)
  frameLo := (628112297663 / 1000000000000 : ℝ)
  frameHi := (1483423635127 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12523]
  agentFrame_pos := by norm_num only [agent12523]
  worldRadius := (2112338699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12523]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (425346489 / 250000000000 : ℝ)
  lowerTail := (124354033 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8863076461 / 1000000000000 : ℝ)
  ledger := by
    have h : (1179936463 / 1000000000000 : ℚ) +
        (2446214671 / 250000000000000000 : ℚ) / (2112338699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (425346489 / 250000000000 : ℚ) + (124354033 / 62500000000 : ℚ) ≤
        (8863076461 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1179936463 / 1000000000000 : ℚ) +
        (2446214671 / 250000000000000000 : ℚ) / (2112338699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (425346489 / 250000000000 : ℚ) + (124354033 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((8863076461 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12523]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12523 :
    2 * 160 < 12523 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999391 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12523 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12524 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12524. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12524 : WorldParameters where
  hiddenCharge := (235978151 / 200000000000 : ℝ)
  frame := (314049026647 / 500000000000 : ℝ)
  moment := (4891407911 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12524 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483389403259 / 1000000000000 : ℝ)
    root := (1723706547 / 200000000000 : ℝ) }

noncomputable def scalar12524 : ScalarCertificate 12524 world12524 agent12524 where
  dimensionLo := 12524
  dimensionHi := 12524
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2112691099 / 1000000000000 : ℝ)
  frameLo := (314049026647 / 500000000000 : ℝ)
  frameHi := (1483389403259 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12524]
  agentFrame_pos := by norm_num only [agent12524]
  worldRadius := (2112691099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12524]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (424979847 / 250000000000 : ℝ)
  lowerTail := (1988070907 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8858781367 / 1000000000000 : ℝ)
  ledger := by
    have h : (235978151 / 200000000000 : ℚ) +
        (4891407911 / 500000000000000000 : ℚ) / (2112691099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (424979847 / 250000000000 : ℚ) + (1988070907 / 1000000000000 : ℚ) ≤
        (8858781367 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((235978151 / 200000000000 : ℚ) +
        (4891407911 / 500000000000000000 : ℚ) / (2112691099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (424979847 / 250000000000 : ℚ) + (1988070907 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8858781367 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12524]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12524 :
    2 * 160 < 12524 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998191 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12524 {← IO.monoMsNow}" : IO Unit)
