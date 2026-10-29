import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12925 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12925. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12925 : WorldParameters where
  hiddenCharge := (1162506689 / 1000000000000 : ℝ)
  frame := (622567133777 / 1000000000000 : ℝ)
  moment := (4504682673 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12925 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467338690497 / 1000000000000 : ℝ)
    root := (8347059343 / 1000000000000 : ℝ) }

noncomputable def scalar12925 : ScalarCertificate 12925 world12925 agent12925 where
  dimensionLo := 12925
  dimensionHi := 12925
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2260480999 / 1000000000000 : ℝ)
  frameLo := (622567133777 / 1000000000000 : ℝ)
  frameHi := (1467338690497 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12925]
  agentFrame_pos := by norm_num only [agent12925]
  worldRadius := (2260480999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12925]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (240583679 / 200000000000 : ℝ)
  lowerTail := (288060017 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3684017109 / 500000000000 : ℝ)
  ledger := by
    have h : (1162506689 / 1000000000000 : ℚ) +
        (4504682673 / 500000000000000000 : ℚ) / (2260480999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240583679 / 200000000000 : ℚ) + (288060017 / 200000000000 : ℚ) ≤
        (3684017109 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1162506689 / 1000000000000 : ℚ) +
        (4504682673 / 500000000000000000 : ℚ) / (2260480999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240583679 / 200000000000 : ℚ) + (288060017 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3684017109 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12925]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12925 :
    2 * 160 < 12925 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (3124999 / 312500000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12925 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12926 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12926. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12926 : WorldParameters where
  hiddenCharge := (1162465587 / 1000000000000 : ℝ)
  frame := (622553777279 / 1000000000000 : ℝ)
  moment := (9007545093 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12926 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91706785947 / 62500000000 : ℝ)
    root := (208660533 / 25000000000 : ℝ) }

noncomputable def scalar12926 : ScalarCertificate 12926 world12926 agent12926 where
  dimensionLo := 12926
  dimensionHi := 12926
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2260842299 / 1000000000000 : ℝ)
  frameLo := (622553777279 / 1000000000000 : ℝ)
  frameHi := (91706785947 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12926]
  agentFrame_pos := by norm_num only [agent12926]
  worldRadius := (2260842299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12926]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1201925681 / 1000000000000 : ℝ)
  lowerTail := (71959821 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1841244283 / 250000000000 : ℝ)
  ledger := by
    have h : (1162465587 / 1000000000000 : ℚ) +
        (9007545093 / 1000000000000000000 : ℚ) / (2260842299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1201925681 / 1000000000000 : ℚ) + (71959821 / 50000000000 : ℚ) ≤
        (1841244283 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1162465587 / 1000000000000 : ℚ) +
        (9007545093 / 1000000000000000000 : ℚ) / (2260842299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1201925681 / 1000000000000 : ℚ) + (71959821 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1841244283 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12926]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12926 :
    2 * 160 < 12926 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997231 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12926 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12927 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12927. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12927 : WorldParameters where
  hiddenCharge := (72651531 / 62500000000 : ℝ)
  frame := (311270211439 / 500000000000 : ℝ)
  moment := (1801145071 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12927 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467278472279 / 1000000000000 : ℝ)
    root := (4172891773 / 500000000000 : ℝ) }

noncomputable def scalar12927 : ScalarCertificate 12927 world12927 agent12927 where
  dimensionLo := 12927
  dimensionHi := 12927
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2261203499 / 1000000000000 : ℝ)
  frameLo := (311270211439 / 500000000000 : ℝ)
  frameHi := (1467278472279 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12927]
  agentFrame_pos := by norm_num only [agent12927]
  worldRadius := (2261203499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12927]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (9607471 / 8000000000 : ℝ)
  lowerTail := (719046849 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7361922663 / 1000000000000 : ℝ)
  ledger := by
    have h : (72651531 / 62500000000 : ℚ) +
        (1801145071 / 200000000000000000 : ℚ) / (2261203499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (9607471 / 8000000000 : ℚ) + (719046849 / 500000000000 : ℚ) ≤
        (7361922663 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((72651531 / 62500000000 : ℚ) +
        (1801145071 / 200000000000000000 : ℚ) / (2261203499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (9607471 / 8000000000 : ℚ) + (719046849 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7361922663 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12927]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12927 :
    2 * 160 < 12927 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999541 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12927 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12928 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12928. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12928 : WorldParameters where
  hiddenCharge := (232476683 / 200000000000 : ℝ)
  frame := (24901082823 / 40000000000 : ℝ)
  moment := (900390613 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12928 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1467248381869 / 1000000000000 : ℝ)
    root := (8345145891 / 1000000000000 : ℝ) }

noncomputable def scalar12928 : ScalarCertificate 12928 world12928 agent12928 where
  dimensionLo := 12928
  dimensionHi := 12928
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2261564899 / 1000000000000 : ℝ)
  frameLo := (24901082823 / 40000000000 : ℝ)
  frameHi := (1467248381869 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12928]
  agentFrame_pos := by norm_num only [agent12928]
  worldRadius := (2261564899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12928]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (18749111 / 15625000000 : ℝ)
  lowerTail := (1436992069 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7358870617 / 1000000000000 : ℝ)
  ledger := by
    have h : (232476683 / 200000000000 : ℚ) +
        (900390613 / 100000000000000000 : ℚ) / (2261564899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (18749111 / 15625000000 : ℚ) + (1436992069 / 1000000000000 : ℚ) ≤
        (7358870617 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((232476683 / 200000000000 : ℚ) +
        (900390613 / 100000000000000000 : ℚ) / (2261564899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (18749111 / 15625000000 : ℚ) + (1436992069 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7358870617 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12928]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12928 :
    2 * 160 < 12928 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999627 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12928 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12929 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12929. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12929 : WorldParameters where
  hiddenCharge := (232468469 / 200000000000 : ℝ)
  frame := (38907107523 / 62500000000 : ℝ)
  moment := (9002087419 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12929 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733609157831 / 500000000000 : ℝ)
    root := (1668901697 / 200000000000 : ℝ) }

noncomputable def scalar12929 : ScalarCertificate 12929 world12929 agent12929 where
  dimensionLo := 12929
  dimensionHi := 12929
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2261926199 / 1000000000000 : ℝ)
  frameLo := (38907107523 / 62500000000 : ℝ)
  frameHi := (733609157831 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12929]
  agentFrame_pos := by norm_num only [agent12929]
  worldRadius := (2261926199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12929]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1198953283 / 1000000000000 : ℝ)
  lowerTail := (1435891437 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3677910641 / 500000000000 : ℝ)
  ledger := by
    have h : (232468469 / 200000000000 : ℚ) +
        (9002087419 / 1000000000000000000 : ℚ) / (2261926199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1198953283 / 1000000000000 : ℚ) + (1435891437 / 1000000000000 : ℚ) ≤
        (3677910641 / 500000000000 : ℚ) := by norm_num only
    have hc : (((232468469 / 200000000000 : ℚ) +
        (9002087419 / 1000000000000000000 : ℚ) / (2261926199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1198953283 / 1000000000000 : ℚ) + (1435891437 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3677910641 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12929]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12929 :
    2 * 160 < 12929 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999177 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12929 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12930 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12930. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12930 : WorldParameters where
  hiddenCharge := (232460257 / 200000000000 : ℝ)
  frame := (622500372257 / 1000000000000 : ℝ)
  moment := (9000269221 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12930 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733554752609 / 500000000000 : ℝ)
    root := (8343871197 / 1000000000000 : ℝ) }

noncomputable def scalar12930 : ScalarCertificate 12930 world12930 agent12930 where
  dimensionLo := 12930
  dimensionHi := 12930
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2262402999 / 1000000000000 : ℝ)
  frameLo := (622500372257 / 1000000000000 : ℝ)
  frameHi := (733554752609 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12930]
  agentFrame_pos := by norm_num only [agent12930]
  worldRadius := (2262402999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12930]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1197751611 / 1000000000000 : ℝ)
  lowerTail := (1434513759 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (919013013 / 125000000000 : ℝ)
  ledger := by
    have h : (232460257 / 200000000000 : ℚ) +
        (9000269221 / 1000000000000000000 : ℚ) / (2262402999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1197751611 / 1000000000000 : ℚ) + (1434513759 / 1000000000000 : ℚ) ≤
        (919013013 / 125000000000 : ℚ) := by norm_num only
    have hc : (((232460257 / 200000000000 : ℚ) +
        (9000269221 / 1000000000000000000 : ℚ) / (2262402999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1197751611 / 1000000000000 : ℚ) + (1434513759 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((919013013 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12930]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12930 :
    2 * 160 < 12930 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997683 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12930 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12931 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12931. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12931 : WorldParameters where
  hiddenCharge := (1162260237 / 1000000000000 : ℝ)
  frame := (311243513121 / 500000000000 : ℝ)
  moment := (562403221 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12931 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293415892961 / 200000000000 : ℝ)
    root := (4171617079 / 500000000000 : ℝ) }

noncomputable def scalar12931 : ScalarCertificate 12931 world12931 agent12931 where
  dimensionLo := 12931
  dimensionHi := 12931
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2262764299 / 1000000000000 : ℝ)
  frameLo := (311243513121 / 500000000000 : ℝ)
  frameHi := (293415892961 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12931]
  agentFrame_pos := by norm_num only [agent12931]
  worldRadius := (2262764299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12931]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (598381899 / 500000000000 : ℝ)
  lowerTail := (5733661 / 4000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3674530119 / 500000000000 : ℝ)
  ledger := by
    have h : (1162260237 / 1000000000000 : ℚ) +
        (562403221 / 62500000000000000 : ℚ) / (2262764299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (598381899 / 500000000000 : ℚ) + (5733661 / 4000000000 : ℚ) ≤
        (3674530119 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1162260237 / 1000000000000 : ℚ) +
        (562403221 / 62500000000000000 : ℚ) / (2262764299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (598381899 / 500000000000 : ℚ) + (5733661 / 4000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3674530119 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12931]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12931 :
    2 * 160 < 12931 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998051 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12931 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12932 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12932. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12932 : WorldParameters where
  hiddenCharge := (1162219199 / 1000000000000 : ℝ)
  frame := (622473682321 / 1000000000000 : ℝ)
  moment := (2249158591 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12932 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733524721349 / 500000000000 : ℝ)
    root := (8342597237 / 1000000000000 : ℝ) }

noncomputable def scalar12932 : ScalarCertificate 12932 world12932 agent12932 where
  dimensionLo := 12932
  dimensionHi := 12932
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2263125599 / 1000000000000 : ℝ)
  frameLo := (622473682321 / 1000000000000 : ℝ)
  frameHi := (733524721349 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12932]
  agentFrame_pos := by norm_num only [agent12932]
  worldRadius := (2263125599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12932]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (119577689 / 100000000000 : ℝ)
  lowerTail := (716158847 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1469203767 / 200000000000 : ℝ)
  ledger := by
    have h : (1162219199 / 1000000000000 : ℚ) +
        (2249158591 / 250000000000000000 : ℚ) / (2263125599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119577689 / 100000000000 : ℚ) + (716158847 / 500000000000 : ℚ) ≤
        (1469203767 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1162219199 / 1000000000000 : ℚ) +
        (2249158591 / 250000000000000000 : ℚ) / (2263125599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119577689 / 100000000000 : ℚ) + (716158847 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1469203767 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12932]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12932 :
    2 * 160 < 12932 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999789 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12932 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12933 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12933. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12933 : WorldParameters where
  hiddenCharge := (1162178171 / 1000000000000 : ℝ)
  frame := (124492068099 / 200000000000 : ℝ)
  moment := (1798963541 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12933 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146701943889 / 100000000000 : ℝ)
    root := (16683921 / 2000000000 : ℝ) }

noncomputable def scalar12933 : ScalarCertificate 12933 world12933 agent12933 where
  dimensionLo := 12933
  dimensionHi := 12933
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2263487099 / 1000000000000 : ℝ)
  frameLo := (124492068099 / 200000000000 : ℝ)
  frameHi := (146701943889 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12933]
  agentFrame_pos := by norm_num only [agent12933]
  worldRadius := (2263487099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12933]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1194791079 / 1000000000000 : ℝ)
  lowerTail := (14312213 / 10000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7342979989 / 1000000000000 : ℝ)
  ledger := by
    have h : (1162178171 / 1000000000000 : ℚ) +
        (1798963541 / 200000000000000000 : ℚ) / (2263487099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1194791079 / 1000000000000 : ℚ) + (14312213 / 10000000000 : ℚ) ≤
        (7342979989 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1162178171 / 1000000000000 : ℚ) +
        (1798963541 / 200000000000000000 : ℚ) / (2263487099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1194791079 / 1000000000000 : ℚ) + (14312213 / 10000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7342979989 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12933]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12933 :
    2 * 160 < 12933 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999031 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12933 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12934 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12934. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12934 : WorldParameters where
  hiddenCharge := (581068577 / 500000000000 : ℝ)
  frame := (622447000763 / 1000000000000 : ℝ)
  moment := (4496500779 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12934 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733494723751 / 500000000000 : ℝ)
    root := (834132401 / 100000000000 : ℝ) }

noncomputable def scalar12934 : ScalarCertificate 12934 world12934 agent12934 where
  dimensionLo := 12934
  dimensionHi := 12934
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2263848399 / 1000000000000 : ℝ)
  frameLo := (622447000763 / 1000000000000 : ℝ)
  frameHi := (733494723751 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12934]
  agentFrame_pos := by norm_num only [agent12934]
  worldRadius := (2263848399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12934]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (74612881 / 62500000000 : ℝ)
  lowerTail := (4469143 / 3125000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3669971869 / 500000000000 : ℝ)
  ledger := by
    have h : (581068577 / 500000000000 : ℚ) +
        (4496500779 / 500000000000000000 : ℚ) / (2263848399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74612881 / 62500000000 : ℚ) + (4469143 / 3125000000 : ℚ) ≤
        (3669971869 / 500000000000 : ℚ) := by norm_num only
    have hc : (((581068577 / 500000000000 : ℚ) +
        (4496500779 / 500000000000000000 : ℚ) / (2263848399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74612881 / 62500000000 : ℚ) + (4469143 / 3125000000 : ℚ) : ℚ) : ℝ) ≤
        ((3669971869 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12934]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12934 :
    2 * 160 < 12934 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997077 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12934 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12935 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12935. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12935 : WorldParameters where
  hiddenCharge := (290524037 / 250000000000 : ℝ)
  frame := (995893861 / 1600000000 : ℝ)
  moment := (2247796481 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12935 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466959474397 / 1000000000000 : ℝ)
    root := (8340687639 / 1000000000000 : ℝ) }

noncomputable def scalar12935 : ScalarCertificate 12935 world12935 agent12935 where
  dimensionLo := 12935
  dimensionHi := 12935
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2264209799 / 1000000000000 : ℝ)
  frameLo := (995893861 / 1600000000 : ℝ)
  frameHi := (1466959474397 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12935]
  agentFrame_pos := by norm_num only [agent12935]
  worldRadius := (2264209799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12935]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (149102761 / 125000000000 : ℝ)
  lowerTail := (357257813 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3668454973 / 500000000000 : ℝ)
  ledger := by
    have h : (290524037 / 250000000000 : ℚ) +
        (2247796481 / 250000000000000000 : ℚ) / (2264209799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (149102761 / 125000000000 : ℚ) + (357257813 / 250000000000 : ℚ) ≤
        (3668454973 / 500000000000 : ℚ) := by norm_num only
    have hc : (((290524037 / 250000000000 : ℚ) +
        (2247796481 / 250000000000000000 : ℚ) / (2264209799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (149102761 / 125000000000 : ℚ) + (357257813 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3668454973 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12935]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12935 :
    2 * 160 < 12935 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995537 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12935 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12936 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12936. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12936 : WorldParameters where
  hiddenCharge := (1162055153 / 1000000000000 : ℝ)
  frame := (622420327579 / 1000000000000 : ℝ)
  moment := (4494685401 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12936 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733464756849 / 500000000000 : ℝ)
    root := (1668010303 / 200000000000 : ℝ) }

noncomputable def scalar12936 : ScalarCertificate 12936 world12936 agent12936 where
  dimensionLo := 12936
  dimensionHi := 12936
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2264571099 / 1000000000000 : ℝ)
  frameLo := (622420327579 / 1000000000000 : ℝ)
  frameHi := (733464756849 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12936]
  agentFrame_pos := by norm_num only [agent12936]
  worldRadius := (2264571099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12936]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (595919489 / 500000000000 : ℝ)
  lowerTail := (1427937677 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (916734843 / 125000000000 : ℝ)
  ledger := by
    have h : (1162055153 / 1000000000000 : ℚ) +
        (4494685401 / 500000000000000000 : ℚ) / (2264571099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (595919489 / 500000000000 : ℚ) + (1427937677 / 1000000000000 : ℚ) ≤
        (916734843 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1162055153 / 1000000000000 : ℚ) +
        (4494685401 / 500000000000000000 : ℚ) / (2264571099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (595919489 / 500000000000 : ℚ) + (1427937677 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((916734843 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12936]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12936 :
    2 * 160 < 12936 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999637 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12936 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12937 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12937. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12937 : WorldParameters where
  hiddenCharge := (145251771 / 125000000000 : ℝ)
  frame := (4979255953 / 8000000000 : ℝ)
  moment := (280861131 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12937 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466899571267 / 1000000000000 : ℝ)
    root := (833941551 / 100000000000 : ℝ) }

noncomputable def scalar12937 : ScalarCertificate 12937 world12937 agent12937 where
  dimensionLo := 12937
  dimensionHi := 12937
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2264932499 / 1000000000000 : ℝ)
  frameLo := (4979255953 / 8000000000 : ℝ)
  frameHi := (1466899571267 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12937]
  agentFrame_pos := by norm_num only [agent12937]
  worldRadius := (2264932499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12937]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (595428421 / 500000000000 : ℝ)
  lowerTail := (356711283 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3665424997 / 500000000000 : ℝ)
  ledger := by
    have h : (145251771 / 125000000000 : ℚ) +
        (280861131 / 31250000000000000 : ℚ) / (2264932499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (595428421 / 500000000000 : ℚ) + (356711283 / 250000000000 : ℚ) ≤
        (3665424997 / 500000000000 : ℚ) := by norm_num only
    have hc : (((145251771 / 125000000000 : ℚ) +
        (280861131 / 31250000000000000 : ℚ) / (2264932499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (595428421 / 500000000000 : ℚ) + (356711283 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3665424997 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12937]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12937 :
    2 * 160 < 12937 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998059 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12937 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12938 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12938. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12938 : WorldParameters where
  hiddenCharge := (580986597 / 500000000000 : ℝ)
  frame := (155598415691 / 250000000000 : ℝ)
  moment := (4492871047 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12938 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466869641227 / 1000000000000 : ℝ)
    root := (1042347461 / 125000000000 : ℝ) }

noncomputable def scalar12938 : ScalarCertificate 12938 world12938 agent12938 where
  dimensionLo := 12938
  dimensionHi := 12938
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2265293899 / 1000000000000 : ℝ)
  frameLo := (155598415691 / 250000000000 : ℝ)
  frameHi := (1466869641227 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12938]
  agentFrame_pos := by norm_num only [agent12938]
  worldRadius := (2265293899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12938]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (118987563 / 100000000000 : ℝ)
  lowerTail := (89109597 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7327823737 / 1000000000000 : ℝ)
  ledger := by
    have h : (580986597 / 500000000000 : ℚ) +
        (4492871047 / 500000000000000000 : ℚ) / (2265293899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (118987563 / 100000000000 : ℚ) + (89109597 / 62500000000 : ℚ) ≤
        (7327823737 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((580986597 / 500000000000 : ℚ) +
        (4492871047 / 500000000000000000 : ℚ) / (2265293899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (118987563 / 100000000000 : ℚ) + (89109597 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7327823737 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12938]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12938 :
    2 * 160 < 12938 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998199 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12938 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12939 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12939. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12939 : WorldParameters where
  hiddenCharge := (116193223 / 100000000000 : ℝ)
  frame := (622380333493 / 1000000000000 : ℝ)
  moment := (2245982127 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12939 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733419864721 / 500000000000 : ℝ)
    root := (521134007 / 62500000000 : ℝ) }

noncomputable def scalar12939 : ScalarCertificate 12939 world12939 agent12939 where
  dimensionLo := 12939
  dimensionHi := 12939
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2265655299 / 1000000000000 : ℝ)
  frameLo := (622380333493 / 1000000000000 : ℝ)
  frameHi := (733419864721 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12939]
  agentFrame_pos := by norm_num only [agent12939]
  worldRadius := (2265655299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12939]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (74305963 / 62500000000 : ℝ)
  lowerTail := (1424663013 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3662400057 / 500000000000 : ℝ)
  ledger := by
    have h : (116193223 / 100000000000 : ℚ) +
        (2245982127 / 250000000000000000 : ℚ) / (2265655299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74305963 / 62500000000 : ℚ) + (1424663013 / 1000000000000 : ℚ) ≤
        (3662400057 / 500000000000 : ℚ) := by norm_num only
    have hc : (((116193223 / 100000000000 : ℚ) +
        (2245982127 / 250000000000000000 : ℚ) / (2265655299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74305963 / 62500000000 : ℚ) + (1424663013 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3662400057 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12939]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12939 :
    2 * 160 < 12939 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998849 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12939 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12940 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12940. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12940 : WorldParameters where
  hiddenCharge := (1161891277 / 1000000000000 : ℝ)
  frame := (311183503157 / 500000000000 : ℝ)
  moment := (8982115433 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12940 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733365595401 / 500000000000 : ℝ)
    root := (4168754327 / 500000000000 : ℝ) }

noncomputable def scalar12940 : ScalarCertificate 12940 world12940 agent12940 where
  dimensionLo := 12940
  dimensionHi := 12940
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2266132299 / 1000000000000 : ℝ)
  frameLo := (311183503157 / 500000000000 : ℝ)
  frameHi := (733365595401 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12940]
  agentFrame_pos := by norm_num only [agent12940]
  worldRadius := (2266132299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12940]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (593852639 / 500000000000 : ℝ)
  lowerTail := (711648897 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3660557023 / 500000000000 : ℝ)
  ledger := by
    have h : (1161891277 / 1000000000000 : ℚ) +
        (8982115433 / 1000000000000000000 : ℚ) / (2266132299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (593852639 / 500000000000 : ℚ) + (711648897 / 500000000000 : ℚ) ≤
        (3660557023 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1161891277 / 1000000000000 : ℚ) +
        (8982115433 / 1000000000000000000 : ℚ) / (2266132299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (593852639 / 500000000000 : ℚ) + (711648897 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3660557023 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12940]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12940 :
    2 * 160 < 12940 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994591 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12940 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12941 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12941. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12941 : WorldParameters where
  hiddenCharge := (232370067 / 200000000000 : ℝ)
  frame := (77794210153 / 125000000000 : ℝ)
  moment := (8980302869 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12941 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466701310529 / 1000000000000 : ℝ)
    root := (8336873443 / 1000000000000 : ℝ) }

noncomputable def scalar12941 : ScalarCertificate 12941 world12941 agent12941 where
  dimensionLo := 12941
  dimensionHi := 12941
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2266493699 / 1000000000000 : ℝ)
  frameLo := (77794210153 / 125000000000 : ℝ)
  frameHi := (1466701310529 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12941]
  agentFrame_pos := by norm_num only [agent12941]
  worldRadius := (2266493699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12941]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1186727063 / 1000000000000 : ℝ)
  lowerTail := (1422209383 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7318095887 / 1000000000000 : ℝ)
  ledger := by
    have h : (232370067 / 200000000000 : ℚ) +
        (8980302869 / 1000000000000000000 : ℚ) / (2266493699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1186727063 / 1000000000000 : ℚ) + (1422209383 / 1000000000000 : ℚ) ≤
        (7318095887 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((232370067 / 200000000000 : ℚ) +
        (8980302869 / 1000000000000000000 : ℚ) / (2266493699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1186727063 / 1000000000000 : ℚ) + (1422209383 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7318095887 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12941]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12941 :
    2 * 160 < 12941 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (124999931 / 12500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12941 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12942 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12942. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12942 : WorldParameters where
  hiddenCharge := (1161809403 / 1000000000000 : ℝ)
  frame := (38896272389 / 62500000000 : ℝ)
  moment := (140288919 / 15625000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12942 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466671442617 / 1000000000000 : ℝ)
    root := (166724767 / 20000000000 : ℝ) }

noncomputable def scalar12942 : ScalarCertificate 12942 world12942 agent12942 where
  dimensionLo := 12942
  dimensionHi := 12942
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2266855099 / 1000000000000 : ℝ)
  frameLo := (38896272389 / 62500000000 : ℝ)
  frameHi := (1466671442617 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12942]
  agentFrame_pos := by norm_num only [agent12942]
  worldRadius := (2266855099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12942]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (592874861 / 500000000000 : ℝ)
  lowerTail := (1421121887 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7315080117 / 1000000000000 : ℝ)
  ledger := by
    have h : (1161809403 / 1000000000000 : ℚ) +
        (140288919 / 15625000000000000 : ℚ) / (2266855099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (592874861 / 500000000000 : ℚ) + (1421121887 / 1000000000000 : ℚ) ≤
        (7315080117 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1161809403 / 1000000000000 : ℚ) +
        (140288919 / 15625000000000000 : ℚ) / (2266855099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (592874861 / 500000000000 : ℚ) + (1421121887 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7315080117 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12942]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12942 :
    2 * 160 < 12942 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997347 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12942 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12943 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12943. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12943 : WorldParameters where
  hiddenCharge := (580884241 / 500000000000 : ℝ)
  frame := (311163518657 / 500000000000 : ℝ)
  moment := (359067171 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12943 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466641592929 / 1000000000000 : ℝ)
    root := (104195043 / 12500000000 : ℝ) }

noncomputable def scalar12943 : ScalarCertificate 12943 world12943 agent12943 where
  dimensionLo := 12943
  dimensionHi := 12943
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2267216499 / 1000000000000 : ℝ)
  frameLo := (311163518657 / 500000000000 : ℝ)
  frameHi := (1466641592929 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12943]
  agentFrame_pos := by norm_num only [agent12943]
  worldRadius := (2267216499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12943]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1184773321 / 1000000000000 : ℝ)
  lowerTail := (71001769 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3656033439 / 500000000000 : ℝ)
  ledger := by
    have h : (580884241 / 500000000000 : ℚ) +
        (359067171 / 40000000000000000 : ℚ) / (2267216499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1184773321 / 1000000000000 : ℚ) + (71001769 / 50000000000 : ℚ) ≤
        (3656033439 / 500000000000 : ℚ) := by norm_num only
    have hc : (((580884241 / 500000000000 : ℚ) +
        (359067171 / 40000000000000000 : ℚ) / (2267216499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1184773321 / 1000000000000 : ℚ) + (71001769 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3656033439 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12943]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12943 :
    2 * 160 < 12943 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999693 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12943 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12944 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12944. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12944 : WorldParameters where
  hiddenCharge := (290431893 / 250000000000 : ℝ)
  frame := (155578429623 / 250000000000 : ℝ)
  moment := (2243717061 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12944 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733305880729 / 500000000000 : ℝ)
    root := (333398751 / 40000000000 : ℝ) }

noncomputable def scalar12944 : ScalarCertificate 12944 world12944 agent12944 where
  dimensionLo := 12944
  dimensionHi := 12944
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2267577999 / 1000000000000 : ℝ)
  frameLo := (155578429623 / 250000000000 : ℝ)
  frameHi := (733305880729 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12944]
  agentFrame_pos := by norm_num only [agent12944]
  worldRadius := (2267577999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12944]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (591898989 / 500000000000 : ℝ)
  lowerTail := (354737497 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3654528129 / 500000000000 : ℝ)
  ledger := by
    have h : (290431893 / 250000000000 : ℚ) +
        (2243717061 / 250000000000000000 : ℚ) / (2267577999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (591898989 / 500000000000 : ℚ) + (354737497 / 250000000000 : ℚ) ≤
        (3654528129 / 500000000000 : ℚ) := by norm_num only
    have hc : (((290431893 / 250000000000 : ℚ) +
        (2243717061 / 250000000000000000 : ℚ) / (2267577999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (591898989 / 500000000000 : ℚ) + (354737497 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3654528129 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12944]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12944 :
    2 * 160 < 12944 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999381 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12944 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12945 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12945. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12945 : WorldParameters where
  hiddenCharge := (72605417 / 62500000000 : ℝ)
  frame := (311150200879 / 500000000000 : ℝ)
  moment := (8973057723 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12945 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466581942327 / 1000000000000 : ℝ)
    root := (2083583557 / 250000000000 : ℝ) }

noncomputable def scalar12945 : ScalarCertificate 12945 world12945 agent12945 where
  dimensionLo := 12945
  dimensionHi := 12945
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2267939499 / 1000000000000 : ℝ)
  frameLo := (311150200879 / 500000000000 : ℝ)
  frameHi := (1466581942327 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12945]
  agentFrame_pos := by norm_num only [agent12945]
  worldRadius := (2267939499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12945]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (236564701 / 200000000000 : ℝ)
  lowerTail := (354466377 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7306048023 / 1000000000000 : ℝ)
  ledger := by
    have h : (72605417 / 62500000000 : ℚ) +
        (8973057723 / 1000000000000000000 : ℚ) / (2267939499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236564701 / 200000000000 : ℚ) + (354466377 / 250000000000 : ℚ) ≤
        (7306048023 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((72605417 / 62500000000 : ℚ) +
        (8973057723 / 1000000000000000000 : ℚ) / (2267939499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236564701 / 200000000000 : ℚ) + (354466377 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7306048023 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12945]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12945 :
    2 * 160 < 12945 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499998867 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12945 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12946 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12946. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12946 : WorldParameters where
  hiddenCharge := (1161645783 / 1000000000000 : ℝ)
  frame := (77785885889 / 125000000000 : ℝ)
  moment := (8971247713 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12946 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466552135529 / 1000000000000 : ℝ)
    root := (8333699863 / 1000000000000 : ℝ) }

noncomputable def scalar12946 : ScalarCertificate 12946 world12946 agent12946 where
  dimensionLo := 12946
  dimensionHi := 12946
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2268300899 / 1000000000000 : ℝ)
  frameLo := (77785885889 / 125000000000 : ℝ)
  frameHi := (1466552135529 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12946]
  agentFrame_pos := by norm_num only [agent12946]
  worldRadius := (2268300899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12946]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (9454799 / 8000000000 : ℝ)
  lowerTail := (88548869 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7303042259 / 1000000000000 : ℝ)
  ledger := by
    have h : (1161645783 / 1000000000000 : ℚ) +
        (8971247713 / 1000000000000000000 : ℚ) / (2268300899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (9454799 / 8000000000 : ℚ) + (88548869 / 62500000000 : ℚ) ≤
        (7303042259 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1161645783 / 1000000000000 : ℚ) +
        (8971247713 / 1000000000000000000 : ℚ) / (2268300899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (9454799 / 8000000000 : ℚ) + (88548869 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7303042259 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12946]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12946 :
    2 * 160 < 12946 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999757 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12946 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12947 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12947. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12947 : WorldParameters where
  hiddenCharge := (232320981 / 200000000000 : ℝ)
  frame := (622273774553 / 1000000000000 : ℝ)
  moment := (4484719107 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12947 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733261173463 / 500000000000 : ℝ)
    root := (520816609 / 62500000000 : ℝ) }

noncomputable def scalar12947 : ScalarCertificate 12947 world12947 agent12947 where
  dimensionLo := 12947
  dimensionHi := 12947
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2268662399 / 1000000000000 : ℝ)
  frameLo := (622273774553 / 1000000000000 : ℝ)
  frameHi := (733261173463 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12947]
  agentFrame_pos := by norm_num only [agent12947]
  worldRadius := (2268662399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12947]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1180877299 / 1000000000000 : ℝ)
  lowerTail := (1415699413 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7300039109 / 1000000000000 : ℝ)
  ledger := by
    have h : (232320981 / 200000000000 : ℚ) +
        (4484719107 / 500000000000000000 : ℚ) / (2268662399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1180877299 / 1000000000000 : ℚ) + (1415699413 / 1000000000000 : ℚ) ≤
        (7300039109 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((232320981 / 200000000000 : ℚ) +
        (4484719107 / 500000000000000000 : ℚ) / (2268662399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1180877299 / 1000000000000 : ℚ) + (1415699413 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7300039109 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12947]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12947 :
    2 * 160 < 12947 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999673 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12947 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12948 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12948. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12948 : WorldParameters where
  hiddenCharge := (1161564037 / 1000000000000 : ℝ)
  frame := (622260464081 / 1000000000000 : ℝ)
  moment := (1120953653 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12948 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146649257651 / 100000000000 : ℝ)
    root := (4166215871 / 500000000000 : ℝ) }

noncomputable def scalar12948 : ScalarCertificate 12948 world12948 agent12948 where
  dimensionLo := 12948
  dimensionHi := 12948
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2269023799 / 1000000000000 : ℝ)
  frameLo := (622260464081 / 1000000000000 : ℝ)
  frameHi := (146649257651 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12948]
  agentFrame_pos := by norm_num only [agent12948]
  worldRadius := (2269023799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12948]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (58995277 / 50000000000 : ℝ)
  lowerTail := (707308889 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3648519191 / 500000000000 : ℝ)
  ledger := by
    have h : (1161564037 / 1000000000000 : ℚ) +
        (1120953653 / 125000000000000000 : ℚ) / (2269023799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (58995277 / 50000000000 : ℚ) + (707308889 / 500000000000 : ℚ) ≤
        (3648519191 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1161564037 / 1000000000000 : ℚ) +
        (1120953653 / 125000000000000000 : ℚ) / (2269023799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (58995277 / 50000000000 : ℚ) + (707308889 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3648519191 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12948]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12948 :
    2 * 160 < 12948 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998563 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12948 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12949 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12949. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12949 : WorldParameters where
  hiddenCharge := (1161523179 / 1000000000000 : ℝ)
  frame := (124449431139 / 200000000000 : ℝ)
  moment := (1120727593 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12949 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293292563681 / 200000000000 : ℝ)
    root := (4165898961 / 500000000000 : ℝ) }

noncomputable def scalar12949 : ScalarCertificate 12949 world12949 agent12949 where
  dimensionLo := 12949
  dimensionHi := 12949
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2269385299 / 1000000000000 : ℝ)
  frameLo := (124449431139 / 200000000000 : ℝ)
  frameHi := (293292563681 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12949]
  agentFrame_pos := by norm_num only [agent12949]
  worldRadius := (2269385299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12949]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (235786953 / 200000000000 : ℝ)
  lowerTail := (706768589 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3647020061 / 500000000000 : ℝ)
  ledger := by
    have h : (1161523179 / 1000000000000 : ℚ) +
        (1120727593 / 125000000000000000 : ℚ) / (2269385299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (235786953 / 200000000000 : ℚ) + (706768589 / 500000000000 : ℚ) ≤
        (3647020061 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1161523179 / 1000000000000 : ℚ) +
        (1120727593 / 125000000000000000 : ℚ) / (2269385299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (235786953 / 200000000000 : ℚ) + (706768589 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3647020061 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12949]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12949 :
    2 * 160 < 12949 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998871 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12949 {← IO.monoMsNow}" : IO Unit)
