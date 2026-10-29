import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12240 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12240. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12240 : WorldParameters where
  hiddenCharge := (4773529 / 4000000000 : ℝ)
  frame := (158059808399 / 250000000000 : ℝ)
  moment := (10387815837 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12240 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1898878371 / 1000000000000 : ℝ)
    frame := (1459420953091 / 1000000000000 : ℝ)
    root := (8838686181 / 1000000000000 : ℝ) }

noncomputable def scalar12240 : ScalarCertificate 12240 world12240 agent12240 where
  dimensionLo := 12240
  dimensionHi := 12240
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2053768799 / 1000000000000 : ℝ)
  frameLo := (158059808399 / 250000000000 : ℝ)
  frameHi := (1459420953091 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12240]
  agentFrame_pos := by norm_num only [agent12240]
  worldRadius := (2053768799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12240]
  retainedCharge := (1898878371 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (406565599 / 200000000000 : ℝ)
  lowerTail := (1159773079 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9907390361 / 1000000000000 : ℝ)
  ledger := by
    have h : (4773529 / 4000000000 : ℚ) +
        (10387815837 / 1000000000000000000 : ℚ) / (2053768799 / 1000000000000 : ℚ) ^ 2 +
        (1898878371 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (406565599 / 200000000000 : ℚ) + (1159773079 / 500000000000 : ℚ) ≤
        (9907390361 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((4773529 / 4000000000 : ℚ) +
        (10387815837 / 1000000000000000000 : ℚ) / (2053768799 / 1000000000000 : ℚ) ^ 2 +
        (1898878371 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (406565599 / 200000000000 : ℚ) + (1159773079 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9907390361 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12240]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12240 :
    2 * 160 < 12240 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (687499851 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12240 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12241 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12241. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12241 : WorldParameters where
  hiddenCharge := (1193332887 / 1000000000000 : ℝ)
  frame := (158056076563 / 250000000000 : ℝ)
  moment := (5192797483 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12241 : AgentParameters :=
  { agentLedgerParameters with
    charge := (7592501 / 4000000000 : ℝ)
    frame := (291875930847 / 200000000000 : ℝ)
    root := (55237153 / 6250000000 : ℝ) }

noncomputable def scalar12241 : ScalarCertificate 12241 world12241 agent12241 where
  dimensionLo := 12241
  dimensionHi := 12241
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2054123099 / 1000000000000 : ℝ)
  frameLo := (158056076563 / 250000000000 : ℝ)
  frameHi := (291875930847 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12241]
  agentFrame_pos := by norm_num only [agent12241]
  worldRadius := (2054123099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12241]
  retainedCharge := (7592501 / 4000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (253877443 / 125000000000 : ℝ)
  lowerTail := (1158808969 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9901475371 / 1000000000000 : ℝ)
  ledger := by
    have h : (1193332887 / 1000000000000 : ℚ) +
        (5192797483 / 500000000000000000 : ℚ) / (2054123099 / 1000000000000 : ℚ) ^ 2 +
        (7592501 / 4000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253877443 / 125000000000 : ℚ) + (1158808969 / 500000000000 : ℚ) ≤
        (9901475371 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1193332887 / 1000000000000 : ℚ) +
        (5192797483 / 500000000000000000 : ℚ) / (2054123099 / 1000000000000 : ℚ) ^ 2 +
        (7592501 / 4000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253877443 / 125000000000 : ℚ) + (1158808969 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9901475371 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12241]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12241 :
    2 * 160 < 12241 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998529 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12241 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12242 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12242. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12242 : WorldParameters where
  hiddenCharge := (1193283537 / 1000000000000 : ℝ)
  frame := (158052345353 / 250000000000 : ℝ)
  moment := (10383374759 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12242 : AgentParameters :=
  { agentLedgerParameters with
    charge := (189737281 / 100000000000 : ℝ)
    frame := (182417297041 / 125000000000 : ℝ)
    root := (4418601507 / 500000000000 : ℝ) }

noncomputable def scalar12242 : ScalarCertificate 12242 world12242 agent12242 where
  dimensionLo := 12242
  dimensionHi := 12242
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2054477599 / 1000000000000 : ℝ)
  frameLo := (158052345353 / 250000000000 : ℝ)
  frameHi := (182417297041 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12242]
  agentFrame_pos := by norm_num only [agent12242]
  worldRadius := (2054477599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12242]
  retainedCharge := (189737281 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (126825823 / 62500000000 : ℝ)
  lowerTail := (2315691823 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9895565737 / 1000000000000 : ℝ)
  ledger := by
    have h : (1193283537 / 1000000000000 : ℚ) +
        (10383374759 / 1000000000000000000 : ℚ) / (2054477599 / 1000000000000 : ℚ) ^ 2 +
        (189737281 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (126825823 / 62500000000 : ℚ) + (2315691823 / 1000000000000 : ℚ) ≤
        (9895565737 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1193283537 / 1000000000000 : ℚ) +
        (10383374759 / 1000000000000000000 : ℚ) / (2054477599 / 1000000000000 : ℚ) ^ 2 +
        (189737281 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (126825823 / 62500000000 : ℚ) + (2315691823 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9895565737 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12242]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12242 :
    2 * 160 < 12242 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995333 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12242 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12243 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12243. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12243 : WorldParameters where
  hiddenCharge := (1193234201 / 1000000000000 : ℝ)
  frame := (158048614769 / 250000000000 : ℝ)
  moment := (2076231043 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12243 : AgentParameters :=
  { agentLedgerParameters with
    charge := (37932421 / 20000000000 : ℝ)
    frame := (1459297113479 / 1000000000000 : ℝ)
    root := (8836461783 / 1000000000000 : ℝ) }

noncomputable def scalar12243 : ScalarCertificate 12243 world12243 agent12243 where
  dimensionLo := 12243
  dimensionHi := 12243
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2054831999 / 1000000000000 : ℝ)
  frameLo := (158048614769 / 250000000000 : ℝ)
  frameHi := (1459297113479 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12243]
  agentFrame_pos := by norm_num only [agent12243]
  worldRadius := (2054831999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12243]
  retainedCharge := (37932421 / 20000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2027408481 / 1000000000000 : ℝ)
  lowerTail := (2313767401 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9889661377 / 1000000000000 : ℝ)
  ledger := by
    have h : (1193234201 / 1000000000000 : ℚ) +
        (2076231043 / 200000000000000000 : ℚ) / (2054831999 / 1000000000000 : ℚ) ^ 2 +
        (37932421 / 20000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2027408481 / 1000000000000 : ℚ) + (2313767401 / 1000000000000 : ℚ) ≤
        (9889661377 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1193234201 / 1000000000000 : ℚ) +
        (2076231043 / 200000000000000000 : ℚ) / (2054831999 / 1000000000000 : ℚ) ^ 2 +
        (37932421 / 20000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2027408481 / 1000000000000 : ℚ) + (2313767401 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9889661377 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12243]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12243 :
    2 * 160 < 12243 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499999193 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12243 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12244 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12244. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12244 : WorldParameters where
  hiddenCharge := (596592439 / 500000000000 : ℝ)
  frame := (632179539243 / 1000000000000 : ℝ)
  moment := (5189468167 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12244 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1895869969 / 1000000000000 : ℝ)
    frame := (4560174617 / 3125000000 : ℝ)
    root := (8835720787 / 1000000000000 : ℝ) }

noncomputable def scalar12244 : ScalarCertificate 12244 world12244 agent12244 where
  dimensionLo := 12244
  dimensionHi := 12244
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2055186499 / 1000000000000 : ℝ)
  frameLo := (632179539243 / 1000000000000 : ℝ)
  frameHi := (4560174617 / 3125000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12244]
  agentFrame_pos := by norm_num only [agent12244]
  worldRadius := (2055186499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12244]
  retainedCharge := (1895869969 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2025605783 / 1000000000000 : ℝ)
  lowerTail := (2311844999 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4941881219 / 500000000000 : ℝ)
  ledger := by
    have h : (596592439 / 500000000000 : ℚ) +
        (5189468167 / 500000000000000000 : ℚ) / (2055186499 / 1000000000000 : ℚ) ^ 2 +
        (1895869969 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2025605783 / 1000000000000 : ℚ) + (2311844999 / 1000000000000 : ℚ) ≤
        (4941881219 / 500000000000 : ℚ) := by norm_num only
    have hc : (((596592439 / 500000000000 : ℚ) +
        (5189468167 / 500000000000000000 : ℚ) / (2055186499 / 1000000000000 : ℚ) ^ 2 +
        (1895869969 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2025605783 / 1000000000000 : ℚ) + (2311844999 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4941881219 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12244]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12244 :
    2 * 160 < 12244 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994239 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12244 {← IO.monoMsNow}" : IO Unit)
