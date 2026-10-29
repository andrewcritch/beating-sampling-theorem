import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12225 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12225. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12225 : WorldParameters where
  hiddenCharge := (1194124331 / 1000000000000 : ℝ)
  frame := (126492688957 / 200000000000 : ℝ)
  moment := (10421208667 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12225 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1910257351 / 1000000000000 : ℝ)
    frame := (29200837 / 20000000 : ℝ)
    root := (884983991 / 100000000000 : ℝ) }

noncomputable def scalar12225 : ScalarCertificate 12225 world12225 agent12225 where
  dimensionLo := 12225
  dimensionHi := 12225
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2048454999 / 1000000000000 : ℝ)
  frameLo := (126492688957 / 200000000000 : ℝ)
  frameHi := (29200837 / 20000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12225]
  agentFrame_pos := by norm_num only [agent12225]
  worldRadius := (2048454999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12225]
  retainedCharge := (1910257351 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1030085673 / 500000000000 : ℝ)
  lowerTail := (117434341 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9996746973 / 1000000000000 : ℝ)
  ledger := by
    have h : (1194124331 / 1000000000000 : ℚ) +
        (10421208667 / 1000000000000000000 : ℚ) / (2048454999 / 1000000000000 : ℚ) ^ 2 +
        (1910257351 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1030085673 / 500000000000 : ℚ) + (117434341 / 50000000000 : ℚ) ≤
        (9996746973 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1194124331 / 1000000000000 : ℚ) +
        (10421208667 / 1000000000000000000 : ℚ) / (2048454999 / 1000000000000 : ℚ) ^ 2 +
        (1910257351 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1030085673 / 500000000000 : ℚ) + (117434341 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9996746973 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12225]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12225 :
    2 * 160 < 12225 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499997653 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12225 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12226 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12226. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12226 : WorldParameters where
  hiddenCharge := (1194074763 / 1000000000000 : ℝ)
  frame := (632448479789 / 1000000000000 : ℝ)
  moment := (1302372227 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12226 : AgentParameters :=
  { agentLedgerParameters with
    charge := (381898787 / 200000000000 : ℝ)
    frame := (730000294443 / 500000000000 : ℝ)
    root := (8849094659 / 1000000000000 : ℝ) }

noncomputable def scalar12226 : ScalarCertificate 12226 world12226 agent12226 where
  dimensionLo := 12226
  dimensionHi := 12226
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2048808799 / 1000000000000 : ℝ)
  frameLo := (632448479789 / 1000000000000 : ℝ)
  frameHi := (730000294443 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12226]
  agentFrame_pos := by norm_num only [agent12226]
  worldRadius := (2048808799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12226]
  retainedCharge := (381898787 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (514584131 / 250000000000 : ℝ)
  lowerTail := (2346732359 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1248844449 / 125000000000 : ℝ)
  ledger := by
    have h : (1194074763 / 1000000000000 : ℚ) +
        (1302372227 / 125000000000000000 : ℚ) / (2048808799 / 1000000000000 : ℚ) ^ 2 +
        (381898787 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (514584131 / 250000000000 : ℚ) + (2346732359 / 1000000000000 : ℚ) ≤
        (1248844449 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1194074763 / 1000000000000 : ℚ) +
        (1302372227 / 125000000000000000 : ℚ) / (2048808799 / 1000000000000 : ℚ) ^ 2 +
        (381898787 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (514584131 / 250000000000 : ℚ) + (2346732359 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1248844449 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12226]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12226 :
    2 * 160 < 12226 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (109999957 / 10000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12226 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12227 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12227. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12227 : WorldParameters where
  hiddenCharge := (1194025209 / 1000000000000 : ℝ)
  frame := (632433517309 / 1000000000000 : ℝ)
  moment := (651046727 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12227 : AgentParameters :=
  { agentLedgerParameters with
    charge := (190873121 / 100000000000 : ℝ)
    frame := (1459959348839 / 1000000000000 : ℝ)
    root := (8848349719 / 1000000000000 : ℝ) }

noncomputable def scalar12227 : ScalarCertificate 12227 world12227 agent12227 where
  dimensionLo := 12227
  dimensionHi := 12227
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2049162599 / 1000000000000 : ℝ)
  frameLo := (632433517309 / 1000000000000 : ℝ)
  frameHi := (1459959348839 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12227]
  agentFrame_pos := by norm_num only [agent12227]
  worldRadius := (2049162599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12227]
  retainedCharge := (190873121 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1028251831 / 500000000000 : ℝ)
  lowerTail := (2344779871 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4992384909 / 500000000000 : ℝ)
  ledger := by
    have h : (1194025209 / 1000000000000 : ℚ) +
        (651046727 / 62500000000000000 : ℚ) / (2049162599 / 1000000000000 : ℚ) ^ 2 +
        (190873121 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1028251831 / 500000000000 : ℚ) + (2344779871 / 1000000000000 : ℚ) ≤
        (4992384909 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1194025209 / 1000000000000 : ℚ) +
        (651046727 / 62500000000000000 : ℚ) / (2049162599 / 1000000000000 : ℚ) ^ 2 +
        (190873121 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1028251831 / 500000000000 : ℚ) + (2344779871 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4992384909 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12227]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12227 :
    2 * 160 < 12227 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994233 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12227 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12228 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12228. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12228 : WorldParameters where
  hiddenCharge := (1193975669 / 1000000000000 : ℝ)
  frame := (316209278671 / 500000000000 : ℝ)
  moment := (2082903623 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12228 : AgentParameters :=
  { agentLedgerParameters with
    charge := (238496147 / 125000000000 : ℝ)
    frame := (1459918106313 / 1000000000000 : ℝ)
    root := (552975309 / 62500000000 : ℝ) }

noncomputable def scalar12228 : ScalarCertificate 12228 world12228 agent12228 where
  dimensionLo := 12228
  dimensionHi := 12228
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2049516499 / 1000000000000 : ℝ)
  frameLo := (316209278671 / 500000000000 : ℝ)
  frameHi := (1459918106313 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12228]
  agentFrame_pos := by norm_num only [agent12228]
  worldRadius := (2049516499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12228]
  retainedCharge := (238496147 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (25683407 / 12500000000 : ℝ)
  lowerTail := (117141457 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1995757799 / 200000000000 : ℝ)
  ledger := by
    have h : (1193975669 / 1000000000000 : ℚ) +
        (2082903623 / 200000000000000000 : ℚ) / (2049516499 / 1000000000000 : ℚ) ^ 2 +
        (238496147 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25683407 / 12500000000 : ℚ) + (117141457 / 50000000000 : ℚ) ≤
        (1995757799 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1193975669 / 1000000000000 : ℚ) +
        (2082903623 / 200000000000000000 : ℚ) / (2049516499 / 1000000000000 : ℚ) ^ 2 +
        (238496147 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25683407 / 12500000000 : ℚ) + (117141457 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1995757799 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12228]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12228 :
    2 * 160 < 12228 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2749998829 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12228 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12229 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12229. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12229 : WorldParameters where
  hiddenCharge := (1193926143 / 1000000000000 : ℝ)
  frame := (632403599889 / 1000000000000 : ℝ)
  moment := (2082457853 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12229 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1907207831 / 1000000000000 : ℝ)
    frame := (1459876567077 / 1000000000000 : ℝ)
    root := (1769372081 / 200000000000 : ℝ) }

noncomputable def scalar12229 : ScalarCertificate 12229 world12229 agent12229 where
  dimensionLo := 12229
  dimensionHi := 12229
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2049870799 / 1000000000000 : ℝ)
  frameLo := (632403599889 / 1000000000000 : ℝ)
  frameHi := (1459876567077 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12229]
  agentFrame_pos := by norm_num only [agent12229]
  worldRadius := (2049870799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12229]
  retainedCharge := (1907207831 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (410568381 / 200000000000 : ℝ)
  lowerTail := (2340878529 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9972809441 / 1000000000000 : ℝ)
  ledger := by
    have h : (1193926143 / 1000000000000 : ℚ) +
        (2082457853 / 200000000000000000 : ℚ) / (2049870799 / 1000000000000 : ℚ) ^ 2 +
        (1907207831 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (410568381 / 200000000000 : ℚ) + (2340878529 / 1000000000000 : ℚ) ≤
        (9972809441 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1193926143 / 1000000000000 : ℚ) +
        (2082457853 / 200000000000000000 : ℚ) / (2049870799 / 1000000000000 : ℚ) ^ 2 +
        (1907207831 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (410568381 / 200000000000 : ℚ) + (2340878529 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9972809441 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12229]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12229 :
    2 * 160 < 12229 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (1099999459 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12229 {← IO.monoMsNow}" : IO Unit)
