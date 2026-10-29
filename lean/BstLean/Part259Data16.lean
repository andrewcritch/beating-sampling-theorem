import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12305 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12305. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12305 : WorldParameters where
  hiddenCharge := (595100833 / 500000000000 : ℝ)
  frame := (631274136837 / 1000000000000 : ℝ)
  moment := (5122413991 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12305 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1851312239 / 1000000000000 : ℝ)
    frame := (291353164659 / 200000000000 : ℝ)
    root := (2197739409 / 250000000000 : ℝ) }

noncomputable def scalar12305 : ScalarCertificate 12305 world12305 agent12305 where
  dimensionLo := 12305
  dimensionHi := 12305
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2076847799 / 1000000000000 : ℝ)
  frameLo := (631274136837 / 1000000000000 : ℝ)
  frameHi := (291353164659 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12305]
  agentFrame_pos := by norm_num only [agent12305]
  worldRadius := (2076847799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12305]
  retainedCharge := (1851312239 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1918995167 / 1000000000000 : ℝ)
  lowerTail := (2197955201 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9533638713 / 1000000000000 : ℝ)
  ledger := by
    have h : (595100833 / 500000000000 : ℚ) +
        (5122413991 / 500000000000000000 : ℚ) / (2076847799 / 1000000000000 : ℚ) ^ 2 +
        (1851312239 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1918995167 / 1000000000000 : ℚ) + (2197955201 / 1000000000000 : ℚ) ≤
        (9533638713 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((595100833 / 500000000000 : ℚ) +
        (5122413991 / 500000000000000000 : ℚ) / (2076847799 / 1000000000000 : ℚ) ^ 2 +
        (1851312239 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1918995167 / 1000000000000 : ℚ) + (2197955201 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9533638713 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12305]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12305 :
    2 * 160 < 12305 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994601 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12305 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12306 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12306. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12306 : WorldParameters where
  hiddenCharge := (47606127 / 40000000000 : ℝ)
  frame := (631259370913 / 1000000000000 : ℝ)
  moment := (2048529941 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12306 : AgentParameters :=
  { agentLedgerParameters with
    charge := (92530099 / 50000000000 : ℝ)
    frame := (291345086529 / 200000000000 : ℝ)
    root := (4395115421 / 500000000000 : ℝ) }

noncomputable def scalar12306 : ScalarCertificate 12306 world12306 agent12306 where
  dimensionLo := 12306
  dimensionHi := 12306
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2077203599 / 1000000000000 : ℝ)
  frameLo := (631259370913 / 1000000000000 : ℝ)
  frameHi := (291345086529 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12306]
  agentFrame_pos := by norm_num only [agent12306]
  worldRadius := (2077203599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12306]
  retainedCharge := (92530099 / 50000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (958650649 / 500000000000 : ℝ)
  lowerTail := (109807123 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1191006863 / 125000000000 : ℝ)
  ledger := by
    have h : (47606127 / 40000000000 : ℚ) +
        (2048529941 / 200000000000000000 : ℚ) / (2077203599 / 1000000000000 : ℚ) ^ 2 +
        (92530099 / 50000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (958650649 / 500000000000 : ℚ) + (109807123 / 50000000000 : ℚ) ≤
        (1191006863 / 125000000000 : ℚ) := by norm_num only
    have hc : (((47606127 / 40000000000 : ℚ) +
        (2048529941 / 200000000000000000 : ℚ) / (2077203599 / 1000000000000 : ℚ) ^ 2 +
        (92530099 / 50000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (958650649 / 500000000000 : ℚ) + (109807123 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1191006863 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12306]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12306 :
    2 * 160 < 12306 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998709 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12306 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12307 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12307. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12307 : WorldParameters where
  hiddenCharge := (595052349 / 500000000000 : ℝ)
  frame := (157811151863 / 250000000000 : ℝ)
  moment := (409618883 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12307 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1849892359 / 1000000000000 : ℝ)
    frame := (364171267057 / 250000000000 : ℝ)
    root := (8789504347 / 1000000000000 : ℝ) }

noncomputable def scalar12307 : ScalarCertificate 12307 world12307 agent12307 where
  dimensionLo := 12307
  dimensionHi := 12307
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2077559299 / 1000000000000 : ℝ)
  frameLo := (157811151863 / 250000000000 : ℝ)
  frameHi := (364171267057 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12307]
  agentFrame_pos := by norm_num only [agent12307]
  worldRadius := (2077559299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12307]
  retainedCharge := (1849892359 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (957804571 / 500000000000 : ℝ)
  lowerTail := (548582863 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1904495267 / 200000000000 : ℝ)
  ledger := by
    have h : (595052349 / 500000000000 : ℚ) +
        (409618883 / 40000000000000000 : ℚ) / (2077559299 / 1000000000000 : ℚ) ^ 2 +
        (1849892359 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (957804571 / 500000000000 : ℚ) + (548582863 / 250000000000 : ℚ) ≤
        (1904495267 / 200000000000 : ℚ) := by norm_num only
    have hc : (((595052349 / 500000000000 : ℚ) +
        (409618883 / 40000000000000000 : ℚ) / (2077559299 / 1000000000000 : ℚ) ^ 2 +
        (1849892359 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (957804571 / 500000000000 : ℚ) + (548582863 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1904495267 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12307]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12307 :
    2 * 160 < 12307 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (219999899 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12307 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12308 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12308. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12308 : WorldParameters where
  hiddenCharge := (1190056233 / 1000000000000 : ℝ)
  frame := (631229846451 / 1000000000000 : ℝ)
  moment := (2559573773 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12308 : AgentParameters :=
  { agentLedgerParameters with
    charge := (115573961 / 62500000000 : ℝ)
    frame := (291328943661 / 200000000000 : ℝ)
    root := (1757755601 / 200000000000 : ℝ) }

noncomputable def scalar12308 : ScalarCertificate 12308 world12308 agent12308 where
  dimensionLo := 12308
  dimensionHi := 12308
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2077914999 / 1000000000000 : ℝ)
  frameLo := (631229846451 / 1000000000000 : ℝ)
  frameHi := (291328943661 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12308]
  agentFrame_pos := by norm_num only [agent12308]
  worldRadius := (2077914999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12308]
  retainedCharge := (115573961 / 62500000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1913918581 / 1000000000000 : ℝ)
  lowerTail := (2192522057 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9516902537 / 1000000000000 : ℝ)
  ledger := by
    have h : (1190056233 / 1000000000000 : ℚ) +
        (2559573773 / 250000000000000000 : ℚ) / (2077914999 / 1000000000000 : ℚ) ^ 2 +
        (115573961 / 62500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1913918581 / 1000000000000 : ℚ) + (2192522057 / 1000000000000 : ℚ) ≤
        (9516902537 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1190056233 / 1000000000000 : ℚ) +
        (2559573773 / 250000000000000000 : ℚ) / (2077914999 / 1000000000000 : ℚ) ^ 2 +
        (115573961 / 62500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1913918581 / 1000000000000 : ℚ) + (2192522057 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9516902537 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12308]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12308 :
    2 * 160 < 12308 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995351 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12308 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12309 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12309. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12309 : WorldParameters where
  hiddenCharge := (595003891 / 500000000000 : ℝ)
  frame := (631215087911 / 1000000000000 : ℝ)
  moment := (2047223751 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12309 : AgentParameters :=
  { agentLedgerParameters with
    charge := (462118757 / 250000000000 : ℝ)
    frame := (1456604382867 / 1000000000000 : ℝ)
    root := (8788051961 / 1000000000000 : ℝ) }

noncomputable def scalar12309 : ScalarCertificate 12309 world12309 agent12309 where
  dimensionLo := 12309
  dimensionHi := 12309
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2078270799 / 1000000000000 : ℝ)
  frameLo := (631215087911 / 1000000000000 : ℝ)
  frameHi := (1456604382867 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12309]
  agentFrame_pos := by norm_num only [agent12309]
  worldRadius := (2078270799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12309]
  retainedCharge := (462118757 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (382445977 / 200000000000 : ℝ)
  lowerTail := (2190714547 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4755666911 / 500000000000 : ℝ)
  ledger := by
    have h : (595003891 / 500000000000 : ℚ) +
        (2047223751 / 200000000000000000 : ℚ) / (2078270799 / 1000000000000 : ℚ) ^ 2 +
        (462118757 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (382445977 / 200000000000 : ℚ) + (2190714547 / 1000000000000 : ℚ) ≤
        (4755666911 / 500000000000 : ℚ) := by norm_num only
    have hc : (((595003891 / 500000000000 : ℚ) +
        (2047223751 / 200000000000000000 : ℚ) / (2078270799 / 1000000000000 : ℚ) ^ 2 +
        (462118757 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (382445977 / 200000000000 : ℚ) + (2190714547 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4755666911 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12309]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12309 :
    2 * 160 < 12309 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999891 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12309 {← IO.monoMsNow}" : IO Unit)
