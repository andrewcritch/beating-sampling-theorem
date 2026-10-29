import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12285 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12285. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12285 : WorldParameters where
  hiddenCharge := (297793569 / 250000000000 : ℝ)
  frame := (315784986627 / 500000000000 : ℝ)
  moment := (2057705957 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12285 : AgentParameters :=
  { agentLedgerParameters with
    charge := (14575409 / 7812500000 : ℝ)
    frame := (364394377749 / 250000000000 : ℝ)
    root := (1100692509 / 125000000000 : ℝ) }

noncomputable def scalar12285 : ScalarCertificate 12285 world12285 agent12285 where
  dimensionLo := 12285
  dimensionHi := 12285
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2069736499 / 1000000000000 : ℝ)
  frameLo := (315784986627 / 500000000000 : ℝ)
  frameHi := (364394377749 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12285]
  agentFrame_pos := by norm_num only [agent12285]
  worldRadius := (2069736499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12285]
  retainedCharge := (14575409 / 7812500000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (39064731 / 20000000000 : ℝ)
  lowerTail := (1117289253 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1929273451 / 200000000000 : ℝ)
  ledger := by
    have h : (297793569 / 250000000000 : ℚ) +
        (2057705957 / 200000000000000000 : ℚ) / (2069736499 / 1000000000000 : ℚ) ^ 2 +
        (14575409 / 7812500000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (39064731 / 20000000000 : ℚ) + (1117289253 / 500000000000 : ℚ) ≤
        (1929273451 / 200000000000 : ℚ) := by norm_num only
    have hc : (((297793569 / 250000000000 : ℚ) +
        (2057705957 / 200000000000000000 : ℚ) / (2069736499 / 1000000000000 : ℚ) ^ 2 +
        (14575409 / 7812500000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (39064731 / 20000000000 : ℚ) + (1117289253 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1929273451 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12285]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12285 :
    2 * 160 < 12285 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994613 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12285 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12286 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12286. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12286 : WorldParameters where
  hiddenCharge := (1191125519 / 1000000000000 : ℝ)
  frame := (15788878949 / 25000000000 : ℝ)
  moment := (5143169257 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12286 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1864929201 / 1000000000000 : ℝ)
    frame := (728768370207 / 500000000000 : ℝ)
    root := (880480881 / 100000000000 : ℝ) }

noncomputable def scalar12286 : ScalarCertificate 12286 world12286 agent12286 where
  dimensionLo := 12286
  dimensionHi := 12286
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2070091899 / 1000000000000 : ℝ)
  frameLo := (15788878949 / 25000000000 : ℝ)
  frameHi := (728768370207 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12286]
  agentFrame_pos := by norm_num only [agent12286]
  worldRadius := (2070091899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12286]
  retainedCharge := (1864929201 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (975753927 / 500000000000 : ℝ)
  lowerTail := (558182627 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1928136541 / 200000000000 : ℝ)
  ledger := by
    have h : (1191125519 / 1000000000000 : ℚ) +
        (5143169257 / 500000000000000000 : ℚ) / (2070091899 / 1000000000000 : ℚ) ^ 2 +
        (1864929201 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (975753927 / 500000000000 : ℚ) + (558182627 / 250000000000 : ℚ) ≤
        (1928136541 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1191125519 / 1000000000000 : ℚ) +
        (5143169257 / 500000000000000000 : ℚ) / (2070091899 / 1000000000000 : ℚ) ^ 2 +
        (1864929201 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (975753927 / 500000000000 : ℚ) + (558182627 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1928136541 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12286]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12286 :
    2 * 160 < 12286 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999767 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12286 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12287 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12287. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12287 : WorldParameters where
  hiddenCharge := (47643071 / 40000000000 : ℝ)
  frame := (631540345141 / 1000000000000 : ℝ)
  moment := (1285518487 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12287 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1864206701 / 1000000000000 : ℝ)
    frame := (728747998127 / 500000000000 : ℝ)
    root := (550254861 / 62500000000 : ℝ) }

noncomputable def scalar12287 : ScalarCertificate 12287 world12287 agent12287 where
  dimensionLo := 12287
  dimensionHi := 12287
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2070447399 / 1000000000000 : ℝ)
  frameLo := (631540345141 / 1000000000000 : ℝ)
  frameHi := (728747998127 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12287]
  agentFrame_pos := by norm_num only [agent12287]
  worldRadius := (2070447399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12287]
  retainedCharge := (1864206701 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (389956211 / 200000000000 : ℝ)
  lowerTail := (2230884441 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4817501671 / 500000000000 : ℝ)
  ledger := by
    have h : (47643071 / 40000000000 : ℚ) +
        (1285518487 / 125000000000000000 : ℚ) / (2070447399 / 1000000000000 : ℚ) ^ 2 +
        (1864206701 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (389956211 / 200000000000 : ℚ) + (2230884441 / 1000000000000 : ℚ) ≤
        (4817501671 / 500000000000 : ℚ) := by norm_num only
    have hc : (((47643071 / 40000000000 : ℚ) +
        (1285518487 / 125000000000000000 : ℚ) / (2070447399 / 1000000000000 : ℚ) ^ 2 +
        (1864206701 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (389956211 / 200000000000 : ℚ) + (2230884441 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4817501671 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12287]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12287 :
    2 * 160 < 12287 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997643 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12287 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12288 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12288. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12288 : WorldParameters where
  hiddenCharge := (238205609 / 200000000000 : ℝ)
  frame := (157881383699 / 250000000000 : ℝ)
  moment := (1028195793 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12288 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1863484851 / 1000000000000 : ℝ)
    frame := (728727636317 / 500000000000 : ℝ)
    root := (4401673449 / 500000000000 : ℝ) }

noncomputable def scalar12288 : ScalarCertificate 12288 world12288 agent12288 where
  dimensionLo := 12288
  dimensionHi := 12288
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2070802799 / 1000000000000 : ℝ)
  frameLo := (157881383699 / 250000000000 : ℝ)
  frameHi := (728727636317 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12288]
  agentFrame_pos := by norm_num only [agent12288]
  worldRadius := (2070802799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12288]
  retainedCharge := (1863484851 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (194805581 / 100000000000 : ℝ)
  lowerTail := (445807989 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4814664463 / 500000000000 : ℝ)
  ledger := by
    have h : (238205609 / 200000000000 : ℚ) +
        (1028195793 / 100000000000000000 : ℚ) / (2070802799 / 1000000000000 : ℚ) ^ 2 +
        (1863484851 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (194805581 / 100000000000 : ℚ) + (445807989 / 200000000000 : ℚ) ≤
        (4814664463 / 500000000000 : ℚ) := by norm_num only
    have hc : (((238205609 / 200000000000 : ℚ) +
        (1028195793 / 100000000000000000 : ℚ) / (2070802799 / 1000000000000 : ℚ) ^ 2 +
        (1863484851 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (194805581 / 100000000000 : ℚ) + (445807989 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4814664463 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12288]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12288 :
    2 * 160 < 12288 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2749998549 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12288 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12289 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12289. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12289 : WorldParameters where
  hiddenCharge := (4652263 / 3906250000 : ℝ)
  frame := (25260429077 / 40000000000 : ℝ)
  moment := (2055953723 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12289 : AgentParameters :=
  { agentLedgerParameters with
    charge := (37255273 / 20000000000 : ℝ)
    frame := (364353640919 / 250000000000 : ℝ)
    root := (8802616321 / 1000000000000 : ℝ) }

noncomputable def scalar12289 : ScalarCertificate 12289 world12289 agent12289 where
  dimensionLo := 12289
  dimensionHi := 12289
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2071158299 / 1000000000000 : ℝ)
  frameLo := (25260429077 / 40000000000 : ℝ)
  frameHi := (364353640919 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12289]
  agentFrame_pos := by norm_num only [agent12289]
  worldRadius := (2071158299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12289]
  retainedCharge := (37255273 / 20000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (243291559 / 125000000000 : ℝ)
  lowerTail := (17817579 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9623659701 / 1000000000000 : ℝ)
  ledger := by
    have h : (4652263 / 3906250000 : ℚ) +
        (2055953723 / 200000000000000000 : ℚ) / (2071158299 / 1000000000000 : ℚ) ^ 2 +
        (37255273 / 20000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (243291559 / 125000000000 : ℚ) + (17817579 / 8000000000 : ℚ) ≤
        (9623659701 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((4652263 / 3906250000 : ℚ) +
        (2055953723 / 200000000000000000 : ℚ) / (2071158299 / 1000000000000 : ℚ) ^ 2 +
        (37255273 / 20000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (243291559 / 125000000000 : ℚ) + (17817579 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9623659701 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12289]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12289 :
    2 * 160 < 12289 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995391 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12289 {← IO.monoMsNow}" : IO Unit)
