import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12800 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12800. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12800 : WorldParameters where
  hiddenCharge := (1167729809 / 1000000000000 : ℝ)
  frame := (624253391691 / 1000000000000 : ℝ)
  moment := (1155125833 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12800 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736053697647 / 500000000000 : ℝ)
    root := (421414637 / 50000000000 : ℝ) }

noncomputable def scalar12800 : ScalarCertificate 12800 world12800 agent12800 where
  dimensionLo := 12800
  dimensionHi := 12800
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2214115199 / 1000000000000 : ℝ)
  frameLo := (624253391691 / 1000000000000 : ℝ)
  frameHi := (736053697647 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12800]
  agentFrame_pos := by norm_num only [agent12800]
  worldRadius := (2214115199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12800]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1337478947 / 1000000000000 : ℝ)
  lowerTail := (1589867531 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1944813711 / 250000000000 : ℝ)
  ledger := by
    have h : (1167729809 / 1000000000000 : ℚ) +
        (1155125833 / 125000000000000000 : ℚ) / (2214115199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1337478947 / 1000000000000 : ℚ) + (1589867531 / 1000000000000 : ℚ) ≤
        (1944813711 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1167729809 / 1000000000000 : ℚ) +
        (1155125833 / 125000000000000000 : ℚ) / (2214115199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1337478947 / 1000000000000 : ℚ) + (1589867531 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1944813711 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12800]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12800 :
    2 * 160 < 12800 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999427 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12800 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12801 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12801. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12801 : WorldParameters where
  hiddenCharge := (583843671 / 500000000000 : ℝ)
  frame := (312119884397 / 500000000000 : ℝ)
  moment := (4619560341 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12801 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736038131757 / 500000000000 : ℝ)
    root := (1685526171 / 200000000000 : ℝ) }

noncomputable def scalar12801 : ScalarCertificate 12801 world12801 agent12801 where
  dimensionLo := 12801
  dimensionHi := 12801
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2214474099 / 1000000000000 : ℝ)
  frameLo := (312119884397 / 500000000000 : ℝ)
  frameHi := (736038131757 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12801]
  agentFrame_pos := by norm_num only [agent12801]
  worldRadius := (2214474099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12801]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (13363597 / 10000000000 : ℝ)
  lowerTail := (317726423 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3887931081 / 500000000000 : ℝ)
  ledger := by
    have h : (583843671 / 500000000000 : ℚ) +
        (4619560341 / 500000000000000000 : ℚ) / (2214474099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (13363597 / 10000000000 : ℚ) + (317726423 / 200000000000 : ℚ) ≤
        (3887931081 / 500000000000 : ℚ) := by norm_num only
    have hc : (((583843671 / 500000000000 : ℚ) +
        (4619560341 / 500000000000000000 : ℚ) / (2214474099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (13363597 / 10000000000 : ℚ) + (317726423 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3887931081 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12801]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12801 :
    2 * 160 < 12801 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994019 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12801 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12802 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12802. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12802 : WorldParameters where
  hiddenCharge := (1167644887 / 1000000000000 : ℝ)
  frame := (312113074031 / 500000000000 : ℝ)
  moment := (4618617619 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12802 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184005642403 / 125000000000 : ℝ)
    root := (8426969169 / 1000000000000 : ℝ) }

noncomputable def scalar12802 : ScalarCertificate 12802 world12802 agent12802 where
  dimensionLo := 12802
  dimensionHi := 12802
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2214832899 / 1000000000000 : ℝ)
  frameLo := (312113074031 / 500000000000 : ℝ)
  frameHi := (184005642403 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12802]
  agentFrame_pos := by norm_num only [agent12802]
  worldRadius := (2214832899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12802]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (66762071 / 50000000000 : ℝ)
  lowerTail := (1587397693 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1943118069 / 250000000000 : ℝ)
  ledger := by
    have h : (1167644887 / 1000000000000 : ℚ) +
        (4618617619 / 500000000000000000 : ℚ) / (2214832899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (66762071 / 50000000000 : ℚ) + (1587397693 / 1000000000000 : ℚ) ≤
        (1943118069 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1167644887 / 1000000000000 : ℚ) +
        (4618617619 / 500000000000000000 : ℚ) / (2214832899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (66762071 / 50000000000 : ℚ) + (1587397693 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1943118069 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12802]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12802 :
    2 * 160 < 12802 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999459 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12802 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12803 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12803. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12803 : WorldParameters where
  hiddenCharge := (1167602443 / 1000000000000 : ℝ)
  frame := (312106264747 / 500000000000 : ℝ)
  moment := (2308837583 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12803 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46000438753 / 31250000000 : ℝ)
    root := (8426307747 / 1000000000000 : ℝ) }

noncomputable def scalar12803 : ScalarCertificate 12803 world12803 agent12803 where
  dimensionLo := 12803
  dimensionHi := 12803
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2215191899 / 1000000000000 : ℝ)
  frameLo := (312106264747 / 500000000000 : ℝ)
  frameHi := (46000438753 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12803]
  agentFrame_pos := by norm_num only [agent12803]
  worldRadius := (2215191899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12803]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (53364979 / 40000000000 : ℝ)
  lowerTail := (793082337 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7769085457 / 1000000000000 : ℝ)
  ledger := by
    have h : (1167602443 / 1000000000000 : ℚ) +
        (2308837583 / 250000000000000000 : ℚ) / (2215191899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (53364979 / 40000000000 : ℚ) + (793082337 / 500000000000 : ℚ) ≤
        (7769085457 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1167602443 / 1000000000000 : ℚ) +
        (2308837583 / 250000000000000000 : ℚ) / (2215191899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (53364979 / 40000000000 : ℚ) + (793082337 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7769085457 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12803]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12803 :
    2 * 160 < 12803 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999007 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12803 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12804 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12804. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12804 : WorldParameters where
  hiddenCharge := (116756001 / 100000000000 : ℝ)
  frame := (62419891309 / 100000000000 : ℝ)
  moment := (9233465963 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12804 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471982954333 / 1000000000000 : ℝ)
    root := (8425646459 / 1000000000000 : ℝ) }

noncomputable def scalar12804 : ScalarCertificate 12804 world12804 agent12804 where
  dimensionLo := 12804
  dimensionHi := 12804
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2215550799 / 1000000000000 : ℝ)
  frameLo := (62419891309 / 100000000000 : ℝ)
  frameHi := (1471982954333 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12804]
  agentFrame_pos := by norm_num only [agent12804]
  worldRadius := (2215550799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12804]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (666504233 / 500000000000 : ℝ)
  lowerTail := (12679461 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7765701377 / 1000000000000 : ℝ)
  ledger := by
    have h : (116756001 / 100000000000 : ℚ) +
        (9233465963 / 1000000000000000000 : ℚ) / (2215550799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (666504233 / 500000000000 : ℚ) + (12679461 / 8000000000 : ℚ) ≤
        (7765701377 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((116756001 / 100000000000 : ℚ) +
        (9233465963 / 1000000000000000000 : ℚ) / (2215550799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (666504233 / 500000000000 : ℚ) + (12679461 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7765701377 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12804]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12804 :
    2 * 160 < 12804 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998669 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12804 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12805 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12805. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12805 : WorldParameters where
  hiddenCharge := (291879397 / 250000000000 : ℝ)
  frame := (624185298849 / 1000000000000 : ℝ)
  moment := (2307895533 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12805 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471951881929 / 1000000000000 : ℝ)
    root := (842498537 / 100000000000 : ℝ) }

noncomputable def scalar12805 : ScalarCertificate 12805 world12805 agent12805 where
  dimensionLo := 12805
  dimensionHi := 12805
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2215909699 / 1000000000000 : ℝ)
  frameLo := (624185298849 / 1000000000000 : ℝ)
  frameHi := (1471951881929 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12805]
  agentFrame_pos := by norm_num only [agent12805]
  worldRadius := (2215909699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12805]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1331893527 / 1000000000000 : ℝ)
  lowerTail := (791850843 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7762320143 / 1000000000000 : ℝ)
  ledger := by
    have h : (291879397 / 250000000000 : ℚ) +
        (2307895533 / 250000000000000000 : ℚ) / (2215909699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1331893527 / 1000000000000 : ℚ) + (791850843 / 500000000000 : ℚ) ≤
        (7762320143 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((291879397 / 250000000000 : ℚ) +
        (2307895533 / 250000000000000000 : ℚ) / (2215909699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1331893527 / 1000000000000 : ℚ) + (791850843 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7762320143 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12805]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12805 :
    2 * 160 < 12805 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997819 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12805 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12806 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12806. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12806 : WorldParameters where
  hiddenCharge := (1167475177 / 1000000000000 : ℝ)
  frame := (62417168677 / 100000000000 : ℝ)
  moment := (9229698837 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12806 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471920828767 / 1000000000000 : ℝ)
    root := (8424324479 / 1000000000000 : ℝ) }

noncomputable def scalar12806 : ScalarCertificate 12806 world12806 agent12806 where
  dimensionLo := 12806
  dimensionHi := 12806
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2216268599 / 1000000000000 : ℝ)
  frameLo := (62417168677 / 100000000000 : ℝ)
  frameHi := (1471920828767 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12806]
  agentFrame_pos := by norm_num only [agent12806]
  worldRadius := (2216268599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12806]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1330779679 / 1000000000000 : ℝ)
  lowerTail := (316494377 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1939735451 / 250000000000 : ℝ)
  ledger := by
    have h : (1167475177 / 1000000000000 : ℚ) +
        (9229698837 / 1000000000000000000 : ℚ) / (2216268599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1330779679 / 1000000000000 : ℚ) + (316494377 / 200000000000 : ℚ) ≤
        (1939735451 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1167475177 / 1000000000000 : ℚ) +
        (9229698837 / 1000000000000000000 : ℚ) / (2216268599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1330779679 / 1000000000000 : ℚ) + (316494377 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1939735451 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12806]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12806 :
    2 * 160 < 12806 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998271 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12806 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12807 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12807. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12807 : WorldParameters where
  hiddenCharge := (1167432777 / 1000000000000 : ℝ)
  frame := (312079038427 / 500000000000 : ℝ)
  moment := (115347701 / 12500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12807 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735944897419 / 500000000000 : ℝ)
    root := (2105915963 / 250000000000 : ℝ) }

noncomputable def scalar12807 : ScalarCertificate 12807 world12807 agent12807 where
  dimensionLo := 12807
  dimensionHi := 12807
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2216627599 / 1000000000000 : ℝ)
  frameLo := (312079038427 / 500000000000 : ℝ)
  frameHi := (735944897419 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12807]
  agentFrame_pos := by norm_num only [agent12807]
  worldRadius := (2216627599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12807]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (265933411 / 200000000000 : ℝ)
  lowerTail := (395310841 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (60590363 / 7812500000 : ℝ)
  ledger := by
    have h : (1167432777 / 1000000000000 : ℚ) +
        (115347701 / 12500000000000000 : ℚ) / (2216627599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265933411 / 200000000000 : ℚ) + (395310841 / 250000000000 : ℚ) ≤
        (60590363 / 7812500000 : ℚ) := by norm_num only
    have hc : (((1167432777 / 1000000000000 : ℚ) +
        (115347701 / 12500000000000000 : ℚ) / (2216627599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265933411 / 200000000000 : ℚ) + (395310841 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((60590363 / 7812500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12807]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12807 :
    2 * 160 < 12807 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998003 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12807 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12808 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12808. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12808 : WorldParameters where
  hiddenCharge := (291847597 / 250000000000 : ℝ)
  frame := (624144469099 / 1000000000000 : ℝ)
  moment := (9225933859 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12808 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735929387121 / 500000000000 : ℝ)
    root := (4211501679 / 500000000000 : ℝ) }

noncomputable def scalar12808 : ScalarCertificate 12808 world12808 agent12808 where
  dimensionLo := 12808
  dimensionHi := 12808
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2216986499 / 1000000000000 : ℝ)
  frameLo := (624144469099 / 1000000000000 : ℝ)
  frameHi := (735929387121 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12808]
  agentFrame_pos := by norm_num only [agent12808]
  worldRadius := (2216986499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12808]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1328555363 / 1000000000000 : ℝ)
  lowerTail := (24687747 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3876096927 / 500000000000 : ℝ)
  ledger := by
    have h : (291847597 / 250000000000 : ℚ) +
        (9225933859 / 1000000000000000000 : ℚ) / (2216986499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1328555363 / 1000000000000 : ℚ) + (24687747 / 15625000000 : ℚ) ≤
        (3876096927 / 500000000000 : ℚ) := by norm_num only
    have hc : (((291847597 / 250000000000 : ℚ) +
        (9225933859 / 1000000000000000000 : ℚ) / (2216986499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1328555363 / 1000000000000 : ℚ) + (24687747 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((3876096927 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12808]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12808 :
    2 * 160 < 12808 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998587 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12808 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12809 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12809. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12809 : WorldParameters where
  hiddenCharge := (1167348011 / 1000000000000 : ℝ)
  frame := (124826172701 / 200000000000 : ℝ)
  moment := (4612026087 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12809 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735913886431 / 500000000000 : ℝ)
    root := (4211171531 / 500000000000 : ℝ) }

noncomputable def scalar12809 : ScalarCertificate 12809 world12809 agent12809 where
  dimensionLo := 12809
  dimensionHi := 12809
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2217345399 / 1000000000000 : ℝ)
  frameLo := (124826172701 / 200000000000 : ℝ)
  frameHi := (735913886431 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12809]
  agentFrame_pos := by norm_num only [agent12809]
  worldRadius := (2217345399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12809]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (33186119 / 25000000000 : ℝ)
  lowerTail := (789394693 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (774882413 / 100000000000 : ℝ)
  ledger := by
    have h : (1167348011 / 1000000000000 : ℚ) +
        (4612026087 / 500000000000000000 : ℚ) / (2217345399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (33186119 / 25000000000 : ℚ) + (789394693 / 500000000000 : ℚ) ≤
        (774882413 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1167348011 / 1000000000000 : ℚ) +
        (4612026087 / 500000000000000000 : ℚ) / (2217345399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (33186119 / 25000000000 : ℚ) + (789394693 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((774882413 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12809]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12809 :
    2 * 160 < 12809 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999823 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12809 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12810 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12810. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12810 : WorldParameters where
  hiddenCharge := (291826411 / 250000000000 : ℝ)
  frame := (624117260071 / 1000000000000 : ℝ)
  moment := (4611085513 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12810 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735858362229 / 500000000000 : ℝ)
    root := (2105420741 / 250000000000 : ℝ) }

noncomputable def scalar12810 : ScalarCertificate 12810 world12810 agent12810 where
  dimensionLo := 12810
  dimensionHi := 12810
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2217818199 / 1000000000000 : ℝ)
  frameLo := (624117260071 / 1000000000000 : ℝ)
  frameHi := (735858362229 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12810]
  agentFrame_pos := by norm_num only [agent12810]
  worldRadius := (2217818199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12810]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1326097701 / 1000000000000 : ℝ)
  lowerTail := (197157013 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3872359579 / 500000000000 : ℝ)
  ledger := by
    have h : (291826411 / 250000000000 : ℚ) +
        (4611085513 / 500000000000000000 : ℚ) / (2217818199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1326097701 / 1000000000000 : ℚ) + (197157013 / 125000000000 : ℚ) ≤
        (3872359579 / 500000000000 : ℚ) := by norm_num only
    have hc : (((291826411 / 250000000000 : ℚ) +
        (4611085513 / 500000000000000000 : ℚ) / (2217818199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1326097701 / 1000000000000 : ℚ) + (197157013 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3872359579 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12810]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12810 :
    2 * 160 < 12810 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999341 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12810 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12811 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12811. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12811 : WorldParameters where
  hiddenCharge := (1167263289 / 1000000000000 : ℝ)
  frame := (624103658797 / 1000000000000 : ℝ)
  moment := (9220290413 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12811 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471685756517 / 1000000000000 : ℝ)
    root := (842102313 / 100000000000 : ℝ) }

noncomputable def scalar12811 : ScalarCertificate 12811 world12811 agent12811 where
  dimensionLo := 12811
  dimensionHi := 12811
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2218177199 / 1000000000000 : ℝ)
  frameLo := (624103658797 / 1000000000000 : ℝ)
  frameHi := (1471685756517 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12811]
  agentFrame_pos := by norm_num only [agent12811]
  worldRadius := (2218177199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12811]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1324989543 / 1000000000000 : ℝ)
  lowerTail := (788016129 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1548271149 / 200000000000 : ℝ)
  ledger := by
    have h : (1167263289 / 1000000000000 : ℚ) +
        (9220290413 / 1000000000000000000 : ℚ) / (2218177199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1324989543 / 1000000000000 : ℚ) + (788016129 / 500000000000 : ℚ) ≤
        (1548271149 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1167263289 / 1000000000000 : ℚ) +
        (9220290413 / 1000000000000000000 : ℚ) / (2218177199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1324989543 / 1000000000000 : ℚ) + (788016129 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1548271149 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12811]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12811 :
    2 * 160 < 12811 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998169 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12811 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12812 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12812. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12812 : WorldParameters where
  hiddenCharge := (233444189 / 200000000000 : ℝ)
  frame := (312045029841 / 500000000000 : ℝ)
  moment := (9218410337 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12812 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367913700469 / 250000000000 : ℝ)
    root := (2105090857 / 250000000000 : ℝ) }

noncomputable def scalar12812 : ScalarCertificate 12812 world12812 agent12812 where
  dimensionLo := 12812
  dimensionHi := 12812
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2218536099 / 1000000000000 : ℝ)
  frameLo := (312045029841 / 500000000000 : ℝ)
  frameHi := (367913700469 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12812]
  agentFrame_pos := by norm_num only [agent12812]
  worldRadius := (2218536099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12812]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1323882313 / 1000000000000 : ℝ)
  lowerTail := (393702343 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (154759901 / 20000000000 : ℝ)
  ledger := by
    have h : (233444189 / 200000000000 : ℚ) +
        (9218410337 / 1000000000000000000 : ℚ) / (2218536099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1323882313 / 1000000000000 : ℚ) + (393702343 / 250000000000 : ℚ) ≤
        (154759901 / 20000000000 : ℚ) := by norm_num only
    have hc : (((233444189 / 200000000000 : ℚ) +
        (9218410337 / 1000000000000000000 : ℚ) / (2218536099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1323882313 / 1000000000000 : ℚ) + (393702343 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((154759901 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12812]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12812 :
    2 * 160 < 12812 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (171874979 / 15625000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12812 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12813 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12813. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12813 : WorldParameters where
  hiddenCharge := (291794653 / 250000000000 : ℝ)
  frame := (312038231363 / 500000000000 : ℝ)
  moment := (2304132699 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12813 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294324773283 / 200000000000 : ℝ)
    root := (8419703923 / 1000000000000 : ℝ) }

noncomputable def scalar12813 : ScalarCertificate 12813 world12813 agent12813 where
  dimensionLo := 12813
  dimensionHi := 12813
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2218895099 / 1000000000000 : ℝ)
  frameLo := (312038231363 / 500000000000 : ℝ)
  frameHi := (294324773283 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12813]
  agentFrame_pos := by norm_num only [agent12813]
  worldRadius := (2218895099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12813]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (661388123 / 500000000000 : ℝ)
  lowerTail := (196698463 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (773463723 / 100000000000 : ℝ)
  ledger := by
    have h : (291794653 / 250000000000 : ℚ) +
        (2304132699 / 250000000000000000 : ℚ) / (2218895099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (661388123 / 500000000000 : ℚ) + (196698463 / 125000000000 : ℚ) ≤
        (773463723 / 100000000000 : ℚ) := by norm_num only
    have hc : (((291794653 / 250000000000 : ℚ) +
        (2304132699 / 250000000000000000 : ℚ) / (2218895099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (661388123 / 500000000000 : ℚ) + (196698463 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((773463723 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12813]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12813 :
    2 * 160 < 12813 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998109 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12813 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12814 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12814. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12814 : WorldParameters where
  hiddenCharge := (116713629 / 100000000000 : ℝ)
  frame := (78007858491 / 125000000000 : ℝ)
  moment := (9214651791 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12814 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471592950127 / 1000000000000 : ℝ)
    root := (8419044617 / 1000000000000 : ℝ) }

noncomputable def scalar12814 : ScalarCertificate 12814 world12814 agent12814 where
  dimensionLo := 12814
  dimensionHi := 12814
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2219254099 / 1000000000000 : ℝ)
  frameLo := (78007858491 / 125000000000 : ℝ)
  frameHi := (1471592950127 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12814]
  agentFrame_pos := by norm_num only [agent12814]
  worldRadius := (2219254099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12814]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (660835631 / 500000000000 : ℝ)
  lowerTail := (786183583 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3865641141 / 500000000000 : ℝ)
  ledger := by
    have h : (116713629 / 100000000000 : ℚ) +
        (9214651791 / 1000000000000000000 : ℚ) / (2219254099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (660835631 / 500000000000 : ℚ) + (786183583 / 500000000000 : ℚ) ≤
        (3865641141 / 500000000000 : ℚ) := by norm_num only
    have hc : (((116713629 / 100000000000 : ℚ) +
        (9214651791 / 1000000000000000000 : ℚ) / (2219254099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (660835631 / 500000000000 : ℚ) + (786183583 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3865641141 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12814]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12814 :
    2 * 160 < 12814 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994673 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12814 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12815 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12815. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12815 : WorldParameters where
  hiddenCharge := (1167093979 / 1000000000000 : ℝ)
  frame := (78006159411 / 125000000000 : ℝ)
  moment := (9212773321 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12815 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471562047113 / 1000000000000 : ℝ)
    root := (8418385507 / 1000000000000 : ℝ) }

noncomputable def scalar12815 : ScalarCertificate 12815 world12815 agent12815 where
  dimensionLo := 12815
  dimensionHi := 12815
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2219613099 / 1000000000000 : ℝ)
  frameLo := (78006159411 / 125000000000 : ℝ)
  frameHi := (1471562047113 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12815]
  agentFrame_pos := by norm_num only [agent12815]
  worldRadius := (2219613099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12815]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (660283667 / 500000000000 : ℝ)
  lowerTail := (785573863 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7727930149 / 1000000000000 : ℝ)
  ledger := by
    have h : (1167093979 / 1000000000000 : ℚ) +
        (9212773321 / 1000000000000000000 : ℚ) / (2219613099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (660283667 / 500000000000 : ℚ) + (785573863 / 500000000000 : ℚ) ≤
        (7727930149 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1167093979 / 1000000000000 : ℚ) +
        (9212773321 / 1000000000000000000 : ℚ) / (2219613099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (660283667 / 500000000000 : ℚ) + (785573863 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7727930149 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12815]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12815 :
    2 * 160 < 12815 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994511 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12815 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12816 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12816. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12816 : WorldParameters where
  hiddenCharge := (1167051679 / 1000000000000 : ℝ)
  frame := (124807136961 / 200000000000 : ℝ)
  moment := (4605447693 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12816 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367882789341 / 250000000000 : ℝ)
    root := (420886333 / 50000000000 : ℝ) }

noncomputable def scalar12816 : ScalarCertificate 12816 world12816 agent12816 where
  dimensionLo := 12816
  dimensionHi := 12816
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2219971999 / 1000000000000 : ℝ)
  frameLo := (124807136961 / 200000000000 : ℝ)
  frameHi := (367882789341 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12816]
  agentFrame_pos := by norm_num only [agent12816]
  worldRadius := (2219971999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12816]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (659732217 / 500000000000 : ℝ)
  lowerTail := (784964673 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7724580931 / 1000000000000 : ℝ)
  ledger := by
    have h : (1167051679 / 1000000000000 : ℚ) +
        (4605447693 / 500000000000000000 : ℚ) / (2219971999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (659732217 / 500000000000 : ℚ) + (784964673 / 500000000000 : ℚ) ≤
        (7724580931 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1167051679 / 1000000000000 : ℚ) +
        (4605447693 / 500000000000000000 : ℚ) / (2219971999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (659732217 / 500000000000 : ℚ) + (784964673 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7724580931 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12816]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12816 :
    2 * 160 < 12816 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999521 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12816 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12817 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12817. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12817 : WorldParameters where
  hiddenCharge := (1167009391 / 1000000000000 : ℝ)
  frame := (312011048239 / 500000000000 : ℝ)
  moment := (4604508993 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12817 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735750143381 / 500000000000 : ℝ)
    root := (1683413589 / 200000000000 : ℝ) }

noncomputable def scalar12817 : ScalarCertificate 12817 world12817 agent12817 where
  dimensionLo := 12817
  dimensionHi := 12817
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2220330999 / 1000000000000 : ℝ)
  frameLo := (312011048239 / 500000000000 : ℝ)
  frameHi := (735750143381 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12817]
  agentFrame_pos := by norm_num only [agent12817]
  worldRadius := (2220330999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12817]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (16479533 / 12500000000 : ℝ)
  lowerTail := (24511127 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3860617237 / 500000000000 : ℝ)
  ledger := by
    have h : (1167009391 / 1000000000000 : ℚ) +
        (4604508993 / 500000000000000000 : ℚ) / (2220330999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (16479533 / 12500000000 : ℚ) + (24511127 / 15625000000 : ℚ) ≤
        (3860617237 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1167009391 / 1000000000000 : ℚ) +
        (4604508993 / 500000000000000000 : ℚ) / (2220330999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (16479533 / 12500000000 : ℚ) + (24511127 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((3860617237 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12817]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12817 :
    2 * 160 < 12817 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998869 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12817 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12818 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12818. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12818 : WorldParameters where
  hiddenCharge := (1166967113 / 1000000000000 : ℝ)
  frame := (156002127577 / 250000000000 : ℝ)
  moment := (7193079 / 781250000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12818 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471469435299 / 1000000000000 : ℝ)
    root := (8416409427 / 1000000000000 : ℝ) }

noncomputable def scalar12818 : ScalarCertificate 12818 world12818 agent12818 where
  dimensionLo := 12818
  dimensionHi := 12818
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2220690099 / 1000000000000 : ℝ)
  frameLo := (156002127577 / 250000000000 : ℝ)
  frameHi := (1471469435299 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12818]
  agentFrame_pos := by norm_num only [agent12818]
  worldRadius := (2220690099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12818]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1317262003 / 1000000000000 : ℝ)
  lowerTail := (783748061 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1929472719 / 250000000000 : ℝ)
  ledger := by
    have h : (1166967113 / 1000000000000 : ℚ) +
        (7193079 / 781250000000000 : ℚ) / (2220690099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1317262003 / 1000000000000 : ℚ) + (783748061 / 500000000000 : ℚ) ≤
        (1929472719 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1166967113 / 1000000000000 : ℚ) +
        (7193079 / 781250000000000 : ℚ) / (2220690099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1317262003 / 1000000000000 : ℚ) + (783748061 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1929472719 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12818]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12818 :
    2 * 160 < 12818 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199998977 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12818 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12819 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12819. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12819 : WorldParameters where
  hiddenCharge := (1166924847 / 1000000000000 : ℝ)
  frame := (155998731573 / 250000000000 : ℝ)
  moment := (9205264789 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12819 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367859649269 / 250000000000 : ℝ)
    root := (4207875553 / 500000000000 : ℝ) }

noncomputable def scalar12819 : ScalarCertificate 12819 world12819 agent12819 where
  dimensionLo := 12819
  dimensionHi := 12819
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2221049099 / 1000000000000 : ℝ)
  frameLo := (155998731573 / 250000000000 : ℝ)
  frameHi := (367859649269 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12819]
  agentFrame_pos := by norm_num only [agent12819]
  worldRadius := (2221049099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12819]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1316162339 / 1000000000000 : ℝ)
  lowerTail := (1566281121 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7714550081 / 1000000000000 : ℝ)
  ledger := by
    have h : (1166924847 / 1000000000000 : ℚ) +
        (9205264789 / 1000000000000000000 : ℚ) / (2221049099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1316162339 / 1000000000000 : ℚ) + (1566281121 / 1000000000000 : ℚ) ≤
        (7714550081 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1166924847 / 1000000000000 : ℚ) +
        (9205264789 / 1000000000000000000 : ℚ) / (2221049099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1316162339 / 1000000000000 : ℚ) + (1566281121 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7714550081 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12819]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12819 :
    2 * 160 < 12819 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995219 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12819 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12820 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12820. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12820 : WorldParameters where
  hiddenCharge := (1166882591 / 1000000000000 : ℝ)
  frame := (38998834027 / 62500000000 : ℝ)
  moment := (9203388993 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12820 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471327826277 / 1000000000000 : ℝ)
    root := (4207546491 / 500000000000 : ℝ) }

noncomputable def scalar12820 : ScalarCertificate 12820 world12820 agent12820 where
  dimensionLo := 12820
  dimensionHi := 12820
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2221521999 / 1000000000000 : ℝ)
  frameLo := (38998834027 / 62500000000 : ℝ)
  frameHi := (1471327826277 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12820]
  agentFrame_pos := by norm_num only [agent12820]
  worldRadius := (2221521999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12820]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (164353537 / 125000000000 : ℝ)
  lowerTail := (1564761779 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7710479983 / 1000000000000 : ℝ)
  ledger := by
    have h : (1166882591 / 1000000000000 : ℚ) +
        (9203388993 / 1000000000000000000 : ℚ) / (2221521999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (164353537 / 125000000000 : ℚ) + (1564761779 / 1000000000000 : ℚ) ≤
        (7710479983 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1166882591 / 1000000000000 : ℚ) +
        (9203388993 / 1000000000000000000 : ℚ) / (2221521999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (164353537 / 125000000000 : ℚ) + (1564761779 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7710479983 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12820]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12820 :
    2 * 160 < 12820 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (8593749 / 781250000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12820 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12821 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12821. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12821 : WorldParameters where
  hiddenCharge := (1166840347 / 1000000000000 : ℝ)
  frame := (311983882363 / 500000000000 : ℝ)
  moment := (920151373 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12821 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471297021319 / 1000000000000 : ℝ)
    root := (105180439 / 12500000000 : ℝ) }

noncomputable def scalar12821 : ScalarCertificate 12821 world12821 agent12821 where
  dimensionLo := 12821
  dimensionHi := 12821
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2221881099 / 1000000000000 : ℝ)
  frameLo := (311983882363 / 500000000000 : ℝ)
  frameHi := (1471297021319 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12821]
  agentFrame_pos := by norm_num only [agent12821]
  worldRadius := (2221881099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12821]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (26274621 / 20000000000 : ℝ)
  lowerTail := (781774663 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1541429087 / 200000000000 : ℝ)
  ledger := by
    have h : (1166840347 / 1000000000000 : ℚ) +
        (920151373 / 100000000000000000 : ℚ) / (2221881099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (26274621 / 20000000000 : ℚ) + (781774663 / 500000000000 : ℚ) ≤
        (1541429087 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1166840347 / 1000000000000 : ℚ) +
        (920151373 / 100000000000000000 : ℚ) / (2221881099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (26274621 / 20000000000 : ℚ) + (781774663 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1541429087 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12821]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12821 :
    2 * 160 < 12821 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999833 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12821 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12822 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12822. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12822 : WorldParameters where
  hiddenCharge := (583399057 / 500000000000 : ℝ)
  frame := (311977093587 / 500000000000 : ℝ)
  moment := (9199639001 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12822 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183908279433 / 125000000000 : ℝ)
    root := (8413777389 / 1000000000000 : ℝ) }

noncomputable def scalar12822 : ScalarCertificate 12822 world12822 agent12822 where
  dimensionLo := 12822
  dimensionHi := 12822
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2222240099 / 1000000000000 : ℝ)
  frameLo := (311977093587 / 500000000000 : ℝ)
  frameHi := (183908279433 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12822]
  agentFrame_pos := by norm_num only [agent12822]
  worldRadius := (2222240099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12822]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (164079343 / 125000000000 : ℝ)
  lowerTail := (390584463 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7703813629 / 1000000000000 : ℝ)
  ledger := by
    have h : (583399057 / 500000000000 : ℚ) +
        (9199639001 / 1000000000000000000 : ℚ) / (2222240099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (164079343 / 125000000000 : ℚ) + (390584463 / 250000000000 : ℚ) ≤
        (7703813629 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((583399057 / 500000000000 : ℚ) +
        (9199639001 / 1000000000000000000 : ℚ) / (2222240099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (164079343 / 125000000000 : ℚ) + (390584463 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7703813629 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12822]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12822 :
    2 * 160 < 12822 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499783 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12822 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12823 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12823. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12823 : WorldParameters where
  hiddenCharge := (1166755891 / 1000000000000 : ℝ)
  frame := (24957624471 / 40000000000 : ℝ)
  moment := (4598882403 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12823 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (45976108213 / 31250000000 : ℝ)
    root := (4206559927 / 500000000000 : ℝ) }

noncomputable def scalar12823 : ScalarCertificate 12823 world12823 agent12823 where
  dimensionLo := 12823
  dimensionHi := 12823
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2222599199 / 1000000000000 : ℝ)
  frameLo := (24957624471 / 40000000000 : ℝ)
  frameHi := (45976108213 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12823]
  agentFrame_pos := by norm_num only [agent12823]
  worldRadius := (2222599199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12823]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (655769783 / 500000000000 : ℝ)
  lowerTail := (780563777 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (962560577 / 125000000000 : ℝ)
  ledger := by
    have h : (1166755891 / 1000000000000 : ℚ) +
        (4598882403 / 500000000000000000 : ℚ) / (2222599199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (655769783 / 500000000000 : ℚ) + (780563777 / 500000000000 : ℚ) ≤
        (962560577 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1166755891 / 1000000000000 : ℚ) +
        (4598882403 / 500000000000000000 : ℚ) / (2222599199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (655769783 / 500000000000 : ℚ) + (780563777 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((962560577 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12823]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12823 :
    2 * 160 < 12823 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (171874953 / 15625000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12823 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12824 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12824. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12824 : WorldParameters where
  hiddenCharge := (14583921 / 12500000000 : ℝ)
  frame := (623927038529 / 1000000000000 : ℝ)
  moment := (1839178229 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12824 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294240941851 / 200000000000 : ℝ)
    root := (2103115629 / 250000000000 : ℝ) }

noncomputable def scalar12824 : ScalarCertificate 12824 world12824 agent12824 where
  dimensionLo := 12824
  dimensionHi := 12824
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2222958299 / 1000000000000 : ℝ)
  frameLo := (623927038529 / 1000000000000 : ℝ)
  frameHi := (294240941851 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12824]
  agentFrame_pos := by norm_num only [agent12824]
  worldRadius := (2222958299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12824]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1310445457 / 1000000000000 : ℝ)
  lowerTail := (779959187 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1539431689 / 200000000000 : ℝ)
  ledger := by
    have h : (14583921 / 12500000000 : ℚ) +
        (1839178229 / 200000000000000000 : ℚ) / (2222958299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1310445457 / 1000000000000 : ℚ) + (779959187 / 500000000000 : ℚ) ≤
        (1539431689 / 200000000000 : ℚ) := by norm_num only
    have hc : (((14583921 / 12500000000 : ℚ) +
        (1839178229 / 200000000000000000 : ℚ) / (2222958299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1310445457 / 1000000000000 : ℚ) + (779959187 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1539431689 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12824]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12824 :
    2 * 160 < 12824 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997163 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12824 {← IO.monoMsNow}" : IO Unit)
