import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12255 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12255. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12255 : WorldParameters where
  hiddenCharge := (47705729 / 40000000000 : ℝ)
  frame := (316007793057 / 500000000000 : ℝ)
  moment := (2588643079 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12255 : AgentParameters :=
  { agentLedgerParameters with
    charge := (377530547 / 200000000000 : ℝ)
    frame := (58352140973 / 40000000000 : ℝ)
    root := (8827585301 / 1000000000000 : ℝ) }

noncomputable def scalar12255 : ScalarCertificate 12255 world12255 agent12255 where
  dimensionLo := 12255
  dimensionHi := 12255
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2059086599 / 1000000000000 : ℝ)
  frameLo := (316007793057 / 500000000000 : ℝ)
  frameHi := (58352140973 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12255]
  agentFrame_pos := by norm_num only [agent12255]
  worldRadius := (2059086599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12255]
  retainedCharge := (377530547 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (125368543 / 62500000000 : ℝ)
  lowerTail := (572705053 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9819223493 / 1000000000000 : ℝ)
  ledger := by
    have h : (47705729 / 40000000000 : ℚ) +
        (2588643079 / 250000000000000000 : ℚ) / (2059086599 / 1000000000000 : ℚ) ^ 2 +
        (377530547 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (125368543 / 62500000000 : ℚ) + (572705053 / 250000000000 : ℚ) ≤
        (9819223493 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((47705729 / 40000000000 : ℚ) +
        (2588643079 / 250000000000000000 : ℚ) / (2059086599 / 1000000000000 : ℚ) ^ 2 +
        (377530547 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (125368543 / 62500000000 : ℚ) + (572705053 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9819223493 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12255]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12255 :
    2 * 160 < 12255 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997353 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12255 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12256 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12256. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12256 : WorldParameters where
  hiddenCharge := (238518813 / 200000000000 : ℝ)
  frame := (632000696269 / 1000000000000 : ℝ)
  moment := (10352361369 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12256 : AgentParameters :=
  { agentLedgerParameters with
    charge := (377381951 / 200000000000 : ℝ)
    frame := (364690630261 / 250000000000 : ℝ)
    root := (4413423557 / 500000000000 : ℝ) }

noncomputable def scalar12256 : ScalarCertificate 12256 world12256 agent12256 where
  dimensionLo := 12256
  dimensionHi := 12256
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2059441299 / 1000000000000 : ℝ)
  frameLo := (632000696269 / 1000000000000 : ℝ)
  frameHi := (364690630261 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12256]
  agentFrame_pos := by norm_num only [agent12256]
  worldRadius := (2059441299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12256]
  retainedCharge := (377381951 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (501029001 / 250000000000 : ℝ)
  lowerTail := (71528751 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9813388023 / 1000000000000 : ℝ)
  ledger := by
    have h : (238518813 / 200000000000 : ℚ) +
        (10352361369 / 1000000000000000000 : ℚ) / (2059441299 / 1000000000000 : ℚ) ^ 2 +
        (377381951 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (501029001 / 250000000000 : ℚ) + (71528751 / 31250000000 : ℚ) ≤
        (9813388023 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((238518813 / 200000000000 : ℚ) +
        (10352361369 / 1000000000000000000 : ℚ) / (2059441299 / 1000000000000 : ℚ) ^ 2 +
        (377381951 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (501029001 / 250000000000 : ℚ) + (71528751 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((9813388023 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12256]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12256 :
    2 * 160 < 12256 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994279 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12256 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12257 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12257. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12257 : WorldParameters where
  hiddenCharge := (596272459 / 500000000000 : ℝ)
  frame := (631985808919 / 1000000000000 : ℝ)
  moment := (10350151081 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12257 : AgentParameters :=
  { agentLedgerParameters with
    charge := (943083723 / 500000000000 : ℝ)
    frame := (1458721532689 / 1000000000000 : ℝ)
    root := (220652729 / 25000000000 : ℝ) }

noncomputable def scalar12257 : ScalarCertificate 12257 world12257 agent12257 where
  dimensionLo := 12257
  dimensionHi := 12257
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2059795899 / 1000000000000 : ℝ)
  frameLo := (631985808919 / 1000000000000 : ℝ)
  frameHi := (1458721532689 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12257]
  agentFrame_pos := by norm_num only [agent12257]
  worldRadius := (2059795899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12257]
  retainedCharge := (943083723 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2002336981 / 1000000000000 : ℝ)
  lowerTail := (2287021517 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9807557749 / 1000000000000 : ℝ)
  ledger := by
    have h : (596272459 / 500000000000 : ℚ) +
        (10350151081 / 1000000000000000000 : ℚ) / (2059795899 / 1000000000000 : ℚ) ^ 2 +
        (943083723 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2002336981 / 1000000000000 : ℚ) + (2287021517 / 1000000000000 : ℚ) ≤
        (9807557749 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((596272459 / 500000000000 : ℚ) +
        (10350151081 / 1000000000000000000 : ℚ) / (2059795899 / 1000000000000 : ℚ) ^ 2 +
        (943083723 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2002336981 / 1000000000000 : ℚ) + (2287021517 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9807557749 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12257]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12257 :
    2 * 160 < 12257 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (549999781 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12257 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12258 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12258. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12258 : WorldParameters where
  hiddenCharge := (238499157 / 200000000000 : ℝ)
  frame := (631970924063 / 1000000000000 : ℝ)
  moment := (10347941453 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12258 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1885425807 / 1000000000000 : ℝ)
    frame := (182335070641 / 125000000000 : ℝ)
    root := (8825371439 / 1000000000000 : ℝ) }

noncomputable def scalar12258 : ScalarCertificate 12258 world12258 agent12258 where
  dimensionLo := 12258
  dimensionHi := 12258
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2060150499 / 1000000000000 : ℝ)
  frameLo := (631970924063 / 1000000000000 : ℝ)
  frameHi := (182335070641 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12258]
  agentFrame_pos := by norm_num only [agent12258]
  worldRadius := (2060150499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12258]
  retainedCharge := (1885425807 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2000559767 / 1000000000000 : ℝ)
  lowerTail := (228512483 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9801732741 / 1000000000000 : ℝ)
  ledger := by
    have h : (238499157 / 200000000000 : ℚ) +
        (10347941453 / 1000000000000000000 : ℚ) / (2060150499 / 1000000000000 : ℚ) ^ 2 +
        (1885425807 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2000559767 / 1000000000000 : ℚ) + (228512483 / 100000000000 : ℚ) ≤
        (9801732741 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((238499157 / 200000000000 : ℚ) +
        (10347941453 / 1000000000000000000 : ℚ) / (2060150499 / 1000000000000 : ℚ) ^ 2 +
        (1885425807 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2000559767 / 1000000000000 : ℚ) + (228512483 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9801732741 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12258]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12258 :
    2 * 160 < 12258 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995349 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12258 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12259 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12259. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12259 : WorldParameters where
  hiddenCharge := (238489333 / 200000000000 : ℝ)
  frame := (631956041701 / 1000000000000 : ℝ)
  moment := (2586433121 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12259 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1884684837 / 1000000000000 : ℝ)
    frame := (58345584499 / 40000000000 : ℝ)
    root := (176492679 / 20000000000 : ℝ) }

noncomputable def scalar12259 : ScalarCertificate 12259 world12259 agent12259 where
  dimensionLo := 12259
  dimensionHi := 12259
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2060505199 / 1000000000000 : ℝ)
  frameLo := (631956041701 / 1000000000000 : ℝ)
  frameHi := (58345584499 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12259]
  agentFrame_pos := by norm_num only [agent12259]
  worldRadius := (2060505199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12259]
  retainedCharge := (1884684837 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1998784439 / 1000000000000 : ℝ)
  lowerTail := (2283230047 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4897956459 / 500000000000 : ℝ)
  ledger := by
    have h : (238489333 / 200000000000 : ℚ) +
        (2586433121 / 250000000000000000 : ℚ) / (2060505199 / 1000000000000 : ℚ) ^ 2 +
        (1884684837 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1998784439 / 1000000000000 : ℚ) + (2283230047 / 1000000000000 : ℚ) ≤
        (4897956459 / 500000000000 : ℚ) := by norm_num only
    have hc : (((238489333 / 200000000000 : ℚ) +
        (2586433121 / 250000000000000000 : ℚ) / (2060505199 / 1000000000000 : ℚ) ^ 2 +
        (1884684837 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1998784439 / 1000000000000 : ℚ) + (2283230047 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4897956459 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12259]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12259 :
    2 * 160 < 12259 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999443 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12259 {← IO.monoMsNow}" : IO Unit)
