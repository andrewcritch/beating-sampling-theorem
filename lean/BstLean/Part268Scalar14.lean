import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12700 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12700. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12700 : WorldParameters where
  hiddenCharge := (293008359 / 250000000000 : ℝ)
  frame := (312813354211 / 500000000000 : ℝ)
  moment := (4716177497 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12700 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (738036951259 / 500000000000 : ℝ)
    root := (8495505169 / 1000000000000 : ℝ) }

noncomputable def scalar12700 : ScalarCertificate 12700 world12700 agent12700 where
  dimensionLo := 12700
  dimensionHi := 12700
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2177187699 / 1000000000000 : ℝ)
  frameLo := (312813354211 / 500000000000 : ℝ)
  frameHi := (738036951259 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12700]
  agentFrame_pos := by norm_num only [agent12700]
  worldRadius := (2177187699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12700]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (364400987 / 250000000000 : ℝ)
  lowerTail := (861272873 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4070608013 / 500000000000 : ℝ)
  ledger := by
    have h : (293008359 / 250000000000 : ℚ) +
        (4716177497 / 500000000000000000 : ℚ) / (2177187699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (364400987 / 250000000000 : ℚ) + (861272873 / 500000000000 : ℚ) ≤
        (4070608013 / 500000000000 : ℚ) := by norm_num only
    have hc : (((293008359 / 250000000000 : ℚ) +
        (4716177497 / 500000000000000000 : ℚ) / (2177187699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (364400987 / 250000000000 : ℚ) + (861272873 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4070608013 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12700]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12700 :
    2 * 160 < 12700 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999017 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12700 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12701 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12701. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12701 : WorldParameters where
  hiddenCharge := (234397967 / 200000000000 : ℝ)
  frame := (125122573249 / 200000000000 : ℝ)
  moment := (9430414221 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12701 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1476041687583 / 1000000000000 : ℝ)
    root := (530926423 / 62500000000 : ℝ) }

noncomputable def scalar12701 : ScalarCertificate 12701 world12701 agent12701 where
  dimensionLo := 12701
  dimensionHi := 12701
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2177544999 / 1000000000000 : ℝ)
  frameLo := (125122573249 / 200000000000 : ℝ)
  frameHi := (1476041687583 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12701]
  agentFrame_pos := by norm_num only [agent12701]
  worldRadius := (2177544999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12701]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (728184703 / 500000000000 : ℝ)
  lowerTail := (1721190881 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8137520757 / 1000000000000 : ℝ)
  ledger := by
    have h : (234397967 / 200000000000 : ℚ) +
        (9430414221 / 1000000000000000000 : ℚ) / (2177544999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (728184703 / 500000000000 : ℚ) + (1721190881 / 1000000000000 : ℚ) ≤
        (8137520757 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((234397967 / 200000000000 : ℚ) +
        (9430414221 / 1000000000000000000 : ℚ) / (2177544999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (728184703 / 500000000000 : ℚ) + (1721190881 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8137520757 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12701]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12701 :
    2 * 160 < 12701 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999841 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12701 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12702 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12702. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12702 : WorldParameters where
  hiddenCharge := (234389249 / 200000000000 : ℝ)
  frame := (62559902629 / 100000000000 : ℝ)
  moment := (9428474007 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12702 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184501186601 / 125000000000 : ℝ)
    root := (424707029 / 50000000000 : ℝ) }

noncomputable def scalar12702 : ScalarCertificate 12702 world12702 agent12702 where
  dimensionLo := 12702
  dimensionHi := 12702
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2177902299 / 1000000000000 : ℝ)
  frameLo := (62559902629 / 100000000000 : ℝ)
  frameHi := (184501186601 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12702]
  agentFrame_pos := by norm_num only [agent12702]
  worldRadius := (2177902299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12702]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1455136091 / 1000000000000 : ℝ)
  lowerTail := (214979661 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (254182147 / 31250000000 : ℝ)
  ledger := by
    have h : (234389249 / 200000000000 : ℚ) +
        (9428474007 / 1000000000000000000 : ℚ) / (2177902299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1455136091 / 1000000000000 : ℚ) + (214979661 / 125000000000 : ℚ) ≤
        (254182147 / 31250000000 : ℚ) := by norm_num only
    have hc : (((234389249 / 200000000000 : ℚ) +
        (9428474007 / 1000000000000000000 : ℚ) / (2177902299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1455136091 / 1000000000000 : ℚ) + (214979661 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((254182147 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12702]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12702 :
    2 * 160 < 12702 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999557 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12702 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12703 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12703. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12703 : WorldParameters where
  hiddenCharge := (1171902667 / 1000000000000 : ℝ)
  frame := (312792594277 / 500000000000 : ℝ)
  moment := (188530687 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12703 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295195463637 / 200000000000 : ℝ)
    root := (2123364651 / 250000000000 : ℝ) }

noncomputable def scalar12703 : ScalarCertificate 12703 world12703 agent12703 where
  dimensionLo := 12703
  dimensionHi := 12703
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2178259599 / 1000000000000 : ℝ)
  frameLo := (312792594277 / 500000000000 : ℝ)
  frameHi := (295195463637 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12703]
  agentFrame_pos := by norm_num only [agent12703]
  worldRadius := (2178259599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12703]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1453904001 / 1000000000000 : ℝ)
  lowerTail := (859242483 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2032534967 / 250000000000 : ℝ)
  ledger := by
    have h : (1171902667 / 1000000000000 : ℚ) +
        (188530687 / 20000000000000000 : ℚ) / (2178259599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1453904001 / 1000000000000 : ℚ) + (859242483 / 500000000000 : ℚ) ≤
        (2032534967 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1171902667 / 1000000000000 : ℚ) +
        (188530687 / 20000000000000000 : ℚ) / (2178259599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1453904001 / 1000000000000 : ℚ) + (859242483 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2032534967 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12703]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12703 :
    2 * 160 < 12703 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997199 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12703 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12704 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12704. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12704 : WorldParameters where
  hiddenCharge := (1171859101 / 1000000000000 : ℝ)
  frame := (312785676519 / 500000000000 : ℝ)
  moment := (37698381 / 4000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12704 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368986289447 / 250000000000 : ℝ)
    root := (8492776841 / 1000000000000 : ℝ) }

noncomputable def scalar12704 : ScalarCertificate 12704 world12704 agent12704 where
  dimensionLo := 12704
  dimensionHi := 12704
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2178616899 / 1000000000000 : ℝ)
  frameLo := (312785676519 / 500000000000 : ℝ)
  frameHi := (368986289447 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12704]
  agentFrame_pos := by norm_num only [agent12704]
  worldRadius := (2178616899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12704]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (145267311 / 100000000000 : ℝ)
  lowerTail := (1717133881 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1625290837 / 200000000000 : ℝ)
  ledger := by
    have h : (1171859101 / 1000000000000 : ℚ) +
        (37698381 / 4000000000000000 : ℚ) / (2178616899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (145267311 / 100000000000 : ℚ) + (1717133881 / 1000000000000 : ℚ) ≤
        (1625290837 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1171859101 / 1000000000000 : ℚ) +
        (37698381 / 4000000000000000 : ℚ) / (2178616899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (145267311 / 100000000000 : ℚ) + (1717133881 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1625290837 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12704]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12704 :
    2 * 160 < 12704 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999543 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12704 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12705 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12705. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12705 : WorldParameters where
  hiddenCharge := (585907773 / 500000000000 : ℝ)
  frame := (625557519741 / 1000000000000 : ℝ)
  moment := (2355664177 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12705 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737956508761 / 500000000000 : ℝ)
    root := (849209529 / 100000000000 : ℝ) }

noncomputable def scalar12705 : ScalarCertificate 12705 world12705 agent12705 where
  dimensionLo := 12705
  dimensionHi := 12705
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2178974299 / 1000000000000 : ℝ)
  frameLo := (625557519741 / 1000000000000 : ℝ)
  frameHi := (737956508761 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12705]
  agentFrame_pos := by norm_num only [agent12705]
  worldRadius := (2178974299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12705]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1451443529 / 1000000000000 : ℝ)
  lowerTail := (10723651 / 6250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (812277171 / 100000000000 : ℝ)
  ledger := by
    have h : (585907773 / 500000000000 : ℚ) +
        (2355664177 / 250000000000000000 : ℚ) / (2178974299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1451443529 / 1000000000000 : ℚ) + (10723651 / 6250000000 : ℚ) ≤
        (812277171 / 100000000000 : ℚ) := by norm_num only
    have hc : (((585907773 / 500000000000 : ℚ) +
        (2355664177 / 250000000000000000 : ℚ) / (2178974299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1451443529 / 1000000000000 : ℚ) + (10723651 / 6250000000 : ℚ) : ℚ) : ℝ) ≤
        ((812277171 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12705]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12705 :
    2 * 160 < 12705 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999311 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12705 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12706 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12706. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12706 : WorldParameters where
  hiddenCharge := (585886001 / 500000000000 : ℝ)
  frame := (312771844331 / 500000000000 : ℝ)
  moment := (9420718723 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12706 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737940448689 / 500000000000 : ℝ)
    root := (8491413951 / 1000000000000 : ℝ) }

noncomputable def scalar12706 : ScalarCertificate 12706 world12706 agent12706 where
  dimensionLo := 12706
  dimensionHi := 12706
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2179331499 / 1000000000000 : ℝ)
  frameLo := (312771844331 / 500000000000 : ℝ)
  frameHi := (737940448689 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12706]
  agentFrame_pos := by norm_num only [agent12706]
  worldRadius := (2179331499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12706]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (362553749 / 250000000000 : ℝ)
  lowerTail := (342887103 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (202977311 / 25000000000 : ℝ)
  ledger := by
    have h : (585886001 / 500000000000 : ℚ) +
        (9420718723 / 1000000000000000000 : ℚ) / (2179331499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (362553749 / 250000000000 : ℚ) + (342887103 / 200000000000 : ℚ) ≤
        (202977311 / 25000000000 : ℚ) := by norm_num only
    have hc : (((585886001 / 500000000000 : ℚ) +
        (9420718723 / 1000000000000000000 : ℚ) / (2179331499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (362553749 / 250000000000 : ℚ) + (342887103 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((202977311 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12706]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12706 :
    2 * 160 < 12706 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997889 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12706 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12707 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12707. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12707 : WorldParameters where
  hiddenCharge := (117172847 / 100000000000 : ℝ)
  frame := (625529859801 / 1000000000000 : ℝ)
  moment := (1883756259 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12707 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475848791431 / 1000000000000 : ℝ)
    root := (1061341603 / 125000000000 : ℝ) }

noncomputable def scalar12707 : ScalarCertificate 12707 world12707 agent12707 where
  dimensionLo := 12707
  dimensionHi := 12707
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2179688899 / 1000000000000 : ℝ)
  frameLo := (625529859801 / 1000000000000 : ℝ)
  frameHi := (1475848791431 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12707]
  agentFrame_pos := by norm_num only [agent12707]
  worldRadius := (2179688899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12707]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (144898783 / 100000000000 : ℝ)
  lowerTail := (1713088293 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4057708157 / 500000000000 : ℝ)
  ledger := by
    have h : (117172847 / 100000000000 : ℚ) +
        (1883756259 / 200000000000000000 : ℚ) / (2179688899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (144898783 / 100000000000 : ℚ) + (1713088293 / 1000000000000 : ℚ) ≤
        (4057708157 / 500000000000 : ℚ) := by norm_num only
    have hc : (((117172847 / 100000000000 : ℚ) +
        (1883756259 / 200000000000000000 : ℚ) / (2179688899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (144898783 / 100000000000 : ℚ) + (1713088293 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4057708157 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12707]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12707 :
    2 * 160 < 12707 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999333 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12707 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12708 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12708. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12708 : WorldParameters where
  hiddenCharge := (23433699 / 20000000000 : ℝ)
  frame := (625516033157 / 1000000000000 : ℝ)
  moment := (1177105553 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12708 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475816705587 / 1000000000000 : ℝ)
    root := (2122512977 / 250000000000 : ℝ) }

noncomputable def scalar12708 : ScalarCertificate 12708 world12708 agent12708 where
  dimensionLo := 12708
  dimensionHi := 12708
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2180046199 / 1000000000000 : ℝ)
  frameLo := (625516033157 / 1000000000000 : ℝ)
  frameHi := (1475816705587 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12708]
  agentFrame_pos := by norm_num only [agent12708]
  worldRadius := (2180046199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12708]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (361940449 / 250000000000 : ℝ)
  lowerTail := (10698389 / 6250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1622348677 / 200000000000 : ℝ)
  ledger := by
    have h : (23433699 / 20000000000 : ℚ) +
        (1177105553 / 125000000000000000 : ℚ) / (2180046199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (361940449 / 250000000000 : ℚ) + (10698389 / 6250000000 : ℚ) ≤
        (1622348677 / 200000000000 : ℚ) := by norm_num only
    have hc : (((23433699 / 20000000000 : ℚ) +
        (1177105553 / 125000000000000000 : ℚ) / (2180046199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (361940449 / 250000000000 : ℚ) + (10698389 / 6250000000 : ℚ) : ℚ) : ℝ) ≤
        ((1622348677 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12708]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12708 :
    2 * 160 < 12708 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997561 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12708 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12709 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12709. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12709 : WorldParameters where
  hiddenCharge := (1171641441 / 1000000000000 : ℝ)
  frame := (62550220873 / 100000000000 : ℝ)
  moment := (9414908109 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12709 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475784633921 / 1000000000000 : ℝ)
    root := (1697874241 / 200000000000 : ℝ) }

noncomputable def scalar12709 : ScalarCertificate 12709 world12709 agent12709 where
  dimensionLo := 12709
  dimensionHi := 12709
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2180403599 / 1000000000000 : ℝ)
  frameLo := (62550220873 / 100000000000 : ℝ)
  frameHi := (1475784633921 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12709]
  agentFrame_pos := by norm_num only [agent12709]
  worldRadius := (2180403599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12709]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (18081713 / 12500000000 : ℝ)
  lowerTail := (213799689 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4054036797 / 500000000000 : ℝ)
  ledger := by
    have h : (1171641441 / 1000000000000 : ℚ) +
        (9414908109 / 1000000000000000000 : ℚ) / (2180403599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (18081713 / 12500000000 : ℚ) + (213799689 / 125000000000 : ℚ) ≤
        (4054036797 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1171641441 / 1000000000000 : ℚ) +
        (9414908109 / 1000000000000000000 : ℚ) / (2180403599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (18081713 / 12500000000 : ℚ) + (213799689 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4054036797 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12709]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12709 :
    2 * 160 < 12709 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499829 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12709 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12710 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12710. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12710 : WorldParameters where
  hiddenCharge := (146449743 / 125000000000 : ℝ)
  frame := (625488386519 / 1000000000000 : ℝ)
  moment := (188259447 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12710 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368917840437 / 250000000000 : ℝ)
    root := (4244345323 / 500000000000 : ℝ) }

noncomputable def scalar12710 : ScalarCertificate 12710 world12710 agent12710 where
  dimensionLo := 12710
  dimensionHi := 12710
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2180873299 / 1000000000000 : ℝ)
  frameLo := (625488386519 / 1000000000000 : ℝ)
  frameHi := (368917840437 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12710]
  agentFrame_pos := by norm_num only [agent12710]
  worldRadius := (2180873299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12710]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1445052493 / 1000000000000 : ℝ)
  lowerTail := (854358939 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4051802993 / 500000000000 : ℝ)
  ledger := by
    have h : (146449743 / 125000000000 : ℚ) +
        (188259447 / 20000000000000000 : ℚ) / (2180873299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1445052493 / 1000000000000 : ℚ) + (854358939 / 500000000000 : ℚ) ≤
        (4051802993 / 500000000000 : ℚ) := by norm_num only
    have hc : (((146449743 / 125000000000 : ℚ) +
        (188259447 / 20000000000000000 : ℚ) / (2180873299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1445052493 / 1000000000000 : ℚ) + (854358939 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4051802993 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12710]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12710 :
    2 * 160 < 12710 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998463 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12710 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12711 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12711. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12711 : WorldParameters where
  hiddenCharge := (585777229 / 500000000000 : ℝ)
  frame := (625474566523 / 1000000000000 : ℝ)
  moment := (2352759287 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12711 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475639331193 / 1000000000000 : ℝ)
    root := (1697602073 / 200000000000 : ℝ) }

noncomputable def scalar12711 : ScalarCertificate 12711 world12711 agent12711 where
  dimensionLo := 12711
  dimensionHi := 12711
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2181230799 / 1000000000000 : ℝ)
  frameLo := (625474566523 / 1000000000000 : ℝ)
  frameHi := (1475639331193 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12711]
  agentFrame_pos := by norm_num only [agent12711]
  worldRadius := (2181230799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12711]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1443830437 / 1000000000000 : ℝ)
  lowerTail := (1707375983 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1619988623 / 200000000000 : ℝ)
  ledger := by
    have h : (585777229 / 500000000000 : ℚ) +
        (2352759287 / 250000000000000000 : ℚ) / (2181230799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1443830437 / 1000000000000 : ℚ) + (1707375983 / 1000000000000 : ℚ) ≤
        (1619988623 / 200000000000 : ℚ) := by norm_num only
    have hc : (((585777229 / 500000000000 : ℚ) +
        (2352759287 / 250000000000000000 : ℚ) / (2181230799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1443830437 / 1000000000000 : ℚ) + (1707375983 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1619988623 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12711]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12711 :
    2 * 160 < 12711 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994083 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12711 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12712 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12712. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12712 : WorldParameters where
  hiddenCharge := (1171510983 / 1000000000000 : ℝ)
  frame := (625460748743 / 1000000000000 : ℝ)
  moment := (9409102501 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12712 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475607314787 / 1000000000000 : ℝ)
    root := (1697466059 / 200000000000 : ℝ) }

noncomputable def scalar12712 : ScalarCertificate 12712 world12712 agent12712 where
  dimensionLo := 12712
  dimensionHi := 12712
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2181588099 / 1000000000000 : ℝ)
  frameLo := (625460748743 / 1000000000000 : ℝ)
  frameHi := (1475607314787 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12712]
  agentFrame_pos := by norm_num only [agent12712]
  worldRadius := (2181588099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12712]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (721304697 / 500000000000 : ℝ)
  lowerTail := (426508781 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2024070843 / 250000000000 : ℝ)
  ledger := by
    have h : (1171510983 / 1000000000000 : ℚ) +
        (9409102501 / 1000000000000000000 : ℚ) / (2181588099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (721304697 / 500000000000 : ℚ) + (426508781 / 250000000000 : ℚ) ≤
        (2024070843 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1171510983 / 1000000000000 : ℚ) +
        (9409102501 / 1000000000000000000 : ℚ) / (2181588099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (721304697 / 500000000000 : ℚ) + (426508781 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2024070843 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12712]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12712 :
    2 * 160 < 12712 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998713 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12712 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12713 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12713. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12713 : WorldParameters where
  hiddenCharge := (915209 / 781250000 : ℝ)
  frame := (78180866647 / 125000000000 : ℝ)
  moment := (9407168411 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12713 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475575312521 / 1000000000000 : ℝ)
    root := (8486650437 / 1000000000000 : ℝ) }

noncomputable def scalar12713 : ScalarCertificate 12713 world12713 agent12713 where
  dimensionLo := 12713
  dimensionHi := 12713
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2181945599 / 1000000000000 : ℝ)
  frameLo := (78180866647 / 125000000000 : ℝ)
  frameHi := (1475575312521 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12713]
  agentFrame_pos := by norm_num only [agent12713]
  worldRadius := (2181945599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12713]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (144138971 / 100000000000 : ℝ)
  lowerTail := (1704695679 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (126447293 / 15625000000 : ℝ)
  ledger := by
    have h : (915209 / 781250000 : ℚ) +
        (9407168411 / 1000000000000000000 : ℚ) / (2181945599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (144138971 / 100000000000 : ℚ) + (1704695679 / 1000000000000 : ℚ) ≤
        (126447293 / 15625000000 : ℚ) := by norm_num only
    have hc : (((915209 / 781250000 : ℚ) +
        (9407168411 / 1000000000000000000 : ℚ) / (2181945599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (144138971 / 100000000000 : ℚ) + (1704695679 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((126447293 / 15625000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12713]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12713 :
    2 * 160 < 12713 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999607 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12713 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12714 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12714. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12714 : WorldParameters where
  hiddenCharge := (1171424069 / 1000000000000 : ℝ)
  frame := (39089569989 / 62500000000 : ℝ)
  moment := (75241879 / 8000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12714 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475543336213 / 1000000000000 : ℝ)
    root := (8485970789 / 1000000000000 : ℝ) }

noncomputable def scalar12714 : ScalarCertificate 12714 world12714 agent12714 where
  dimensionLo := 12714
  dimensionHi := 12714
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2182302899 / 1000000000000 : ℝ)
  frameLo := (39089569989 / 62500000000 : ℝ)
  frameHi := (1475543336213 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12714]
  agentFrame_pos := by norm_num only [agent12714]
  worldRadius := (2182302899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12714]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1440171089 / 1000000000000 : ℝ)
  lowerTail := (1703357333 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1011121671 / 125000000000 : ℝ)
  ledger := by
    have h : (1171424069 / 1000000000000 : ℚ) +
        (75241879 / 8000000000000000 : ℚ) / (2182302899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1440171089 / 1000000000000 : ℚ) + (1703357333 / 1000000000000 : ℚ) ≤
        (1011121671 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1171424069 / 1000000000000 : ℚ) +
        (75241879 / 8000000000000000 : ℚ) / (2182302899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1440171089 / 1000000000000 : ℚ) + (1703357333 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1011121671 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12714]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12714 :
    2 * 160 < 12714 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (343749839 / 31250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12714 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12715 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12715. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12715 : WorldParameters where
  hiddenCharge := (1171380629 / 1000000000000 : ℝ)
  frame := (156354827171 / 250000000000 : ℝ)
  moment := (1880660379 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12715 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (59020454961 / 40000000000 : ℝ)
    root := (8485291353 / 1000000000000 : ℝ) }

noncomputable def scalar12715 : ScalarCertificate 12715 world12715 agent12715 where
  dimensionLo := 12715
  dimensionHi := 12715
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2182660199 / 1000000000000 : ℝ)
  frameLo := (156354827171 / 250000000000 : ℝ)
  frameHi := (59020454961 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12715]
  agentFrame_pos := by norm_num only [agent12715]
  worldRadius := (2182660199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12715]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1438953651 / 1000000000000 : ℝ)
  lowerTail := (106376263 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (80853231 / 10000000000 : ℝ)
  ledger := by
    have h : (1171380629 / 1000000000000 : ℚ) +
        (1880660379 / 200000000000000000 : ℚ) / (2182660199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1438953651 / 1000000000000 : ℚ) + (106376263 / 62500000000 : ℚ) ≤
        (80853231 / 10000000000 : ℚ) := by norm_num only
    have hc : (((1171380629 / 1000000000000 : ℚ) +
        (1880660379 / 200000000000000000 : ℚ) / (2182660199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1438953651 / 1000000000000 : ℚ) + (106376263 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((80853231 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12715]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12715 :
    2 * 160 < 12715 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999253 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12715 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12716 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12716. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12716 : WorldParameters where
  hiddenCharge := (1171337201 / 1000000000000 : ℝ)
  frame := (312702749879 / 500000000000 : ℝ)
  moment := (940136947 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12716 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475479425949 / 1000000000000 : ℝ)
    root := (8484612127 / 1000000000000 : ℝ) }

noncomputable def scalar12716 : ScalarCertificate 12716 world12716 agent12716 where
  dimensionLo := 12716
  dimensionHi := 12716
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2183017499 / 1000000000000 : ℝ)
  frameLo := (312702749879 / 500000000000 : ℝ)
  frameHi := (1475479425949 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12716]
  agentFrame_pos := by norm_num only [agent12716]
  worldRadius := (2183017499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12716]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (718868697 / 500000000000 : ℝ)
  lowerTail := (340136861 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1616335189 / 200000000000 : ℝ)
  ledger := by
    have h : (1171337201 / 1000000000000 : ℚ) +
        (940136947 / 100000000000000000 : ℚ) / (2183017499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (718868697 / 500000000000 : ℚ) + (340136861 / 200000000000 : ℚ) ≤
        (1616335189 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1171337201 / 1000000000000 : ℚ) +
        (940136947 / 100000000000000000 : ℚ) / (2183017499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (718868697 / 500000000000 : ℚ) + (340136861 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1616335189 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12716]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12716 :
    2 * 160 < 12716 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996723 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12716 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12717 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12717. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12717 : WorldParameters where
  hiddenCharge := (146411723 / 125000000000 : ℝ)
  frame := (625391693043 / 1000000000000 : ℝ)
  moment := (11749297 / 1250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12717 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46107734309 / 31250000000 : ℝ)
    root := (8483933111 / 1000000000000 : ℝ) }

noncomputable def scalar12717 : ScalarCertificate 12717 world12717 agent12717 where
  dimensionLo := 12717
  dimensionHi := 12717
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2183374999 / 1000000000000 : ℝ)
  frameLo := (625391693043 / 1000000000000 : ℝ)
  frameHi := (46107734309 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12717]
  agentFrame_pos := by norm_num only [agent12717]
  worldRadius := (2183374999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12717]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1436522517 / 1000000000000 : ℝ)
  lowerTail := (1699349841 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (201950799 / 25000000000 : ℝ)
  ledger := by
    have h : (146411723 / 125000000000 : ℚ) +
        (11749297 / 1250000000000000 : ℚ) / (2183374999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1436522517 / 1000000000000 : ℚ) + (1699349841 / 1000000000000 : ℚ) ≤
        (201950799 / 25000000000 : ℚ) := by norm_num only
    have hc : (((146411723 / 125000000000 : ℚ) +
        (11749297 / 1250000000000000 : ℚ) / (2183374999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1436522517 / 1000000000000 : ℚ) + (1699349841 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((201950799 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12717]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12717 :
    2 * 160 < 12717 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996767 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12717 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12718 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12718. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12718 : WorldParameters where
  hiddenCharge := (585625189 / 500000000000 : ℝ)
  frame := (31268894427 / 50000000000 : ℝ)
  moment := (1879501257 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12718 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475415589833 / 1000000000000 : ℝ)
    root := (8483254239 / 1000000000000 : ℝ) }

noncomputable def scalar12718 : ScalarCertificate 12718 world12718 agent12718 where
  dimensionLo := 12718
  dimensionHi := 12718
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2183732399 / 1000000000000 : ℝ)
  frameLo := (31268894427 / 50000000000 : ℝ)
  frameHi := (1475415589833 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12718]
  agentFrame_pos := by norm_num only [agent12718]
  worldRadius := (2183732399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12718]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1435308701 / 1000000000000 : ℝ)
  lowerTail := (424504119 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (504649439 / 62500000000 : ℝ)
  ledger := by
    have h : (585625189 / 500000000000 : ℚ) +
        (1879501257 / 200000000000000000 : ℚ) / (2183732399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1435308701 / 1000000000000 : ℚ) + (424504119 / 250000000000 : ℚ) ≤
        (504649439 / 62500000000 : ℚ) := by norm_num only
    have hc : (((585625189 / 500000000000 : ℚ) +
        (1879501257 / 200000000000000000 : ℚ) / (2183732399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1435308701 / 1000000000000 : ℚ) + (424504119 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((504649439 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12718]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12718 :
    2 * 160 < 12718 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999413 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12718 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12719 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12719. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12719 : WorldParameters where
  hiddenCharge := (146400873 / 125000000000 : ℝ)
  frame := (78170510781 / 125000000000 : ℝ)
  moment := (2348893881 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12719 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475383695861 / 1000000000000 : ℝ)
    root := (1696515129 / 200000000000 : ℝ) }

noncomputable def scalar12719 : ScalarCertificate 12719 world12719 agent12719 where
  dimensionLo := 12719
  dimensionHi := 12719
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2184089899 / 1000000000000 : ℝ)
  frameLo := (78170510781 / 125000000000 : ℝ)
  frameHi := (1475383695861 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12719]
  agentFrame_pos := by norm_num only [agent12719]
  worldRadius := (2184089899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12719]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (286819241 / 200000000000 : ℝ)
  lowerTail := (5302139 / 3125000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8070753307 / 1000000000000 : ℝ)
  ledger := by
    have h : (146400873 / 125000000000 : ℚ) +
        (2348893881 / 250000000000000000 : ℚ) / (2184089899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (286819241 / 200000000000 : ℚ) + (5302139 / 3125000000 : ℚ) ≤
        (8070753307 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((146400873 / 125000000000 : ℚ) +
        (2348893881 / 250000000000000000 : ℚ) / (2184089899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (286819241 / 200000000000 : ℚ) + (5302139 / 3125000000 : ℚ) : ℚ) : ℝ) ≤
        ((8070753307 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12719]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12719 :
    2 * 160 < 12719 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994947 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12719 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12720 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12720. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12720 : WorldParameters where
  hiddenCharge := (585581801 / 500000000000 : ℝ)
  frame := (625350286167 / 1000000000000 : ℝ)
  moment := (9393645317 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12720 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737635356307 / 500000000000 : ℝ)
    root := (424094863 / 50000000000 : ℝ) }

noncomputable def scalar12720 : ScalarCertificate 12720 world12720 agent12720 where
  dimensionLo := 12720
  dimensionHi := 12720
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2184559899 / 1000000000000 : ℝ)
  frameLo := (625350286167 / 1000000000000 : ℝ)
  frameHi := (737635356307 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12720]
  agentFrame_pos := by norm_num only [agent12720]
  worldRadius := (2184559899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12720]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1432626419 / 1000000000000 : ℝ)
  lowerTail := (21187757 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8066324337 / 1000000000000 : ℝ)
  ledger := by
    have h : (585581801 / 500000000000 : ℚ) +
        (9393645317 / 1000000000000000000 : ℚ) / (2184559899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1432626419 / 1000000000000 : ℚ) + (21187757 / 12500000000 : ℚ) ≤
        (8066324337 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((585581801 / 500000000000 : ℚ) +
        (9393645317 / 1000000000000000000 : ℚ) / (2184559899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1432626419 / 1000000000000 : ℚ) + (21187757 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((8066324337 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12720]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12720 :
    2 * 160 < 12720 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999839 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12720 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12721 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12721. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12721 : WorldParameters where
  hiddenCharge := (1171120231 / 1000000000000 : ℝ)
  frame := (125067297659 / 200000000000 : ℝ)
  moment := (586982229 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12721 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475238859553 / 1000000000000 : ℝ)
    root := (1696243817 / 200000000000 : ℝ) }

noncomputable def scalar12721 : ScalarCertificate 12721 world12721 agent12721 where
  dimensionLo := 12721
  dimensionHi := 12721
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2184917199 / 1000000000000 : ℝ)
  frameLo := (125067297659 / 200000000000 : ℝ)
  frameHi := (1475238859553 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12721]
  agentFrame_pos := by norm_num only [agent12721]
  worldRadius := (2184917199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12721]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (715708167 / 500000000000 : ℝ)
  lowerTail := (1693691083 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8062693469 / 1000000000000 : ℝ)
  ledger := by
    have h : (1171120231 / 1000000000000 : ℚ) +
        (586982229 / 62500000000000000 : ℚ) / (2184917199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (715708167 / 500000000000 : ℚ) + (1693691083 / 1000000000000 : ℚ) ≤
        (8062693469 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1171120231 / 1000000000000 : ℚ) +
        (586982229 / 62500000000000000 : ℚ) / (2184917199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (715708167 / 500000000000 : ℚ) + (1693691083 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8062693469 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12721]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12721 :
    2 * 160 < 12721 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (343749829 / 31250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12721 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12722 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12722. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12722 : WorldParameters where
  hiddenCharge := (1171076871 / 1000000000000 : ℝ)
  frame := (78165336579 / 125000000000 : ℝ)
  moment := (4694893283 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12722 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368801753659 / 250000000000 : ℝ)
    root := (26501691 / 3125000000 : ℝ) }

noncomputable def scalar12722 : ScalarCertificate 12722 world12722 agent12722 where
  dimensionLo := 12722
  dimensionHi := 12722
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2185274699 / 1000000000000 : ℝ)
  frameLo := (78165336579 / 125000000000 : ℝ)
  frameHi := (368801753659 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12722]
  agentFrame_pos := by norm_num only [agent12722]
  worldRadius := (2185274699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12722]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1430207569 / 1000000000000 : ℝ)
  lowerTail := (846181487 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8059065637 / 1000000000000 : ℝ)
  ledger := by
    have h : (1171076871 / 1000000000000 : ℚ) +
        (4694893283 / 500000000000000000 : ℚ) / (2185274699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1430207569 / 1000000000000 : ℚ) + (846181487 / 500000000000 : ℚ) ≤
        (8059065637 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1171076871 / 1000000000000 : ℚ) +
        (4694893283 / 500000000000000000 : ℚ) / (2185274699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1430207569 / 1000000000000 : ℚ) + (846181487 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8059065637 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12722]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12722 :
    2 * 160 < 12722 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999409 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12722 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12723 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12723. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12723 : WorldParameters where
  hiddenCharge := (1171033523 / 1000000000000 : ℝ)
  frame := (625308899179 / 1000000000000 : ℝ)
  moment := (469392901 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12723 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737587597793 / 500000000000 : ℝ)
    root := (4239931649 / 500000000000 : ℝ) }

noncomputable def scalar12723 : ScalarCertificate 12723 world12723 agent12723 where
  dimensionLo := 12723
  dimensionHi := 12723
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2185632199 / 1000000000000 : ℝ)
  frameLo := (625308899179 / 1000000000000 : ℝ)
  frameHi := (737587597793 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12723]
  agentFrame_pos := by norm_num only [agent12723]
  worldRadius := (2185632199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12723]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (142899997 / 100000000000 : ℝ)
  lowerTail := (422759021 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4027720449 / 500000000000 : ℝ)
  ledger := by
    have h : (1171033523 / 1000000000000 : ℚ) +
        (469392901 / 50000000000000000 : ℚ) / (2185632199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (142899997 / 100000000000 : ℚ) + (422759021 / 250000000000 : ℚ) ≤
        (4027720449 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1171033523 / 1000000000000 : ℚ) +
        (469392901 / 50000000000000000 : ℚ) / (2185632199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (142899997 / 100000000000 : ℚ) + (422759021 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4027720449 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12723]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12723 :
    2 * 160 < 12723 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995323 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12723 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12724 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12724. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12724 : WorldParameters where
  hiddenCharge := (585495093 / 500000000000 : ℝ)
  frame := (625295107933 / 1000000000000 : ℝ)
  moment := (9385930029 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12724 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475143390573 / 1000000000000 : ℝ)
    root := (1059898219 / 125000000000 : ℝ) }

noncomputable def scalar12724 : ScalarCertificate 12724 world12724 agent12724 where
  dimensionLo := 12724
  dimensionHi := 12724
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2185989599 / 1000000000000 : ℝ)
  frameLo := (625295107933 / 1000000000000 : ℝ)
  frameHi := (1475143390573 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12724]
  agentFrame_pos := by norm_num only [agent12724]
  worldRadius := (2185989599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12724]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (178474189 / 125000000000 : ℝ)
  lowerTail := (844855183 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4025909679 / 500000000000 : ℝ)
  ledger := by
    have h : (585495093 / 500000000000 : ℚ) +
        (9385930029 / 1000000000000000000 : ℚ) / (2185989599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (178474189 / 125000000000 : ℚ) + (844855183 / 500000000000 : ℚ) ≤
        (4025909679 / 500000000000 : ℚ) := by norm_num only
    have hc : (((585495093 / 500000000000 : ℚ) +
        (9385930029 / 1000000000000000000 : ℚ) / (2185989599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (178474189 / 125000000000 : ℚ) + (844855183 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4025909679 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12724]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12724 :
    2 * 160 < 12724 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499661 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12724 {← IO.monoMsNow}" : IO Unit)
