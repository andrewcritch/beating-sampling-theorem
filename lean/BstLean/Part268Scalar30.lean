import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13100 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13100. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13100 : WorldParameters where
  hiddenCharge := (1155473327 / 1000000000000 : ℝ)
  frame := (620261227429 / 1000000000000 : ℝ)
  moment := (8698484587 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13100 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460825653583 / 1000000000000 : ℝ)
    root := (8238109007 / 1000000000000 : ℝ) }

noncomputable def scalar13100 : ScalarCertificate 13100 world13100 agent13100 where
  dimensionLo := 13100
  dimensionHi := 13100
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2326042499 / 1000000000000 : ℝ)
  frameLo := (620261227429 / 1000000000000 : ℝ)
  frameHi := (1460825653583 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13100]
  agentFrame_pos := by norm_num only [agent13100]
  worldRadius := (2326042499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13100]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (103930191 / 100000000000 : ℝ)
  lowerTail := (502739 / 400000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6858480931 / 1000000000000 : ℝ)
  ledger := by
    have h : (1155473327 / 1000000000000 : ℚ) +
        (8698484587 / 1000000000000000000 : ℚ) / (2326042499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (103930191 / 100000000000 : ℚ) + (502739 / 400000000 : ℚ) ≤
        (6858480931 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1155473327 / 1000000000000 : ℚ) +
        (8698484587 / 1000000000000000000 : ℚ) / (2326042499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (103930191 / 100000000000 : ℚ) + (502739 / 400000000 : ℚ) : ℚ) : ℝ) ≤
        ((6858480931 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13100]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13100 :
    2 * 160 < 13100 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997773 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13100 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13101 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13101. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13101 : WorldParameters where
  hiddenCharge := (28885851 / 25000000000 : ℝ)
  frame := (620248230159 / 1000000000000 : ℝ)
  moment := (8696751499 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13101 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460797180299 / 1000000000000 : ℝ)
    root := (4118750737 / 500000000000 : ℝ) }

noncomputable def scalar13101 : ScalarCertificate 13101 world13101 agent13101 where
  dimensionLo := 13101
  dimensionHi := 13101
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2326406899 / 1000000000000 : ℝ)
  frameLo := (620248230159 / 1000000000000 : ℝ)
  frameHi := (1460797180299 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13101]
  agentFrame_pos := by norm_num only [agent13101]
  worldRadius := (2326406899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13101]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1038461119 / 1000000000000 : ℝ)
  lowerTail := (313975909 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1713958289 / 250000000000 : ℝ)
  ledger := by
    have h : (28885851 / 25000000000 : ℚ) +
        (8696751499 / 1000000000000000000 : ℚ) / (2326406899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1038461119 / 1000000000000 : ℚ) + (313975909 / 250000000000 : ℚ) ≤
        (1713958289 / 250000000000 : ℚ) := by norm_num only
    have hc : (((28885851 / 25000000000 : ℚ) +
        (8696751499 / 1000000000000000000 : ℚ) / (2326406899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1038461119 / 1000000000000 : ℚ) + (313975909 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1713958289 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13101]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13101 :
    2 * 160 < 13101 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999889 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13101 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13102 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13102. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13102 : WorldParameters where
  hiddenCharge := (1155394763 / 1000000000000 : ℝ)
  frame := (620235234897 / 1000000000000 : ℝ)
  moment := (1739003779 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13102 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460768730057 / 1000000000000 : ℝ)
    root := (8236894169 / 1000000000000 : ℝ) }

noncomputable def scalar13102 : ScalarCertificate 13102 world13102 agent13102 where
  dimensionLo := 13102
  dimensionHi := 13102
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2326771099 / 1000000000000 : ℝ)
  frameLo := (620235234897 / 1000000000000 : ℝ)
  frameHi := (1460768730057 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13102]
  agentFrame_pos := by norm_num only [agent13102]
  worldRadius := (2326771099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13102]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (20752421 / 20000000000 : ℝ)
  lowerTail := (627480267 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3426593839 / 500000000000 : ℝ)
  ledger := by
    have h : (1155394763 / 1000000000000 : ℚ) +
        (1739003779 / 200000000000000000 : ℚ) / (2326771099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (20752421 / 20000000000 : ℚ) + (627480267 / 500000000000 : ℚ) ≤
        (3426593839 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1155394763 / 1000000000000 : ℚ) +
        (1739003779 / 200000000000000000 : ℚ) / (2326771099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (20752421 / 20000000000 : ℚ) + (627480267 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3426593839 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13102]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13102 :
    2 * 160 < 13102 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (78124957 / 7812500000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13102 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13103 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13103. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13103 : WorldParameters where
  hiddenCharge := (1155355497 / 1000000000000 : ℝ)
  frame := (620222241643 / 1000000000000 : ℝ)
  moment := (2173321693 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13103 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460740285343 / 1000000000000 : ℝ)
    root := (8236286967 / 1000000000000 : ℝ) }

noncomputable def scalar13103 : ScalarCertificate 13103 world13103 agent13103 where
  dimensionLo := 13103
  dimensionHi := 13103
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2327135399 / 1000000000000 : ℝ)
  frameLo := (620222241643 / 1000000000000 : ℝ)
  frameHi := (1460740285343 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13103]
  agentFrame_pos := by norm_num only [agent13103]
  worldRadius := (2327135399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13103]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (3239943 / 3125000000 : ℝ)
  lowerTail := (78376141 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3425272099 / 500000000000 : ℝ)
  ledger := by
    have h : (1155355497 / 1000000000000 : ℚ) +
        (2173321693 / 250000000000000000 : ℚ) / (2327135399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (3239943 / 3125000000 : ℚ) + (78376141 / 62500000000 : ℚ) ≤
        (3425272099 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1155355497 / 1000000000000 : ℚ) +
        (2173321693 / 250000000000000000 : ℚ) / (2327135399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (3239943 / 3125000000 : ℚ) + (78376141 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((3425272099 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13103]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13103 :
    2 * 160 < 13103 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998873 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13103 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13104 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13104. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13104 : WorldParameters where
  hiddenCharge := (14441453 / 12500000000 : ℝ)
  frame := (155052312599 / 250000000000 : ℝ)
  moment := (2172888783 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13104 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730355928911 / 500000000000 : ℝ)
    root := (823567993 / 100000000000 : ℝ) }

noncomputable def scalar13104 : ScalarCertificate 13104 world13104 agent13104 where
  dimensionLo := 13104
  dimensionHi := 13104
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2327499699 / 1000000000000 : ℝ)
  frameLo := (155052312599 / 250000000000 : ℝ)
  frameHi := (730355928911 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13104]
  agentFrame_pos := by norm_num only [agent13104]
  worldRadius := (2327499699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13104]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1035943261 / 1000000000000 : ℝ)
  lowerTail := (1253076817 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1369580577 / 200000000000 : ℝ)
  ledger := by
    have h : (14441453 / 12500000000 : ℚ) +
        (2172888783 / 250000000000000000 : ℚ) / (2327499699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1035943261 / 1000000000000 : ℚ) + (1253076817 / 1000000000000 : ℚ) ≤
        (1369580577 / 200000000000 : ℚ) := by norm_num only
    have hc : (((14441453 / 12500000000 : ℚ) +
        (2172888783 / 250000000000000000 : ℚ) / (2327499699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1035943261 / 1000000000000 : ℚ) + (1253076817 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1369580577 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13104]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13104 :
    2 * 160 < 13104 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999449 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13104 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13105 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13105. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13105 : WorldParameters where
  hiddenCharge := (577638497 / 500000000000 : ℝ)
  frame := (155049065289 / 250000000000 : ℝ)
  moment := (8689823973 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13105 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460683447489 / 1000000000000 : ℝ)
    root := (8235073059 / 1000000000000 : ℝ) }

noncomputable def scalar13105 : ScalarCertificate 13105 world13105 agent13105 where
  dimensionLo := 13105
  dimensionHi := 13105
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2327864099 / 1000000000000 : ℝ)
  frameLo := (155049065289 / 250000000000 : ℝ)
  frameHi := (1460683447489 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13105]
  agentFrame_pos := by norm_num only [agent13105]
  worldRadius := (2327864099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13105]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (517552809 / 500000000000 : ℝ)
  lowerTail := (125213629 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6845263739 / 1000000000000 : ℝ)
  ledger := by
    have h : (577638497 / 500000000000 : ℚ) +
        (8689823973 / 1000000000000000000 : ℚ) / (2327864099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (517552809 / 500000000000 : ℚ) + (125213629 / 100000000000 : ℚ) ≤
        (6845263739 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((577638497 / 500000000000 : ℚ) +
        (8689823973 / 1000000000000000000 : ℚ) / (2327864099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (517552809 / 500000000000 : ℚ) + (125213629 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6845263739 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13105]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13105 :
    2 * 160 < 13105 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997311 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13105 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13106 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13106. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13106 : WorldParameters where
  hiddenCharge := (577618879 / 500000000000 : ℝ)
  frame := (310091636961 / 500000000000 : ℝ)
  moment := (8688093297 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13106 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365163760667 / 250000000000 : ℝ)
    root := (514654151 / 62500000000 : ℝ) }

noncomputable def scalar13106 : ScalarCertificate 13106 world13106 agent13106 where
  dimensionLo := 13106
  dimensionHi := 13106
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2328228299 / 1000000000000 : ℝ)
  frameLo := (310091636961 / 500000000000 : ℝ)
  frameHi := (365163760667 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13106]
  agentFrame_pos := by norm_num only [agent13106]
  worldRadius := (2328228299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13106]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (206853727 / 200000000000 : ℝ)
  lowerTail := (1251196447 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3421313373 / 500000000000 : ℝ)
  ledger := by
    have h : (577618879 / 500000000000 : ℚ) +
        (8688093297 / 1000000000000000000 : ℚ) / (2328228299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (206853727 / 200000000000 : ℚ) + (1251196447 / 1000000000000 : ℚ) ≤
        (3421313373 / 500000000000 : ℚ) := by norm_num only
    have hc : (((577618879 / 500000000000 : ℚ) +
        (8688093297 / 1000000000000000000 : ℚ) / (2328228299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (206853727 / 200000000000 : ℚ) + (1251196447 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3421313373 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13106]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13106 :
    2 * 160 < 13106 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999799 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13106 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13107 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13107. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13107 : WorldParameters where
  hiddenCharge := (1155198531 / 1000000000000 : ℝ)
  frame := (310085144347 / 500000000000 : ℝ)
  moment := (4343181551 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13107 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182578332607 / 125000000000 : ℝ)
    root := (65870879 / 8000000000 : ℝ) }

noncomputable def scalar13107 : ScalarCertificate 13107 world13107 agent13107 where
  dimensionLo := 13107
  dimensionHi := 13107
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2328592599 / 1000000000000 : ℝ)
  frameLo := (310085144347 / 500000000000 : ℝ)
  frameHi := (182578332607 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13107]
  agentFrame_pos := by norm_num only [agent13107]
  worldRadius := (2328592599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13107]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1033432487 / 1000000000000 : ℝ)
  lowerTail := (625128749 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6839991877 / 1000000000000 : ℝ)
  ledger := by
    have h : (1155198531 / 1000000000000 : ℚ) +
        (4343181551 / 500000000000000000 : ℚ) / (2328592599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1033432487 / 1000000000000 : ℚ) + (625128749 / 500000000000 : ℚ) ≤
        (6839991877 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1155198531 / 1000000000000 : ℚ) +
        (4343181551 / 500000000000000000 : ℚ) / (2328592599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1033432487 / 1000000000000 : ℚ) + (625128749 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6839991877 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13107]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13107 :
    2 * 160 < 13107 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995613 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13107 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13108 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13108. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13108 : WorldParameters where
  hiddenCharge := (231031863 / 200000000000 : ℝ)
  frame := (620157305471 / 1000000000000 : ℝ)
  moment := (2171158347 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13108 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (5705462049 / 3906250000 : ℝ)
    root := (8233253499 / 1000000000000 : ℝ) }

noncomputable def scalar13108 : ScalarCertificate 13108 world13108 agent13108 where
  dimensionLo := 13108
  dimensionHi := 13108
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2328956899 / 1000000000000 : ℝ)
  frameLo := (620157305471 / 1000000000000 : ℝ)
  frameHi := (5705462049 / 3906250000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13108]
  agentFrame_pos := by norm_num only [agent13108]
  worldRadius := (2328956899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13108]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1032597087 / 1000000000000 : ℝ)
  lowerTail := (156164917 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6837359079 / 1000000000000 : ℝ)
  ledger := by
    have h : (231031863 / 200000000000 : ℚ) +
        (2171158347 / 250000000000000000 : ℚ) / (2328956899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1032597087 / 1000000000000 : ℚ) + (156164917 / 125000000000 : ℚ) ≤
        (6837359079 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((231031863 / 200000000000 : ℚ) +
        (2171158347 / 250000000000000000 : ℚ) / (2328956899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1032597087 / 1000000000000 : ℚ) + (156164917 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6837359079 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13108]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13108 :
    2 * 160 < 13108 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999871 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13108 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13109 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13109. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13109 : WorldParameters where
  hiddenCharge := (1155120109 / 1000000000000 : ℝ)
  frame := (620144324253 / 1000000000000 : ℝ)
  moment := (2170726039 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13109 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460569931229 / 1000000000000 : ℝ)
    root := (164652947 / 20000000000 : ℝ) }

noncomputable def scalar13109 : ScalarCertificate 13109 world13109 agent13109 where
  dimensionLo := 13109
  dimensionHi := 13109
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2329321299 / 1000000000000 : ℝ)
  frameLo := (620144324253 / 1000000000000 : ℝ)
  frameHi := (1460569931229 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13109]
  agentFrame_pos := by norm_num only [agent13109]
  worldRadius := (2329321299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13109]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1031762599 / 1000000000000 : ℝ)
  lowerTail := (312095537 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6834728561 / 1000000000000 : ℝ)
  ledger := by
    have h : (1155120109 / 1000000000000 : ℚ) +
        (2170726039 / 250000000000000000 : ℚ) / (2329321299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1031762599 / 1000000000000 : ℚ) + (312095537 / 250000000000 : ℚ) ≤
        (6834728561 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1155120109 / 1000000000000 : ℚ) +
        (2170726039 / 250000000000000000 : ℚ) / (2329321299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1031762599 / 1000000000000 : ℚ) + (312095537 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6834728561 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13109]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13109 :
    2 * 160 < 13109 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994867 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13109 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13110 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13110. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13110 : WorldParameters where
  hiddenCharge := (1155080913 / 1000000000000 : ℝ)
  frame := (7751641813 / 12500000000 : ℝ)
  moment := (1736235081 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13110 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (18255809949 / 12500000000 : ℝ)
    root := (1646408261 / 200000000000 : ℝ) }

noncomputable def scalar13110 : ScalarCertificate 13110 world13110 agent13110 where
  dimensionLo := 13110
  dimensionHi := 13110
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2329803099 / 1000000000000 : ℝ)
  frameLo := (7751641813 / 12500000000 : ℝ)
  frameHi := (18255809949 / 12500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13110]
  agentFrame_pos := by norm_num only [agent13110]
  worldRadius := (2329803099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13110]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1030748189 / 1000000000000 : ℝ)
  lowerTail := (1247206993 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6831519493 / 1000000000000 : ℝ)
  ledger := by
    have h : (1155080913 / 1000000000000 : ℚ) +
        (1736235081 / 200000000000000000 : ℚ) / (2329803099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1030748189 / 1000000000000 : ℚ) + (1247206993 / 1000000000000 : ℚ) ≤
        (6831519493 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1155080913 / 1000000000000 : ℚ) +
        (1736235081 / 200000000000000000 : ℚ) / (2329803099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1030748189 / 1000000000000 : ℚ) + (1247206993 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6831519493 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13110]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13110 :
    2 * 160 < 13110 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998071 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13110 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13111 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13111. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13111 : WorldParameters where
  hiddenCharge := (577520863 / 500000000000 : ℝ)
  frame := (62011836783 / 100000000000 : ℝ)
  moment := (1735889427 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13111 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460436466091 / 1000000000000 : ℝ)
    root := (257232357 / 31250000000 : ℝ) }

noncomputable def scalar13111 : ScalarCertificate 13111 world13111 agent13111 where
  dimensionLo := 13111
  dimensionHi := 13111
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2330167599 / 1000000000000 : ℝ)
  frameLo := (62011836783 / 100000000000 : ℝ)
  frameHi := (1460436466091 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13111]
  agentFrame_pos := by norm_num only [agent13111]
  worldRadius := (2330167599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13111]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1029915381 / 1000000000000 : ℝ)
  lowerTail := (249254321 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6828893491 / 1000000000000 : ℝ)
  ledger := by
    have h : (577520863 / 500000000000 : ℚ) +
        (1735889427 / 200000000000000000 : ℚ) / (2330167599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1029915381 / 1000000000000 : ℚ) + (249254321 / 200000000000 : ℚ) ≤
        (6828893491 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((577520863 / 500000000000 : ℚ) +
        (1735889427 / 200000000000000000 : ℚ) / (2330167599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1029915381 / 1000000000000 : ℚ) + (249254321 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6828893491 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13111]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13111 :
    2 * 160 < 13111 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999483 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13111 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13112 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13112. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13112 : WorldParameters where
  hiddenCharge := (23100051 / 20000000000 : ℝ)
  frame := (620105392623 / 1000000000000 : ℝ)
  moment := (4338859673 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13112 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460408153407 / 1000000000000 : ℝ)
    root := (8230829707 / 1000000000000 : ℝ) }

noncomputable def scalar13112 : ScalarCertificate 13112 world13112 agent13112 where
  dimensionLo := 13112
  dimensionHi := 13112
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2330531999 / 1000000000000 : ℝ)
  frameLo := (620105392623 / 1000000000000 : ℝ)
  frameHi := (1460408153407 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13112]
  agentFrame_pos := by norm_num only [agent13112]
  worldRadius := (2330531999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13112]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1029083293 / 1000000000000 : ℝ)
  lowerTail := (1245336977 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (170656741 / 25000000000 : ℝ)
  ledger := by
    have h : (23100051 / 20000000000 : ℚ) +
        (4338859673 / 500000000000000000 : ℚ) / (2330531999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1029083293 / 1000000000000 : ℚ) + (1245336977 / 1000000000000 : ℚ) ≤
        (170656741 / 25000000000 : ℚ) := by norm_num only
    have hc : (((23100051 / 20000000000 : ℚ) +
        (4338859673 / 500000000000000000 : ℚ) / (2330531999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1029083293 / 1000000000000 : ℚ) + (1245336977 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((170656741 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13112]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13112 :
    2 * 160 < 13112 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997213 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13112 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13113 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13113. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13113 : WorldParameters where
  hiddenCharge := (144370423 / 125000000000 : ℝ)
  frame := (620092419419 / 1000000000000 : ℝ)
  moment := (8675992037 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13113 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292075969239 / 200000000000 : ℝ)
    root := (8230224217 / 1000000000000 : ℝ) }

noncomputable def scalar13113 : ScalarCertificate 13113 world13113 agent13113 where
  dimensionLo := 13113
  dimensionHi := 13113
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2330896399 / 1000000000000 : ℝ)
  frameLo := (620092419419 / 1000000000000 : ℝ)
  frameHi := (292075969239 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13113]
  agentFrame_pos := by norm_num only [agent13113]
  worldRadius := (2330896399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13113]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (102825199 / 100000000000 : ℝ)
  lowerTail := (1244403173 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (852955991 / 125000000000 : ℝ)
  ledger := by
    have h : (144370423 / 125000000000 : ℚ) +
        (8675992037 / 1000000000000000000 : ℚ) / (2330896399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (102825199 / 100000000000 : ℚ) + (1244403173 / 1000000000000 : ℚ) ≤
        (852955991 / 125000000000 : ℚ) := by norm_num only
    have hc : (((144370423 / 125000000000 : ℚ) +
        (8675992037 / 1000000000000000000 : ℚ) / (2330896399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (102825199 / 100000000000 : ℚ) + (1244403173 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((852955991 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13113]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13113 :
    2 * 160 < 13113 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999869 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13113 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13114 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13114. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13114 : WorldParameters where
  hiddenCharge := (288731057 / 250000000000 : ℝ)
  frame := (310039724109 / 500000000000 : ℝ)
  moment := (8674265209 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13114 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460351561947 / 1000000000000 : ℝ)
    root := (822961883 / 100000000000 : ℝ) }

noncomputable def scalar13114 : ScalarCertificate 13114 world13114 agent13114 where
  dimensionLo := 13114
  dimensionHi := 13114
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2331260699 / 1000000000000 : ℝ)
  frameLo := (310039724109 / 500000000000 : ℝ)
  frameHi := (1460351561947 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13114]
  agentFrame_pos := by norm_num only [agent13114]
  worldRadius := (2331260699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13114]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (205484277 / 200000000000 : ℝ)
  lowerTail := (38858441 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6821028327 / 1000000000000 : ℝ)
  ledger := by
    have h : (288731057 / 250000000000 : ℚ) +
        (8674265209 / 1000000000000000000 : ℚ) / (2331260699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (205484277 / 200000000000 : ℚ) + (38858441 / 31250000000 : ℚ) ≤
        (6821028327 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((288731057 / 250000000000 : ℚ) +
        (8674265209 / 1000000000000000000 : ℚ) / (2331260699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (205484277 / 200000000000 : ℚ) + (38858441 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((6821028327 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13114]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13114 :
    2 * 160 < 13114 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997181 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13114 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13115 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13115. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13115 : WorldParameters where
  hiddenCharge := (577442541 / 500000000000 : ℝ)
  frame := (310033239509 / 500000000000 : ℝ)
  moment := (8672538861 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13115 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (36508082079 / 25000000000 : ℝ)
    root := (8229013607 / 1000000000000 : ℝ) }

noncomputable def scalar13115 : ScalarCertificate 13115 world13115 agent13115 where
  dimensionLo := 13115
  dimensionHi := 13115
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2331625099 / 1000000000000 : ℝ)
  frameLo := (310033239509 / 500000000000 : ℝ)
  frameHi := (36508082079 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13115]
  agentFrame_pos := by norm_num only [agent13115]
  worldRadius := (2331625099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13115]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1026591587 / 1000000000000 : ℝ)
  lowerTail := (248507581 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6818410781 / 1000000000000 : ℝ)
  ledger := by
    have h : (577442541 / 500000000000 : ℚ) +
        (8672538861 / 1000000000000000000 : ℚ) / (2331625099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1026591587 / 1000000000000 : ℚ) + (248507581 / 200000000000 : ℚ) ≤
        (6818410781 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((577442541 / 500000000000 : ℚ) +
        (8672538861 / 1000000000000000000 : ℚ) / (2331625099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1026591587 / 1000000000000 : ℚ) + (248507581 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6818410781 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13115]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13115 :
    2 * 160 < 13115 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997769 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13115 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13116 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13116. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13116 : WorldParameters where
  hiddenCharge := (577422973 / 500000000000 : ℝ)
  frame := (31002675591 / 50000000000 : ℝ)
  moment := (8670812993 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13116 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (730147510747 / 500000000000 : ℝ)
    root := (8228408549 / 1000000000000 : ℝ) }

noncomputable def scalar13116 : ScalarCertificate 13116 world13116 agent13116 where
  dimensionLo := 13116
  dimensionHi := 13116
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2331989499 / 1000000000000 : ℝ)
  frameLo := (31002675591 / 50000000000 : ℝ)
  frameHi := (730147510747 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13116]
  agentFrame_pos := by norm_num only [agent13116]
  worldRadius := (2331989499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13116]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (256440643 / 250000000000 : ℝ)
  lowerTail := (1241606527 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6815795377 / 1000000000000 : ℝ)
  ledger := by
    have h : (577422973 / 500000000000 : ℚ) +
        (8670812993 / 1000000000000000000 : ℚ) / (2331989499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (256440643 / 250000000000 : ℚ) + (1241606527 / 1000000000000 : ℚ) ≤
        (6815795377 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((577422973 / 500000000000 : ℚ) +
        (8670812993 / 1000000000000000000 : ℚ) / (2331989499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (256440643 / 250000000000 : ℚ) + (1241606527 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6815795377 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13116]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13116 :
    2 * 160 < 13116 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999433 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13116 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13117 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13117. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13117 : WorldParameters where
  hiddenCharge := (57740341 / 50000000000 : ℝ)
  frame := (620040546623 / 1000000000000 : ℝ)
  moment := (1733817521 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13117 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460266771109 / 1000000000000 : ℝ)
    root := (4113901827 / 500000000000 : ℝ) }

noncomputable def scalar13117 : ScalarCertificate 13117 world13117 agent13117 where
  dimensionLo := 13117
  dimensionHi := 13117
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2332353999 / 1000000000000 : ℝ)
  frameLo := (620040546623 / 1000000000000 : ℝ)
  frameHi := (1460266771109 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13117]
  agentFrame_pos := by norm_num only [agent13117]
  worldRadius := (2332353999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13117]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (512467191 / 500000000000 : ℝ)
  lowerTail := (620338013 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6813182069 / 1000000000000 : ℝ)
  ledger := by
    have h : (57740341 / 50000000000 : ℚ) +
        (1733817521 / 200000000000000000 : ℚ) / (2332353999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (512467191 / 500000000000 : ℚ) + (620338013 / 500000000000 : ℚ) ≤
        (6813182069 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((57740341 / 50000000000 : ℚ) +
        (1733817521 / 200000000000000000 : ℚ) / (2332353999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (512467191 / 500000000000 : ℚ) + (620338013 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6813182069 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13117]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13117 :
    2 * 160 < 13117 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999989 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13117 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13118 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13118. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13118 : WorldParameters where
  hiddenCharge := (144345963 / 125000000000 : ℝ)
  frame := (310013791713 / 500000000000 : ℝ)
  moment := (8667362697 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13118 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182529817229 / 125000000000 : ℝ)
    root := (4113599493 / 500000000000 : ℝ) }

noncomputable def scalar13118 : ScalarCertificate 13118 world13118 agent13118 where
  dimensionLo := 13118
  dimensionHi := 13118
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2332718499 / 1000000000000 : ℝ)
  frameLo := (310013791713 / 500000000000 : ℝ)
  frameHi := (182529817229 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13118]
  agentFrame_pos := by norm_num only [agent13118]
  worldRadius := (2332718499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13118]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1024107011 / 1000000000000 : ℝ)
  lowerTail := (1239746393 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6810570979 / 1000000000000 : ℝ)
  ledger := by
    have h : (144345963 / 125000000000 : ℚ) +
        (8667362697 / 1000000000000000000 : ℚ) / (2332718499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1024107011 / 1000000000000 : ℚ) + (1239746393 / 1000000000000 : ℚ) ≤
        (6810570979 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((144345963 / 125000000000 : ℚ) +
        (8667362697 / 1000000000000000000 : ℚ) / (2332718499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1024107011 / 1000000000000 : ℚ) + (1239746393 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6810570979 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13118]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13118 :
    2 * 160 < 13118 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998673 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13118 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13119 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13119. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13119 : WorldParameters where
  hiddenCharge := (577364299 / 500000000000 : ℝ)
  frame := (620014622229 / 1000000000000 : ℝ)
  moment := (2166409567 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13119 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58408412633 / 40000000000 : ℝ)
    root := (8226594419 / 1000000000000 : ℝ) }

noncomputable def scalar13119 : ScalarCertificate 13119 world13119 agent13119 where
  dimensionLo := 13119
  dimensionHi := 13119
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2333082799 / 1000000000000 : ℝ)
  frameLo := (620014622229 / 1000000000000 : ℝ)
  frameHi := (58408412633 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13119]
  agentFrame_pos := by norm_num only [agent13119]
  worldRadius := (2333082799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13119]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (127910029 / 125000000000 : ℝ)
  lowerTail := (1238817379 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (68079619 / 10000000000 : ℝ)
  ledger := by
    have h : (577364299 / 500000000000 : ℚ) +
        (2166409567 / 250000000000000000 : ℚ) / (2333082799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127910029 / 125000000000 : ℚ) + (1238817379 / 1000000000000 : ℚ) ≤
        (68079619 / 10000000000 : ℚ) := by norm_num only
    have hc : (((577364299 / 500000000000 : ℚ) +
        (2166409567 / 250000000000000000 : ℚ) / (2333082799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127910029 / 125000000000 : ℚ) + (1238817379 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((68079619 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13119]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13119 :
    2 * 160 < 13119 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999807 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13119 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13120 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13120. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13120 : WorldParameters where
  hiddenCharge := (1154689503 / 1000000000000 : ℝ)
  frame := (620001663031 / 1000000000000 : ℝ)
  moment := (8663914319 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13120 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460105430439 / 1000000000000 : ℝ)
    root := (8225990017 / 1000000000000 : ℝ) }

noncomputable def scalar13120 : ScalarCertificate 13120 world13120 agent13120 where
  dimensionLo := 13120
  dimensionHi := 13120
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2333564899 / 1000000000000 : ℝ)
  frameLo := (620001663031 / 1000000000000 : ℝ)
  frameHi := (1460105430439 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13120]
  agentFrame_pos := by norm_num only [agent13120]
  worldRadius := (2333564899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13120]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (204455083 / 200000000000 : ℝ)
  lowerTail := (1237652689 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1360955799 / 200000000000 : ℝ)
  ledger := by
    have h : (1154689503 / 1000000000000 : ℚ) +
        (8663914319 / 1000000000000000000 : ℚ) / (2333564899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (204455083 / 200000000000 : ℚ) + (1237652689 / 1000000000000 : ℚ) ≤
        (1360955799 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1154689503 / 1000000000000 : ℚ) +
        (8663914319 / 1000000000000000000 : ℚ) / (2333564899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (204455083 / 200000000000 : ℚ) + (1237652689 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1360955799 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13120]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13120 :
    2 * 160 < 13120 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999703 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13120 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13121 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13121. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13121 : WorldParameters where
  hiddenCharge := (1154650417 / 1000000000000 : ℝ)
  frame := (77498588229 / 125000000000 : ℝ)
  moment := (8662190849 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13121 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365019309407 / 250000000000 : ℝ)
    root := (4112692889 / 500000000000 : ℝ) }

noncomputable def scalar13121 : ScalarCertificate 13121 world13121 agent13121 where
  dimensionLo := 13121
  dimensionHi := 13121
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2333929399 / 1000000000000 : ℝ)
  frameLo := (77498588229 / 125000000000 : ℝ)
  frameHi := (365019309407 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13121]
  agentFrame_pos := by norm_num only [agent13121]
  worldRadius := (2333929399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13121]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1021450421 / 1000000000000 : ℝ)
  lowerTail := (618362797 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6802174511 / 1000000000000 : ℝ)
  ledger := by
    have h : (1154650417 / 1000000000000 : ℚ) +
        (8662190849 / 1000000000000000000 : ℚ) / (2333929399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1021450421 / 1000000000000 : ℚ) + (618362797 / 500000000000 : ℚ) ≤
        (6802174511 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1154650417 / 1000000000000 : ℚ) +
        (8662190849 / 1000000000000000000 : ℚ) / (2333929399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1021450421 / 1000000000000 : ℚ) + (618362797 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6802174511 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13121]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13121 :
    2 * 160 < 13121 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998311 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13121 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13122 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13122. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13122 : WorldParameters where
  hiddenCharge := (1154611341 / 1000000000000 : ℝ)
  frame := (619975750631 / 1000000000000 : ℝ)
  moment := (8660467859 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13122 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1460049056069 / 1000000000000 : ℝ)
    root := (1028097713 / 125000000000 : ℝ) }

noncomputable def scalar13122 : ScalarCertificate 13122 world13122 agent13122 where
  dimensionLo := 13122
  dimensionHi := 13122
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2334293899 / 1000000000000 : ℝ)
  frameLo := (619975750631 / 1000000000000 : ℝ)
  frameHi := (1460049056069 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13122]
  agentFrame_pos := by norm_num only [agent13122]
  worldRadius := (2334293899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13122]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (127578273 / 125000000000 : ℝ)
  lowerTail := (617899649 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1359914423 / 200000000000 : ℝ)
  ledger := by
    have h : (1154611341 / 1000000000000 : ℚ) +
        (8660467859 / 1000000000000000000 : ℚ) / (2334293899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127578273 / 125000000000 : ℚ) + (617899649 / 500000000000 : ℚ) ≤
        (1359914423 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1154611341 / 1000000000000 : ℚ) +
        (8660467859 / 1000000000000000000 : ℚ) / (2334293899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127578273 / 125000000000 : ℚ) + (617899649 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1359914423 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13122]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13122 :
    2 * 160 < 13122 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998373 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13122 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13123 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13123. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13123 : WorldParameters where
  hiddenCharge := (46182891 / 40000000000 : ℝ)
  frame := (619962797429 / 1000000000000 : ℝ)
  moment := (8658745347 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13123 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (365005222897 / 250000000000 : ℝ)
    root := (4112088927 / 500000000000 : ℝ) }

noncomputable def scalar13123 : ScalarCertificate 13123 world13123 agent13123 where
  dimensionLo := 13123
  dimensionHi := 13123
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2334658399 / 1000000000000 : ℝ)
  frameLo := (619962797429 / 1000000000000 : ℝ)
  frameHi := (365005222897 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13123]
  agentFrame_pos := by norm_num only [agent13123]
  worldRadius := (2334658399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13123]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (509901381 / 500000000000 : ℝ)
  lowerTail := (617436933 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1699242981 / 250000000000 : ℝ)
  ledger := by
    have h : (46182891 / 40000000000 : ℚ) +
        (8658745347 / 1000000000000000000 : ℚ) / (2334658399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (509901381 / 500000000000 : ℚ) + (617436933 / 500000000000 : ℚ) ≤
        (1699242981 / 250000000000 : ℚ) := by norm_num only
    have hc : (((46182891 / 40000000000 : ℚ) +
        (8658745347 / 1000000000000000000 : ℚ) / (2334658399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (509901381 / 500000000000 : ℚ) + (617436933 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1699242981 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13123]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13123 :
    2 * 160 < 13123 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996541 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13123 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13124 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13124. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13124 : WorldParameters where
  hiddenCharge := (1154533219 / 1000000000000 : ℝ)
  frame := (619949846223 / 1000000000000 : ℝ)
  moment := (4328511657 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13124 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459992738347 / 1000000000000 : ℝ)
    root := (4111787053 / 500000000000 : ℝ) }

noncomputable def scalar13124 : ScalarCertificate 13124 world13124 agent13124 where
  dimensionLo := 13124
  dimensionHi := 13124
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2335022899 / 1000000000000 : ℝ)
  frameLo := (619949846223 / 1000000000000 : ℝ)
  frameHi := (1459992738347 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13124]
  agentFrame_pos := by norm_num only [agent13124]
  worldRadius := (2335022899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13124]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (203796011 / 200000000000 : ℝ)
  lowerTail := (1233949193 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1358874747 / 200000000000 : ℝ)
  ledger := by
    have h : (1154533219 / 1000000000000 : ℚ) +
        (4328511657 / 500000000000000000 : ℚ) / (2335022899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (203796011 / 200000000000 : ℚ) + (1233949193 / 1000000000000 : ℚ) ≤
        (1358874747 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1154533219 / 1000000000000 : ℚ) +
        (4328511657 / 500000000000000000 : ℚ) / (2335022899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (203796011 / 200000000000 : ℚ) + (1233949193 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1358874747 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13124]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13124 :
    2 * 160 < 13124 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996831 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13124 {← IO.monoMsNow}" : IO Unit)
