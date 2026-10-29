import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12260 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12260. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12260 : WorldParameters where
  hiddenCharge := (1192397559 / 1000000000000 : ℝ)
  frame := (631941161831 / 1000000000000 : ℝ)
  moment := (5171762087 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12260 : AgentParameters :=
  { agentLedgerParameters with
    charge := (235493067 / 125000000000 : ℝ)
    frame := (364649671619 / 250000000000 : ℝ)
    root := (441194831 / 50000000000 : ℝ) }

noncomputable def scalar12260 : ScalarCertificate 12260 world12260 agent12260 where
  dimensionLo := 12260
  dimensionHi := 12260
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2060859799 / 1000000000000 : ℝ)
  frameLo := (631941161831 / 1000000000000 : ℝ)
  frameHi := (364649671619 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12260]
  agentFrame_pos := by norm_num only [agent12260]
  worldRadius := (2060859799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12260]
  retainedCharge := (235493067 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (7988043 / 4000000000 : ℝ)
  lowerTail := (91253477 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (489504913 / 50000000000 : ℝ)
  ledger := by
    have h : (1192397559 / 1000000000000 : ℚ) +
        (5171762087 / 500000000000000000 : ℚ) / (2060859799 / 1000000000000 : ℚ) ^ 2 +
        (235493067 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7988043 / 4000000000 : ℚ) + (91253477 / 40000000000 : ℚ) ≤
        (489504913 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1192397559 / 1000000000000 : ℚ) +
        (5171762087 / 500000000000000000 : ℚ) / (2060859799 / 1000000000000 : ℚ) ^ 2 +
        (235493067 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7988043 / 4000000000 : ℚ) + (91253477 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((489504913 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12260]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12260 :
    2 * 160 < 12260 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499997931 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12260 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12261 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12261. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12261 : WorldParameters where
  hiddenCharge := (1192348467 / 1000000000000 : ℝ)
  frame := (631926284453 / 1000000000000 : ℝ)
  moment := (5170658261 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12261 : AgentParameters :=
  { agentLedgerParameters with
    charge := (941602451 / 500000000000 : ℝ)
    frame := (291711555073 / 200000000000 : ℝ)
    root := (8823159597 / 1000000000000 : ℝ) }

noncomputable def scalar12261 : ScalarCertificate 12261 world12261 agent12261 where
  dimensionLo := 12261
  dimensionHi := 12261
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2061214599 / 1000000000000 : ℝ)
  frameLo := (631926284453 / 1000000000000 : ℝ)
  frameHi := (291711555073 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12261]
  agentFrame_pos := by norm_num only [agent12261]
  worldRadius := (2061214599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12261]
  retainedCharge := (941602451 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1995239143 / 1000000000000 : ℝ)
  lowerTail := (2279445907 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4892144471 / 500000000000 : ℝ)
  ledger := by
    have h : (1192348467 / 1000000000000 : ℚ) +
        (5170658261 / 500000000000000000 : ℚ) / (2061214599 / 1000000000000 : ℚ) ^ 2 +
        (941602451 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1995239143 / 1000000000000 : ℚ) + (2279445907 / 1000000000000 : ℚ) ≤
        (4892144471 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1192348467 / 1000000000000 : ℚ) +
        (5170658261 / 500000000000000000 : ℚ) / (2061214599 / 1000000000000 : ℚ) ^ 2 +
        (941602451 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1995239143 / 1000000000000 : ℚ) + (2279445907 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4892144471 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12261]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12261 :
    2 * 160 < 12261 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999319 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12261 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12262 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12262. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12262 : WorldParameters where
  hiddenCharge := (298074847 / 250000000000 : ℝ)
  frame := (315955704783 / 500000000000 : ℝ)
  moment := (1292388691 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12262 : AgentParameters :=
  { agentLedgerParameters with
    charge := (117654121 / 62500000000 : ℝ)
    frame := (1458516885011 / 1000000000000 : ℝ)
    root := (1764484561 / 200000000000 : ℝ) }

noncomputable def scalar12262 : ScalarCertificate 12262 world12262 agent12262 where
  dimensionLo := 12262
  dimensionHi := 12262
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2061569299 / 1000000000000 : ℝ)
  frameLo := (315955704783 / 500000000000 : ℝ)
  frameHi := (1458516885011 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12262]
  agentFrame_pos := by norm_num only [agent12262]
  worldRadius := (2061569299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12262]
  retainedCharge := (117654121 / 62500000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (99673461 / 50000000000 : ℝ)
  lowerTail := (1138778293 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2444621217 / 250000000000 : ℝ)
  ledger := by
    have h : (298074847 / 250000000000 : ℚ) +
        (1292388691 / 125000000000000000 : ℚ) / (2061569299 / 1000000000000 : ℚ) ^ 2 +
        (117654121 / 62500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (99673461 / 50000000000 : ℚ) + (1138778293 / 500000000000 : ℚ) ≤
        (2444621217 / 250000000000 : ℚ) := by norm_num only
    have hc : (((298074847 / 250000000000 : ℚ) +
        (1292388691 / 125000000000000000 : ℚ) / (2061569299 / 1000000000000 : ℚ) ^ 2 +
        (117654121 / 62500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (99673461 / 50000000000 : ℚ) + (1138778293 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2444621217 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12262]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12262 :
    2 * 160 < 12262 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499997803 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12262 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12263 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12263. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12263 : WorldParameters where
  hiddenCharge := (596125161 / 500000000000 : ℝ)
  frame := (63189653717 / 100000000000 : ℝ)
  moment := (10336903193 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12263 : AgentParameters :=
  { agentLedgerParameters with
    charge := (470431909 / 250000000000 : ℝ)
    frame := (182309501191 / 125000000000 : ℝ)
    root := (4410843123 / 500000000000 : ℝ) }

noncomputable def scalar12263 : ScalarCertificate 12263 world12263 agent12263 where
  dimensionLo := 12263
  dimensionHi := 12263
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2061923999 / 1000000000000 : ℝ)
  frameLo := (63189653717 / 100000000000 : ℝ)
  frameHi := (182309501191 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12263]
  agentFrame_pos := by norm_num only [agent12263]
  worldRadius := (2061923999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12263]
  retainedCharge := (470431909 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1991701061 / 1000000000000 : ℝ)
  lowerTail := (28445863 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9772685957 / 1000000000000 : ℝ)
  ledger := by
    have h : (596125161 / 500000000000 : ℚ) +
        (10336903193 / 1000000000000000000 : ℚ) / (2061923999 / 1000000000000 : ℚ) ^ 2 +
        (470431909 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1991701061 / 1000000000000 : ℚ) + (28445863 / 12500000000 : ℚ) ≤
        (9772685957 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((596125161 / 500000000000 : ℚ) +
        (10336903193 / 1000000000000000000 : ℚ) / (2061923999 / 1000000000000 : ℚ) ^ 2 +
        (470431909 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1991701061 / 1000000000000 : ℚ) + (28445863 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((9772685957 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12263]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12263 :
    2 * 160 < 12263 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998883 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12263 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12264 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12264. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12264 : WorldParameters where
  hiddenCharge := (119220127 / 100000000000 : ℝ)
  frame := (9873151051 / 15625000000 : ℝ)
  moment := (2066939503 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12264 : AgentParameters :=
  { agentLedgerParameters with
    charge := (940495001 / 500000000000 : ℝ)
    frame := (1458435160659 / 1000000000000 : ℝ)
    root := (8820949919 / 1000000000000 : ℝ) }

noncomputable def scalar12264 : ScalarCertificate 12264 world12264 agent12264 where
  dimensionLo := 12264
  dimensionHi := 12264
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2062278699 / 1000000000000 : ℝ)
  frameLo := (9873151051 / 15625000000 : ℝ)
  frameHi := (1458435160659 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12264]
  agentFrame_pos := by norm_num only [agent12264]
  worldRadius := (2062278699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12264]
  retainedCharge := (940495001 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1989934731 / 1000000000000 : ℝ)
  lowerTail := (45475667 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4883446177 / 500000000000 : ℝ)
  ledger := by
    have h : (119220127 / 100000000000 : ℚ) +
        (2066939503 / 200000000000000000 : ℚ) / (2062278699 / 1000000000000 : ℚ) ^ 2 +
        (940495001 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1989934731 / 1000000000000 : ℚ) + (45475667 / 20000000000 : ℚ) ≤
        (4883446177 / 500000000000 : ℚ) := by norm_num only
    have hc : (((119220127 / 100000000000 : ℚ) +
        (2066939503 / 200000000000000000 : ℚ) / (2062278699 / 1000000000000 : ℚ) ^ 2 +
        (940495001 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1989934731 / 1000000000000 : ℚ) + (45475667 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4883446177 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12264]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12264 :
    2 * 160 < 12264 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5371091 / 488281250 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12264 {← IO.monoMsNow}" : IO Unit)
