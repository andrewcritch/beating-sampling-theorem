import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12330 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12330. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12330 : WorldParameters where
  hiddenCharge := (594496681 / 500000000000 : ℝ)
  frame := (630905725747 / 1000000000000 : ℝ)
  moment := (10190564609 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12330 : AgentParameters :=
  { agentLedgerParameters with
    charge := (366749133 / 200000000000 : ℝ)
    frame := (291151524527 / 200000000000 : ℝ)
    root := (4386428039 / 500000000000 : ℝ) }

noncomputable def scalar12330 : ScalarCertificate 12330 world12330 agent12330 where
  dimensionLo := 12330
  dimensionHi := 12330
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2085750099 / 1000000000000 : ℝ)
  frameLo := (630905725747 / 1000000000000 : ℝ)
  frameHi := (291151524527 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12330]
  agentFrame_pos := by norm_num only [agent12330]
  worldRadius := (2085750099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12330]
  retainedCharge := (366749133 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (938570501 / 500000000000 : ℝ)
  lowerTail := (2153131537 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1879096149 / 200000000000 : ℝ)
  ledger := by
    have h : (594496681 / 500000000000 : ℚ) +
        (10190564609 / 1000000000000000000 : ℚ) / (2085750099 / 1000000000000 : ℚ) ^ 2 +
        (366749133 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (938570501 / 500000000000 : ℚ) + (2153131537 / 1000000000000 : ℚ) ≤
        (1879096149 / 200000000000 : ℚ) := by norm_num only
    have hc : (((594496681 / 500000000000 : ℚ) +
        (10190564609 / 1000000000000000000 : ℚ) / (2085750099 / 1000000000000 : ℚ) ^ 2 +
        (366749133 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (938570501 / 500000000000 : ℚ) + (2153131537 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1879096149 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12330]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12330 :
    2 * 160 < 12330 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (439999949 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12330 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12331 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12331. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12331 : WorldParameters where
  hiddenCharge := (594472601 / 500000000000 : ℝ)
  frame := (630891021169 / 1000000000000 : ℝ)
  moment := (2037680487 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12331 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1833051163 / 1000000000000 : ℝ)
    frame := (90982335593 / 62500000000 : ℝ)
    root := (8772134879 / 1000000000000 : ℝ) }

noncomputable def scalar12331 : ScalarCertificate 12331 world12331 agent12331 where
  dimensionLo := 12331
  dimensionHi := 12331
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2086106599 / 1000000000000 : ℝ)
  frameLo := (630891021169 / 1000000000000 : ℝ)
  frameHi := (90982335593 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12331]
  agentFrame_pos := by norm_num only [agent12331]
  worldRadius := (2086106599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12331]
  retainedCharge := (1833051163 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1875488041 / 1000000000000 : ℝ)
  lowerTail := (2151359923 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9390016113 / 1000000000000 : ℝ)
  ledger := by
    have h : (594472601 / 500000000000 : ℚ) +
        (2037680487 / 200000000000000000 : ℚ) / (2086106599 / 1000000000000 : ℚ) ^ 2 +
        (1833051163 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1875488041 / 1000000000000 : ℚ) + (2151359923 / 1000000000000 : ℚ) ≤
        (9390016113 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((594472601 / 500000000000 : ℚ) +
        (2037680487 / 200000000000000000 : ℚ) / (2086106599 / 1000000000000 : ℚ) ^ 2 +
        (1833051163 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1875488041 / 1000000000000 : ℚ) + (2151359923 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9390016113 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12331]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12331 :
    2 * 160 < 12331 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (549999983 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12331 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12332 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12332. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12332 : WorldParameters where
  hiddenCharge := (594448527 / 500000000000 : ℝ)
  frame := (157719079759 / 250000000000 : ℝ)
  moment := (10186240901 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12332 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1832357283 / 1000000000000 : ℝ)
    frame := (1455677136513 / 1000000000000 : ℝ)
    root := (1096426747 / 125000000000 : ℝ) }

noncomputable def scalar12332 : ScalarCertificate 12332 world12332 agent12332 where
  dimensionLo := 12332
  dimensionHi := 12332
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2086462999 / 1000000000000 : ℝ)
  frameLo := (157719079759 / 250000000000 : ℝ)
  frameHi := (1455677136513 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12332]
  agentFrame_pos := by norm_num only [agent12332]
  worldRadius := (2086462999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12332]
  retainedCharge := (1832357283 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (936918357 / 500000000000 : ℝ)
  lowerTail := (1074794979 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4692278261 / 500000000000 : ℝ)
  ledger := by
    have h : (594448527 / 500000000000 : ℚ) +
        (10186240901 / 1000000000000000000 : ℚ) / (2086462999 / 1000000000000 : ℚ) ^ 2 +
        (1832357283 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (936918357 / 500000000000 : ℚ) + (1074794979 / 500000000000 : ℚ) ≤
        (4692278261 / 500000000000 : ℚ) := by norm_num only
    have hc : (((594448527 / 500000000000 : ℚ) +
        (10186240901 / 1000000000000000000 : ℚ) / (2086462999 / 1000000000000 : ℚ) ^ 2 +
        (1832357283 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (936918357 / 500000000000 : ℚ) + (1074794979 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4692278261 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12332]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12332 :
    2 * 160 < 12332 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2749999797 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12332 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12333 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12333. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12333 : WorldParameters where
  hiddenCharge := (29721223 / 25000000000 : ℝ)
  frame := (157715404837 / 250000000000 : ℝ)
  moment := (10184080009 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12333 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1831664023 / 1000000000000 : ℝ)
    frame := (1455636923703 / 1000000000000 : ℝ)
    root := (8770693221 / 1000000000000 : ℝ) }

noncomputable def scalar12333 : ScalarCertificate 12333 world12333 agent12333 where
  dimensionLo := 12333
  dimensionHi := 12333
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2086819499 / 1000000000000 : ℝ)
  frameLo := (157715404837 / 250000000000 : ℝ)
  frameHi := (1455636923703 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12333]
  agentFrame_pos := by norm_num only [agent12333]
  worldRadius := (2086819499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12333]
  retainedCharge := (1831664023 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (46804677 / 25000000000 : ℝ)
  lowerTail := (2147821719 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1875820331 / 200000000000 : ℝ)
  ledger := by
    have h : (29721223 / 25000000000 : ℚ) +
        (10184080009 / 1000000000000000000 : ℚ) / (2086819499 / 1000000000000 : ℚ) ^ 2 +
        (1831664023 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (46804677 / 25000000000 : ℚ) + (2147821719 / 1000000000000 : ℚ) ≤
        (1875820331 / 200000000000 : ℚ) := by norm_num only
    have hc : (((29721223 / 25000000000 : ℚ) +
        (10184080009 / 1000000000000000000 : ℚ) / (2086819499 / 1000000000000 : ℚ) ^ 2 +
        (1831664023 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (46804677 / 25000000000 : ℚ) + (2147821719 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1875820331 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12333]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12333 :
    2 * 160 < 12333 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998639 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12333 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12334 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12334. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12334 : WorldParameters where
  hiddenCharge := (594400399 / 500000000000 : ℝ)
  frame := (78855865263 / 125000000000 : ℝ)
  moment := (2545479939 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12334 : AgentParameters :=
  { agentLedgerParameters with
    charge := (915485693 / 500000000000 : ℝ)
    frame := (145559672519 / 100000000000 : ℝ)
    root := (548123293 / 62500000000 : ℝ) }

noncomputable def scalar12334 : ScalarCertificate 12334 world12334 agent12334 where
  dimensionLo := 12334
  dimensionHi := 12334
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2087176099 / 1000000000000 : ℝ)
  frameLo := (78855865263 / 125000000000 : ℝ)
  frameHi := (145559672519 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12334]
  agentFrame_pos := by norm_num only [agent12334]
  worldRadius := (2087176099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12334]
  retainedCharge := (915485693 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (935269591 / 500000000000 : ℝ)
  lowerTail := (2146055241 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9373651591 / 1000000000000 : ℝ)
  ledger := by
    have h : (594400399 / 500000000000 : ℚ) +
        (2545479939 / 250000000000000000 : ℚ) / (2087176099 / 1000000000000 : ℚ) ^ 2 +
        (915485693 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (935269591 / 500000000000 : ℚ) + (2146055241 / 1000000000000 : ℚ) ≤
        (9373651591 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((594400399 / 500000000000 : ℚ) +
        (2545479939 / 250000000000000000 : ℚ) / (2087176099 / 1000000000000 : ℚ) ^ 2 +
        (915485693 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (935269591 / 500000000000 : ℚ) + (2146055241 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9373651591 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12334]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12334 :
    2 * 160 < 12334 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999911 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12334 {← IO.monoMsNow}" : IO Unit)
