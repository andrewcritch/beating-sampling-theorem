import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12310 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12310. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12310 : WorldParameters where
  hiddenCharge := (74372459 / 62500000000 : ℝ)
  frame := (631200331831 / 1000000000000 : ℝ)
  moment := (2046788613 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12310 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1847767317 / 1000000000000 : ℝ)
    frame := (364141018409 / 250000000000 : ℝ)
    root := (4393663071 / 500000000000 : ℝ) }

noncomputable def scalar12310 : ScalarCertificate 12310 world12310 agent12310 where
  dimensionLo := 12310
  dimensionHi := 12310
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2078626499 / 1000000000000 : ℝ)
  frameLo := (631200331831 / 1000000000000 : ℝ)
  frameHi := (364141018409 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12310]
  agentFrame_pos := by norm_num only [agent12310]
  worldRadius := (2078626499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12310]
  retainedCharge := (1847767317 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (382108563 / 200000000000 : ℝ)
  lowerTail := (2188908687 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2376442543 / 250000000000 : ℝ)
  ledger := by
    have h : (74372459 / 62500000000 : ℚ) +
        (2046788613 / 200000000000000000 : ℚ) / (2078626499 / 1000000000000 : ℚ) ^ 2 +
        (1847767317 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (382108563 / 200000000000 : ℚ) + (2188908687 / 1000000000000 : ℚ) ≤
        (2376442543 / 250000000000 : ℚ) := by norm_num only
    have hc : (((74372459 / 62500000000 : ℚ) +
        (2046788613 / 200000000000000000 : ℚ) / (2078626499 / 1000000000000 : ℚ) ^ 2 +
        (1847767317 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (382108563 / 200000000000 : ℚ) + (2188908687 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2376442543 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12310]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12310 :
    2 * 160 < 12310 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998239 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12310 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12311 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12311. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12311 : WorldParameters where
  hiddenCharge := (29747773 / 25000000000 : ℝ)
  frame := (631185578209 / 1000000000000 : ℝ)
  moment := (10231768021 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12311 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1847060241 / 1000000000000 : ℝ)
    frame := (182065472359 / 125000000000 : ℝ)
    root := (4393300237 / 500000000000 : ℝ) }

noncomputable def scalar12311 : ScalarCertificate 12311 world12311 agent12311 where
  dimensionLo := 12311
  dimensionHi := 12311
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2078982399 / 1000000000000 : ℝ)
  frameLo := (631185578209 / 1000000000000 : ℝ)
  frameHi := (182065472359 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12311]
  agentFrame_pos := by norm_num only [agent12311]
  worldRadius := (2078982399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12311]
  retainedCharge := (1847060241 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1908857557 / 1000000000000 : ℝ)
  lowerTail := (2187104669 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4750105639 / 500000000000 : ℝ)
  ledger := by
    have h : (29747773 / 25000000000 : ℚ) +
        (10231768021 / 1000000000000000000 : ℚ) / (2078982399 / 1000000000000 : ℚ) ^ 2 +
        (1847060241 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1908857557 / 1000000000000 : ℚ) + (2187104669 / 1000000000000 : ℚ) ≤
        (4750105639 / 500000000000 : ℚ) := by norm_num only
    have hc : (((29747773 / 25000000000 : ℚ) +
        (10231768021 / 1000000000000000000 : ℚ) / (2078982399 / 1000000000000 : ℚ) ^ 2 +
        (1847060241 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1908857557 / 1000000000000 : ℚ) + (2187104669 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4750105639 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12311]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12311 :
    2 * 160 < 12311 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997153 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12311 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12312 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12312. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12312 : WorldParameters where
  hiddenCharge := (297465627 / 250000000000 : ℝ)
  frame := (315585413523 / 500000000000 : ℝ)
  moment := (5114796811 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12312 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1846353799 / 1000000000000 : ℝ)
    frame := (91030219027 / 62500000000 : ℝ)
    root := (1757175021 / 200000000000 : ℝ) }

noncomputable def scalar12312 : ScalarCertificate 12312 world12312 agent12312 where
  dimensionLo := 12312
  dimensionHi := 12312
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2079338199 / 1000000000000 : ℝ)
  frameLo := (315585413523 / 500000000000 : ℝ)
  frameHi := (91030219027 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12312]
  agentFrame_pos := by norm_num only [agent12312]
  worldRadius := (2079338199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12312]
  retainedCharge := (1846353799 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (119198373 / 62500000000 : ℝ)
  lowerTail := (437060467 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2373664381 / 250000000000 : ℝ)
  ledger := by
    have h : (297465627 / 250000000000 : ℚ) +
        (5114796811 / 500000000000000000 : ℚ) / (2079338199 / 1000000000000 : ℚ) ^ 2 +
        (1846353799 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119198373 / 62500000000 : ℚ) + (437060467 / 200000000000 : ℚ) ≤
        (2373664381 / 250000000000 : ℚ) := by norm_num only
    have hc : (((297465627 / 250000000000 : ℚ) +
        (5114796811 / 500000000000000000 : ℚ) / (2079338199 / 1000000000000 : ℚ) ^ 2 +
        (1846353799 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119198373 / 62500000000 : ℚ) + (437060467 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2373664381 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12312]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12312 :
    2 * 160 < 12312 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999171 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12312 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12313 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12313. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12313 : WorldParameters where
  hiddenCharge := (118981411 / 100000000000 : ℝ)
  frame := (631156078341 / 1000000000000 : ℝ)
  moment := (1022741987 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12313 : AgentParameters :=
  { agentLedgerParameters with
    charge := (230705999 / 125000000000 : ℝ)
    frame := (1456443244441 / 1000000000000 : ℝ)
    root := (8785149887 / 1000000000000 : ℝ) }

noncomputable def scalar12313 : ScalarCertificate 12313 world12313 agent12313 where
  dimensionLo := 12313
  dimensionHi := 12313
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2079693999 / 1000000000000 : ℝ)
  frameLo := (631156078341 / 1000000000000 : ℝ)
  frameHi := (1456443244441 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12313]
  agentFrame_pos := by norm_num only [agent12313]
  worldRadius := (2079693999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12313]
  retainedCharge := (230705999 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (381098393 / 200000000000 : ℝ)
  lowerTail := (436700321 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9489108517 / 1000000000000 : ℝ)
  ledger := by
    have h : (118981411 / 100000000000 : ℚ) +
        (1022741987 / 100000000000000000 : ℚ) / (2079693999 / 1000000000000 : ℚ) ^ 2 +
        (230705999 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (381098393 / 200000000000 : ℚ) + (436700321 / 200000000000 : ℚ) ≤
        (9489108517 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((118981411 / 100000000000 : ℚ) +
        (1022741987 / 100000000000000000 : ℚ) / (2079693999 / 1000000000000 : ℚ) ^ 2 +
        (230705999 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (381098393 / 200000000000 : ℚ) + (436700321 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9489108517 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12313]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12313 :
    2 * 160 < 12313 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998597 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12313 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12314 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12314. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12314 : WorldParameters where
  hiddenCharge := (47590629 / 40000000000 : ℝ)
  frame := (157785333023 / 250000000000 : ℝ)
  moment := (5112623381 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12314 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1844942819 / 1000000000000 : ℝ)
    frame := (1456403004757 / 1000000000000 : ℝ)
    root := (8784424967 / 1000000000000 : ℝ) }

noncomputable def scalar12314 : ScalarCertificate 12314 world12314 agent12314 where
  dimensionLo := 12314
  dimensionHi := 12314
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2080049799 / 1000000000000 : ℝ)
  frameLo := (157785333023 / 250000000000 : ℝ)
  frameHi := (1456403004757 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12314]
  agentFrame_pos := by norm_num only [agent12314]
  worldRadius := (2080049799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12314]
  retainedCharge := (1844942819 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1903811739 / 1000000000000 : ℝ)
  lowerTail := (2181702673 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4741782319 / 500000000000 : ℝ)
  ledger := by
    have h : (47590629 / 40000000000 : ℚ) +
        (5112623381 / 500000000000000000 : ℚ) / (2080049799 / 1000000000000 : ℚ) ^ 2 +
        (1844942819 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1903811739 / 1000000000000 : ℚ) + (2181702673 / 1000000000000 : ℚ) ≤
        (4741782319 / 500000000000 : ℚ) := by norm_num only
    have hc : (((47590629 / 40000000000 : ℚ) +
        (5112623381 / 500000000000000000 : ℚ) / (2080049799 / 1000000000000 : ℚ) ^ 2 +
        (1844942819 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1903811739 / 1000000000000 : ℚ) + (2181702673 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4741782319 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12314]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12314 :
    2 * 160 < 12314 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999863 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12314 {← IO.monoMsNow}" : IO Unit)
