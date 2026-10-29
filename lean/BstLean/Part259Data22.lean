import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12335 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12335. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12335 : WorldParameters where
  hiddenCharge := (118875269 / 100000000000 : ℝ)
  frame := (78854028413 / 125000000000 : ℝ)
  moment := (636235009 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12335 : AgentParameters :=
  { agentLedgerParameters with
    charge := (228784921 / 125000000000 : ℝ)
    frame := (727778276341 / 500000000000 : ℝ)
    root := (175385049 / 20000000000 : ℝ) }

noncomputable def scalar12335 : ScalarCertificate 12335 world12335 agent12335 where
  dimensionLo := 12335
  dimensionHi := 12335
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2087532599 / 1000000000000 : ℝ)
  frameLo := (78854028413 / 125000000000 : ℝ)
  frameHi := (727778276341 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12335]
  agentFrame_pos := by norm_num only [agent12335]
  worldRadius := (2087532599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12335]
  retainedCharge := (228784921 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (116805809 / 62500000000 : ℝ)
  lowerTail := (2144290447 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9368206623 / 1000000000000 : ℝ)
  ledger := by
    have h : (118875269 / 100000000000 : ℚ) +
        (636235009 / 62500000000000000 : ℚ) / (2087532599 / 1000000000000 : ℚ) ^ 2 +
        (228784921 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (116805809 / 62500000000 : ℚ) + (2144290447 / 1000000000000 : ℚ) ≤
        (9368206623 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((118875269 / 100000000000 : ℚ) +
        (636235009 / 62500000000000000 : ℚ) / (2087532599 / 1000000000000 : ℚ) ^ 2 +
        (228784921 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (116805809 / 62500000000 : ℚ) + (2144290447 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9368206623 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12335]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12335 :
    2 * 160 < 12335 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995043 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12335 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12336 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12336. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12336 : WorldParameters where
  hiddenCharge := (237740919 / 200000000000 : ℝ)
  frame := (315408767473 / 500000000000 : ℝ)
  moment := (2544400293 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12336 : AgentParameters :=
  { agentLedgerParameters with
    charge := (182958797 / 100000000000 : ℝ)
    frame := (727758197227 / 500000000000 : ℝ)
    root := (219213309 / 25000000000 : ℝ) }

noncomputable def scalar12336 : ScalarCertificate 12336 world12336 agent12336 where
  dimensionLo := 12336
  dimensionHi := 12336
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2087889099 / 1000000000000 : ℝ)
  frameLo := (315408767473 / 500000000000 : ℝ)
  frameHi := (727758197227 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12336]
  agentFrame_pos := by norm_num only [agent12336]
  worldRadius := (2087889099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12336]
  retainedCharge := (182958797 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (466812063 / 250000000000 : ℝ)
  lowerTail := (2142527217 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4681383147 / 500000000000 : ℝ)
  ledger := by
    have h : (237740919 / 200000000000 : ℚ) +
        (2544400293 / 250000000000000000 : ℚ) / (2087889099 / 1000000000000 : ℚ) ^ 2 +
        (182958797 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (466812063 / 250000000000 : ℚ) + (2142527217 / 1000000000000 : ℚ) ≤
        (4681383147 / 500000000000 : ℚ) := by norm_num only
    have hc : (((237740919 / 200000000000 : ℚ) +
        (2544400293 / 250000000000000000 : ℚ) / (2087889099 / 1000000000000 : ℚ) ^ 2 +
        (182958797 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (466812063 / 250000000000 : ℚ) + (2142527217 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4681383147 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12336]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12336 :
    2 * 160 < 12336 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199998933 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12336 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12337 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12337. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12337 : WorldParameters where
  hiddenCharge := (1188656513 / 1000000000000 : ℝ)
  frame := (63080284503 / 100000000000 : ℝ)
  moment := (254386071 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12337 : AgentParameters :=
  { agentLedgerParameters with
    charge := (228612149 / 125000000000 : ℝ)
    frame := (11370908207 / 7812500000 : ℝ)
    root := (2191953141 / 250000000000 : ℝ) }

noncomputable def scalar12337 : ScalarCertificate 12337 world12337 agent12337 where
  dimensionLo := 12337
  dimensionHi := 12337
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2088245699 / 1000000000000 : ℝ)
  frameLo := (63080284503 / 100000000000 : ℝ)
  frameHi := (11370908207 / 7812500000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12337]
  agentFrame_pos := by norm_num only [agent12337]
  worldRadius := (2088245699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12337]
  retainedCharge := (228612149 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1865605369 / 1000000000000 : ℝ)
  lowerTail := (2140765821 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2339332727 / 250000000000 : ℝ)
  ledger := by
    have h : (1188656513 / 1000000000000 : ℚ) +
        (254386071 / 25000000000000000 : ℚ) / (2088245699 / 1000000000000 : ℚ) ^ 2 +
        (228612149 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1865605369 / 1000000000000 : ℚ) + (2140765821 / 1000000000000 : ℚ) ≤
        (2339332727 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1188656513 / 1000000000000 : ℚ) +
        (254386071 / 25000000000000000 : ℚ) / (2088245699 / 1000000000000 : ℚ) ^ 2 +
        (228612149 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1865605369 / 1000000000000 : ℚ) + (2140765821 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2339332727 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12337]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12337 :
    2 * 160 < 12337 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998753 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12337 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12338 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12338. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12338 : WorldParameters where
  hiddenCharge := (297152111 / 250000000000 : ℝ)
  frame := (157697039389 / 250000000000 : ℝ)
  moment := (10173285147 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12338 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1828207031 / 1000000000000 : ℝ)
    frame := (727718066259 / 500000000000 : ℝ)
    root := (2191773229 / 250000000000 : ℝ) }

noncomputable def scalar12338 : ScalarCertificate 12338 world12338 agent12338 where
  dimensionLo := 12338
  dimensionHi := 12338
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2088602299 / 1000000000000 : ℝ)
  frameLo := (157697039389 / 250000000000 : ℝ)
  frameHi := (727718066259 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12338]
  agentFrame_pos := by norm_num only [agent12338]
  worldRadius := (2088602299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12338]
  retainedCharge := (1828207031 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1863964093 / 1000000000000 : ℝ)
  lowerTail := (2139006063 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2337975073 / 250000000000 : ℝ)
  ledger := by
    have h : (297152111 / 250000000000 : ℚ) +
        (10173285147 / 1000000000000000000 : ℚ) / (2088602299 / 1000000000000 : ℚ) ^ 2 +
        (1828207031 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1863964093 / 1000000000000 : ℚ) + (2139006063 / 1000000000000 : ℚ) ≤
        (2337975073 / 250000000000 : ℚ) := by norm_num only
    have hc : (((297152111 / 250000000000 : ℚ) +
        (10173285147 / 1000000000000000000 : ℚ) / (2088602299 / 1000000000000 : ℚ) ^ 2 +
        (1828207031 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1863964093 / 1000000000000 : ℚ) + (2139006063 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2337975073 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12338]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12338 :
    2 * 160 < 12338 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995253 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12338 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12339 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12339. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12339 : WorldParameters where
  hiddenCharge := (1188560389 / 1000000000000 : ℝ)
  frame := (630773472523 / 1000000000000 : ℝ)
  moment := (5085564047 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12339 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1827517489 / 1000000000000 : ℝ)
    frame := (727698014397 / 500000000000 : ℝ)
    root := (8766373489 / 1000000000000 : ℝ) }

noncomputable def scalar12339 : ScalarCertificate 12339 world12339 agent12339 where
  dimensionLo := 12339
  dimensionHi := 12339
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2088958799 / 1000000000000 : ℝ)
  frameLo := (630773472523 / 1000000000000 : ℝ)
  frameHi := (727698014397 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12339]
  agentFrame_pos := by norm_num only [agent12339]
  worldRadius := (2088958799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12339]
  retainedCharge := (1827517489 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1862324327 / 1000000000000 : ℝ)
  lowerTail := (534311957 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1869294891 / 200000000000 : ℝ)
  ledger := by
    have h : (1188560389 / 1000000000000 : ℚ) +
        (5085564047 / 500000000000000000 : ℚ) / (2088958799 / 1000000000000 : ℚ) ^ 2 +
        (1827517489 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1862324327 / 1000000000000 : ℚ) + (534311957 / 250000000000 : ℚ) ≤
        (1869294891 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1188560389 / 1000000000000 : ℚ) +
        (5085564047 / 500000000000000000 : ℚ) / (2088958799 / 1000000000000 : ℚ) ^ 2 +
        (1827517489 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1862324327 / 1000000000000 : ℚ) + (534311957 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1869294891 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12339]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12339 :
    2 * 160 < 12339 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998083 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12339 {← IO.monoMsNow}" : IO Unit)
