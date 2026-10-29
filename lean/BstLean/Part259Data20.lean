import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12325 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12325. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12325 : WorldParameters where
  hiddenCharge := (1189234363 / 1000000000000 : ℝ)
  frame := (31548964267 / 50000000000 : ℝ)
  moment := (10201385103 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12325 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1837227529 / 1000000000000 : ℝ)
    frame := (1455959167839 / 1000000000000 : ℝ)
    root := (1755293037 / 200000000000 : ℝ) }

noncomputable def scalar12325 : ScalarCertificate 12325 world12325 agent12325 where
  dimensionLo := 12325
  dimensionHi := 12325
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2083967899 / 1000000000000 : ℝ)
  frameLo := (31548964267 / 50000000000 : ℝ)
  frameHi := (1455959167839 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12325]
  agentFrame_pos := by norm_num only [agent12325]
  worldRadius := (2083967899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12325]
  retainedCharge := (1837227529 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (377086159 / 200000000000 : ℝ)
  lowerTail := (2162014961 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9422876601 / 1000000000000 : ℝ)
  ledger := by
    have h : (1189234363 / 1000000000000 : ℚ) +
        (10201385103 / 1000000000000000000 : ℚ) / (2083967899 / 1000000000000 : ℚ) ^ 2 +
        (1837227529 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377086159 / 200000000000 : ℚ) + (2162014961 / 1000000000000 : ℚ) ≤
        (9422876601 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1189234363 / 1000000000000 : ℚ) +
        (10201385103 / 1000000000000000000 : ℚ) / (2083967899 / 1000000000000 : ℚ) ^ 2 +
        (1837227529 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377086159 / 200000000000 : ℚ) + (2162014961 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9422876601 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12325]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12325 :
    2 * 160 < 12325 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999581 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12325 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12326 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12326. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12326 : WorldParameters where
  hiddenCharge := (1189186137 / 1000000000000 : ℝ)
  frame := (25238582741 / 40000000000 : ℝ)
  moment := (254980493 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12326 : AgentParameters :=
  { agentLedgerParameters with
    charge := (459132477 / 250000000000 : ℝ)
    frame := (727959409777 / 500000000000 : ℝ)
    root := (8775742947 / 1000000000000 : ℝ) }

noncomputable def scalar12326 : ScalarCertificate 12326 world12326 agent12326 where
  dimensionLo := 12326
  dimensionHi := 12326
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2084324299 / 1000000000000 : ℝ)
  frameLo := (25238582741 / 40000000000 : ℝ)
  frameHi := (727959409777 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12326]
  agentFrame_pos := by norm_num only [agent12326]
  worldRadius := (2084324299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12326]
  retainedCharge := (459132477 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1883769487 / 1000000000000 : ℝ)
  lowerTail := (2160234877 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (588586731 / 62500000000 : ℝ)
  ledger := by
    have h : (1189186137 / 1000000000000 : ℚ) +
        (254980493 / 25000000000000000 : ℚ) / (2084324299 / 1000000000000 : ℚ) ^ 2 +
        (459132477 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1883769487 / 1000000000000 : ℚ) + (2160234877 / 1000000000000 : ℚ) ≤
        (588586731 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1189186137 / 1000000000000 : ℚ) +
        (254980493 / 25000000000000000 : ℚ) / (2084324299 / 1000000000000 : ℚ) ^ 2 +
        (459132477 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1883769487 / 1000000000000 : ℚ) + (2160234877 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((588586731 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12326]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12326 :
    2 * 160 < 12326 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999461 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12326 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12327 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12327. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12327 : WorldParameters where
  hiddenCharge := (1189137923 / 1000000000000 : ℝ)
  frame := (630949854159 / 1000000000000 : ℝ)
  moment := (509852749 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12327 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1835832911 / 1000000000000 : ℝ)
    frame := (291175698297 / 200000000000 : ℝ)
    root := (438751043 / 50000000000 : ℝ) }

noncomputable def scalar12327 : ScalarCertificate 12327 world12327 agent12327 where
  dimensionLo := 12327
  dimensionHi := 12327
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2084680699 / 1000000000000 : ℝ)
  frameLo := (630949854159 / 1000000000000 : ℝ)
  frameHi := (291175698297 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12327]
  agentFrame_pos := by norm_num only [agent12327]
  worldRadius := (2084680699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12327]
  retainedCharge := (1835832911 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (75284391 / 40000000000 : ℝ)
  lowerTail := (2158456413 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1882380709 / 200000000000 : ℝ)
  ledger := by
    have h : (1189137923 / 1000000000000 : ℚ) +
        (509852749 / 50000000000000000 : ℚ) / (2084680699 / 1000000000000 : ℚ) ^ 2 +
        (1835832911 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (75284391 / 40000000000 : ℚ) + (2158456413 / 1000000000000 : ℚ) ≤
        (1882380709 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1189137923 / 1000000000000 : ℚ) +
        (509852749 / 50000000000000000 : ℚ) / (2084680699 / 1000000000000 : ℚ) ^ 2 +
        (1835832911 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (75284391 / 40000000000 : ℚ) + (2158456413 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1882380709 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12327]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12327 :
    2 * 160 < 12327 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999749 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12327 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12328 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12328. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12328 : WorldParameters where
  hiddenCharge := (1189089723 / 1000000000000 : ℝ)
  frame := (630935142241 / 1000000000000 : ℝ)
  moment := (10194890881 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12328 : AgentParameters :=
  { agentLedgerParameters with
    charge := (917568269 / 500000000000 : ℝ)
    frame := (727919091813 / 500000000000 : ℝ)
    root := (2193574767 / 250000000000 : ℝ) }

noncomputable def scalar12328 : ScalarCertificate 12328 world12328 agent12328 where
  dimensionLo := 12328
  dimensionHi := 12328
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2085037199 / 1000000000000 : ℝ)
  frameLo := (630935142241 / 1000000000000 : ℝ)
  frameHi := (727919091813 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12328]
  agentFrame_pos := by norm_num only [agent12328]
  worldRadius := (2085037199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12328]
  retainedCharge := (917568269 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1880451921 / 1000000000000 : ℝ)
  lowerTail := (2156679839 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1175803057 / 125000000000 : ℝ)
  ledger := by
    have h : (1189089723 / 1000000000000 : ℚ) +
        (10194890881 / 1000000000000000000 : ℚ) / (2085037199 / 1000000000000 : ℚ) ^ 2 +
        (917568269 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1880451921 / 1000000000000 : ℚ) + (2156679839 / 1000000000000 : ℚ) ≤
        (1175803057 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1189089723 / 1000000000000 : ℚ) +
        (10194890881 / 1000000000000000000 : ℚ) / (2085037199 / 1000000000000 : ℚ) ^ 2 +
        (917568269 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1880451921 / 1000000000000 : ℚ) + (2156679839 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1175803057 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12328]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12328 :
    2 * 160 < 12328 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998743 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12328 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12329 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12329. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12329 : WorldParameters where
  hiddenCharge := (9289387 / 7812500000 : ℝ)
  frame := (630920432771 / 1000000000000 : ℝ)
  moment := (79630683 / 7812500000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12329 : AgentParameters :=
  { agentLedgerParameters with
    charge := (183444079 / 100000000000 : ℝ)
    frame := (291159579193 / 200000000000 : ℝ)
    root := (350943097 / 40000000000 : ℝ) }

noncomputable def scalar12329 : ScalarCertificate 12329 world12329 agent12329 where
  dimensionLo := 12329
  dimensionHi := 12329
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2085393599 / 1000000000000 : ℝ)
  frameLo := (630920432771 / 1000000000000 : ℝ)
  frameHi := (291159579193 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12329]
  agentFrame_pos := by norm_num only [agent12329]
  worldRadius := (2085393599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12329]
  retainedCharge := (183444079 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (37575911 / 20000000000 : ℝ)
  lowerTail := (430980953 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9400950111 / 1000000000000 : ℝ)
  ledger := by
    have h : (9289387 / 7812500000 : ℚ) +
        (79630683 / 7812500000000000 : ℚ) / (2085393599 / 1000000000000 : ℚ) ^ 2 +
        (183444079 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (37575911 / 20000000000 : ℚ) + (430980953 / 200000000000 : ℚ) ≤
        (9400950111 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((9289387 / 7812500000 : ℚ) +
        (79630683 / 7812500000000000 : ℚ) / (2085393599 / 1000000000000 : ℚ) ^ 2 +
        (183444079 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (37575911 / 20000000000 : ℚ) + (430980953 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9400950111 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12329]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12329 :
    2 * 160 < 12329 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999996411 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12329 {← IO.monoMsNow}" : IO Unit)
