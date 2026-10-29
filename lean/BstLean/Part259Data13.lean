import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12290 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12290. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12290 : WorldParameters where
  hiddenCharge := (18608291 / 15625000000 : ℝ)
  frame := (315747960763 / 500000000000 : ℝ)
  moment := (642348747 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12290 : AgentParameters :=
  { agentLedgerParameters with
    charge := (931021549 / 500000000000 : ℝ)
    frame := (1457373875241 / 1000000000000 : ℝ)
    root := (2200471493 / 250000000000 : ℝ) }

noncomputable def scalar12290 : ScalarCertificate 12290 world12290 agent12290 where
  dimensionLo := 12290
  dimensionHi := 12290
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2071513799 / 1000000000000 : ℝ)
  frameLo := (315747960763 / 500000000000 : ℝ)
  frameHi := (1457373875241 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12290]
  agentFrame_pos := by norm_num only [agent12290]
  worldRadius := (2071513799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12290]
  retainedCharge := (931021549 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (972305439 / 500000000000 : ℝ)
  lowerTail := (222535657 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4808997787 / 500000000000 : ℝ)
  ledger := by
    have h : (18608291 / 15625000000 : ℚ) +
        (642348747 / 62500000000000000 : ℚ) / (2071513799 / 1000000000000 : ℚ) ^ 2 +
        (931021549 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (972305439 / 500000000000 : ℚ) + (222535657 / 100000000000 : ℚ) ≤
        (4808997787 / 500000000000 : ℚ) := by norm_num only
    have hc : (((18608291 / 15625000000 : ℚ) +
        (642348747 / 62500000000000000 : ℚ) / (2071513799 / 1000000000000 : ℚ) ^ 2 +
        (931021549 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (972305439 / 500000000000 : ℚ) + (222535657 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4808997787 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12290]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12290 :
    2 * 160 < 12290 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995209 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12290 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12291 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12291. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12291 : WorldParameters where
  hiddenCharge := (1190881933 / 1000000000000 : ℝ)
  frame := (3157405593 / 5000000000 : ℝ)
  moment := (10275391939 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12291 : AgentParameters :=
  { agentLedgerParameters with
    charge := (372264639 / 200000000000 : ℝ)
    frame := (29146664029 / 20000000000 : ℝ)
    root := (8801155777 / 1000000000000 : ℝ) }

noncomputable def scalar12291 : ScalarCertificate 12291 world12291 agent12291 where
  dimensionLo := 12291
  dimensionHi := 12291
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2071869399 / 1000000000000 : ℝ)
  frameLo := (3157405593 / 5000000000 : ℝ)
  frameHi := (29146664029 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12291]
  agentFrame_pos := by norm_num only [agent12291]
  worldRadius := (2071869399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12291]
  retainedCharge := (372264639 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (121430689 / 62500000000 : ℝ)
  lowerTail := (2223517529 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1922467261 / 200000000000 : ℝ)
  ledger := by
    have h : (1190881933 / 1000000000000 : ℚ) +
        (10275391939 / 1000000000000000000 : ℚ) / (2071869399 / 1000000000000 : ℚ) ^ 2 +
        (372264639 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (121430689 / 62500000000 : ℚ) + (2223517529 / 1000000000000 : ℚ) ≤
        (1922467261 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1190881933 / 1000000000000 : ℚ) +
        (10275391939 / 1000000000000000000 : ℚ) / (2071869399 / 1000000000000 : ℚ) ^ 2 +
        (372264639 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (121430689 / 62500000000 : ℚ) + (2223517529 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1922467261 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12291]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12291 :
    2 * 160 < 12291 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999619 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12291 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12292 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12292. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12292 : WorldParameters where
  hiddenCharge := (148854157 / 125000000000 : ℝ)
  frame := (126293263629 / 200000000000 : ℝ)
  moment := (10273204577 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12292 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1860603939 / 1000000000000 : ℝ)
    frame := (91080784627 / 62500000000 : ℝ)
    root := (2200106471 / 250000000000 : ℝ) }

noncomputable def scalar12292 : ScalarCertificate 12292 world12292 agent12292 where
  dimensionLo := 12292
  dimensionHi := 12292
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2072224799 / 1000000000000 : ℝ)
  frameLo := (126293263629 / 200000000000 : ℝ)
  frameHi := (91080784627 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12292]
  agentFrame_pos := by norm_num only [agent12292]
  worldRadius := (2072224799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12292]
  retainedCharge := (1860603939 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1213233 / 625000000 : ℝ)
  lowerTail := (2221680131 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9606682357 / 1000000000000 : ℝ)
  ledger := by
    have h : (148854157 / 125000000000 : ℚ) +
        (10273204577 / 1000000000000000000 : ℚ) / (2072224799 / 1000000000000 : ℚ) ^ 2 +
        (1860603939 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1213233 / 625000000 : ℚ) + (2221680131 / 1000000000000 : ℚ) ≤
        (9606682357 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((148854157 / 125000000000 : ℚ) +
        (10273204577 / 1000000000000000000 : ℚ) / (2072224799 / 1000000000000 : ℚ) ^ 2 +
        (1860603939 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1213233 / 625000000 : ℚ) + (2221680131 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9606682357 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12292]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12292 :
    2 * 160 < 12292 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (54999983 / 5000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12292 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12293 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12293. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12293 : WorldParameters where
  hiddenCharge := (1190784593 / 1000000000000 : ℝ)
  frame := (631451520161 / 1000000000000 : ℝ)
  moment := (5135508933 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12293 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1859885329 / 1000000000000 : ℝ)
    frame := (1457251921241 / 1000000000000 : ℝ)
    root := (4399848109 / 500000000000 : ℝ) }

noncomputable def scalar12293 : ScalarCertificate 12293 world12293 agent12293 where
  dimensionLo := 12293
  dimensionHi := 12293
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2072580399 / 1000000000000 : ℝ)
  frameLo := (631451520161 / 1000000000000 : ℝ)
  frameHi := (1457251921241 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12293]
  agentFrame_pos := by norm_num only [agent12293]
  worldRadius := (2072580399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12293]
  retainedCharge := (1859885329 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (969728253 / 500000000000 : ℝ)
  lowerTail := (221984469 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4800516709 / 500000000000 : ℝ)
  ledger := by
    have h : (1190784593 / 1000000000000 : ℚ) +
        (5135508933 / 500000000000000000 : ℚ) / (2072580399 / 1000000000000 : ℚ) ^ 2 +
        (1859885329 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (969728253 / 500000000000 : ℚ) + (221984469 / 100000000000 : ℚ) ≤
        (4800516709 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1190784593 / 1000000000000 : ℚ) +
        (5135508933 / 500000000000000000 : ℚ) / (2072580399 / 1000000000000 : ℚ) ^ 2 +
        (1859885329 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (969728253 / 500000000000 : ℚ) + (221984469 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4800516709 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12293]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12293 :
    2 * 160 < 12293 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998119 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12293 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12294 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12294. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12294 : WorldParameters where
  hiddenCharge := (595367971 / 500000000000 : ℝ)
  frame := (631436724647 / 1000000000000 : ℝ)
  moment := (2053766361 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12294 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1859167367 / 1000000000000 : ℝ)
    frame := (182151413617 / 125000000000 : ℝ)
    root := (439948339 / 50000000000 : ℝ) }

noncomputable def scalar12294 : ScalarCertificate 12294 world12294 agent12294 where
  dimensionLo := 12294
  dimensionHi := 12294
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2072935899 / 1000000000000 : ℝ)
  frameLo := (631436724647 / 1000000000000 : ℝ)
  frameHi := (182151413617 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12294]
  agentFrame_pos := by norm_num only [agent12294]
  worldRadius := (2072935899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12294]
  retainedCharge := (1859167367 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (484435459 / 250000000000 : ℝ)
  lowerTail := (2218010889 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2398847389 / 250000000000 : ℝ)
  ledger := by
    have h : (595367971 / 500000000000 : ℚ) +
        (2053766361 / 200000000000000000 : ℚ) / (2072935899 / 1000000000000 : ℚ) ^ 2 +
        (1859167367 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (484435459 / 250000000000 : ℚ) + (2218010889 / 1000000000000 : ℚ) ≤
        (2398847389 / 250000000000 : ℚ) := by norm_num only
    have hc : (((595367971 / 500000000000 : ℚ) +
        (2053766361 / 200000000000000000 : ℚ) / (2072935899 / 1000000000000 : ℚ) ^ 2 +
        (1859167367 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (484435459 / 250000000000 : ℚ) + (2218010889 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2398847389 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12294]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12294 :
    2 * 160 < 12294 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (219999963 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12294 {← IO.monoMsNow}" : IO Unit)
