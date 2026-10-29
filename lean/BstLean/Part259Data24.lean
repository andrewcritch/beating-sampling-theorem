import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12345 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12345. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12345 : WorldParameters where
  hiddenCharge := (118827233 / 100000000000 : ℝ)
  frame := (78835676693 / 125000000000 : ℝ)
  moment := (5079099591 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12345 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1823393171 / 1000000000000 : ℝ)
    frame := (181894474879 / 125000000000 : ℝ)
    root := (4381030889 / 500000000000 : ℝ) }

noncomputable def scalar12345 : ScalarCertificate 12345 world12345 agent12345 where
  dimensionLo := 12345
  dimensionHi := 12345
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2091098599 / 1000000000000 : ℝ)
  frameLo := (78835676693 / 125000000000 : ℝ)
  frameHi := (181894474879 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12345]
  agentFrame_pos := by norm_num only [agent12345]
  worldRadius := (2091098599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12345]
  retainedCharge := (1823393171 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1852521229 / 1000000000000 : ℝ)
  lowerTail := (2126734457 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1862804219 / 200000000000 : ℝ)
  ledger := by
    have h : (118827233 / 100000000000 : ℚ) +
        (5079099591 / 500000000000000000 : ℚ) / (2091098599 / 1000000000000 : ℚ) ^ 2 +
        (1823393171 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1852521229 / 1000000000000 : ℚ) + (2126734457 / 1000000000000 : ℚ) ≤
        (1862804219 / 200000000000 : ℚ) := by norm_num only
    have hc : (((118827233 / 100000000000 : ℚ) +
        (5079099591 / 500000000000000000 : ℚ) / (2091098599 / 1000000000000 : ℚ) ^ 2 +
        (1823393171 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1852521229 / 1000000000000 : ℚ) + (2126734457 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1862804219 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12345]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12345 :
    2 * 160 < 12345 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (687499787 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12345 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12346 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12346. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12346 : WorldParameters where
  hiddenCharge := (237644873 / 200000000000 : ℝ)
  frame := (315335372789 / 500000000000 : ℝ)
  moment := (2539011649 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12346 : AgentParameters :=
  { agentLedgerParameters with
    charge := (56959623 / 31250000000 : ℝ)
    frame := (181889478017 / 125000000000 : ℝ)
    root := (4380671947 / 500000000000 : ℝ) }

noncomputable def scalar12346 : ScalarCertificate 12346 world12346 agent12346 where
  dimensionLo := 12346
  dimensionHi := 12346
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2091455299 / 1000000000000 : ℝ)
  frameLo := (315335372789 / 500000000000 : ℝ)
  frameHi := (181889478017 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12346]
  agentFrame_pos := by norm_num only [agent12346]
  worldRadius := (2091455299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12346]
  retainedCharge := (56959623 / 31250000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1850893117 / 1000000000000 : ℝ)
  lowerTail := (531247013 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4654314461 / 500000000000 : ℝ)
  ledger := by
    have h : (237644873 / 200000000000 : ℚ) +
        (2539011649 / 250000000000000000 : ℚ) / (2091455299 / 1000000000000 : ℚ) ^ 2 +
        (56959623 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1850893117 / 1000000000000 : ℚ) + (531247013 / 250000000000 : ℚ) ≤
        (4654314461 / 500000000000 : ℚ) := by norm_num only
    have hc : (((237644873 / 200000000000 : ℚ) +
        (2539011649 / 250000000000000000 : ℚ) / (2091455299 / 1000000000000 : ℚ) ^ 2 +
        (56959623 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1850893117 / 1000000000000 : ℚ) + (531247013 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4654314461 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12346]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12346 :
    2 * 160 < 12346 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997583 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12346 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12347 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12347. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12347 : WorldParameters where
  hiddenCharge := (594088207 / 500000000000 : ℝ)
  frame := (39416005003 / 62500000000 : ℝ)
  moment := (10153894647 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12347 : AgentParameters :=
  { agentLedgerParameters with
    charge := (911011657 / 500000000000 : ℝ)
    frame := (363768967321 / 250000000000 : ℝ)
    root := (876062623 / 100000000000 : ℝ) }

noncomputable def scalar12347 : ScalarCertificate 12347 world12347 agent12347 where
  dimensionLo := 12347
  dimensionHi := 12347
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2091811999 / 1000000000000 : ℝ)
  frameLo := (39416005003 / 62500000000 : ℝ)
  frameHi := (363768967321 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12347]
  agentFrame_pos := by norm_num only [agent12347]
  worldRadius := (2091811999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12347]
  retainedCharge := (911011657 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1849266641 / 1000000000000 : ℝ)
  lowerTail := (530810827 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9303241557 / 1000000000000 : ℝ)
  ledger := by
    have h : (594088207 / 500000000000 : ℚ) +
        (10153894647 / 1000000000000000000 : ℚ) / (2091811999 / 1000000000000 : ℚ) ^ 2 +
        (911011657 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1849266641 / 1000000000000 : ℚ) + (530810827 / 250000000000 : ℚ) ≤
        (9303241557 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((594088207 / 500000000000 : ℚ) +
        (10153894647 / 1000000000000000000 : ℚ) / (2091811999 / 1000000000000 : ℚ) ^ 2 +
        (911011657 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1849266641 / 1000000000000 : ℚ) + (530810827 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9303241557 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12347]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12347 :
    2 * 160 < 12347 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998377 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12347 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12348 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12348. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12348 : WorldParameters where
  hiddenCharge := (1188128477 / 1000000000000 : ℝ)
  frame := (630641416953 / 1000000000000 : ℝ)
  moment := (1268967917 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12348 : AgentParameters :=
  { agentLedgerParameters with
    charge := (227667413 / 125000000000 : ℝ)
    frame := (727517967233 / 500000000000 : ℝ)
    root := (8759908857 / 1000000000000 : ℝ) }

noncomputable def scalar12348 : ScalarCertificate 12348 world12348 agent12348 where
  dimensionLo := 12348
  dimensionHi := 12348
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2092168699 / 1000000000000 : ℝ)
  frameLo := (630641416953 / 1000000000000 : ℝ)
  frameHi := (727517967233 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12348]
  agentFrame_pos := by norm_num only [agent12348]
  worldRadius := (2092168699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12348]
  retainedCharge := (227667413 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (461910469 / 250000000000 : ℝ)
  lowerTail := (21215003 / 10000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (185957183 / 20000000000 : ℝ)
  ledger := by
    have h : (1188128477 / 1000000000000 : ℚ) +
        (1268967917 / 125000000000000000 : ℚ) / (2092168699 / 1000000000000 : ℚ) ^ 2 +
        (227667413 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (461910469 / 250000000000 : ℚ) + (21215003 / 10000000000 : ℚ) ≤
        (185957183 / 20000000000 : ℚ) := by norm_num only
    have hc : (((1188128477 / 1000000000000 : ℚ) +
        (1268967917 / 125000000000000000 : ℚ) / (2092168699 / 1000000000000 : ℚ) ^ 2 +
        (227667413 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (461910469 / 250000000000 : ℚ) + (21215003 / 10000000000 : ℚ) : ℚ) : ℝ) ≤
        ((185957183 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12348]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12348 :
    2 * 160 < 12348 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (68749963 / 6250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12348 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12349 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12349. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12349 : WorldParameters where
  hiddenCharge := (148510069 / 125000000000 : ℝ)
  frame := (157656689073 / 250000000000 : ℝ)
  moment := (10149592661 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12349 : AgentParameters :=
  { agentLedgerParameters with
    charge := (56895497 / 31250000000 : ℝ)
    frame := (727498006909 / 500000000000 : ℝ)
    root := (547449477 / 62500000000 : ℝ) }

noncomputable def scalar12349 : ScalarCertificate 12349 world12349 agent12349 where
  dimensionLo := 12349
  dimensionHi := 12349
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2092525399 / 1000000000000 : ℝ)
  frameLo := (157656689073 / 250000000000 : ℝ)
  frameHi := (727498006909 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12349]
  agentFrame_pos := by norm_num only [agent12349]
  worldRadius := (2092525399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12349]
  retainedCharge := (56895497 / 31250000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (923009317 / 500000000000 : ℝ)
  lowerTail := (1059879417 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9292481319 / 1000000000000 : ℝ)
  ledger := by
    have h : (148510069 / 125000000000 : ℚ) +
        (10149592661 / 1000000000000000000 : ℚ) / (2092525399 / 1000000000000 : ℚ) ^ 2 +
        (56895497 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (923009317 / 500000000000 : ℚ) + (1059879417 / 500000000000 : ℚ) ≤
        (9292481319 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((148510069 / 125000000000 : ℚ) +
        (10149592661 / 1000000000000000000 : ℚ) / (2092525399 / 1000000000000 : ℚ) ^ 2 +
        (56895497 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (923009317 / 500000000000 : ℚ) + (1059879417 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9292481319 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12349]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12349 :
    2 * 160 < 12349 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995569 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12349 {← IO.monoMsNow}" : IO Unit)
