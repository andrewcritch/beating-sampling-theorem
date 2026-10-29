import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12315 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12315. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12315 : WorldParameters where
  hiddenCharge := (594858677 / 500000000000 : ℝ)
  frame := (6311265883 / 10000000000 : ℝ)
  moment := (102230743 / 10000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12315 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1844238277 / 1000000000000 : ℝ)
    frame := (1456362785369 / 1000000000000 : ℝ)
    root := (4391850099 / 500000000000 : ℝ) }

noncomputable def scalar12315 : ScalarCertificate 12315 world12315 agent12315 where
  dimensionLo := 12315
  dimensionHi := 12315
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2080405699 / 1000000000000 : ℝ)
  frameLo := (6311265883 / 10000000000 : ℝ)
  frameHi := (1456362785369 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12315]
  agentFrame_pos := by norm_num only [agent12315]
  worldRadius := (2080405699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12315]
  retainedCharge := (1844238277 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (951066619 / 500000000000 : ℝ)
  lowerTail := (1089952749 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9478025569 / 1000000000000 : ℝ)
  ledger := by
    have h : (594858677 / 500000000000 : ℚ) +
        (102230743 / 10000000000000000 : ℚ) / (2080405699 / 1000000000000 : ℚ) ^ 2 +
        (1844238277 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (951066619 / 500000000000 : ℚ) + (1089952749 / 500000000000 : ℚ) ≤
        (9478025569 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((594858677 / 500000000000 : ℚ) +
        (102230743 / 10000000000000000 : ℚ) / (2080405699 / 1000000000000 : ℚ) ^ 2 +
        (1844238277 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (951066619 / 500000000000 : ℚ) + (1089952749 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9478025569 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12315]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12315 :
    2 * 160 < 12315 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998991 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12315 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12316 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12316. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12316 : WorldParameters where
  hiddenCharge := (237933799 / 200000000000 : ℝ)
  frame := (157777961741 / 250000000000 : ℝ)
  moment := (5110451241 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12316 : AgentParameters :=
  { agentLedgerParameters with
    charge := (57610449 / 31250000000 : ℝ)
    frame := (145632258627 / 100000000000 : ℝ)
    root := (8782975727 / 1000000000000 : ℝ) }

noncomputable def scalar12316 : ScalarCertificate 12316 world12316 agent12316 where
  dimensionLo := 12316
  dimensionHi := 12316
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2080761399 / 1000000000000 : ℝ)
  frameLo := (157777961741 / 250000000000 : ℝ)
  frameHi := (145632258627 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12316]
  agentFrame_pos := by norm_num only [agent12316]
  worldRadius := (2080761399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12316]
  retainedCharge := (57610449 / 31250000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1900456289 / 1000000000000 : ℝ)
  lowerTail := (2178109883 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4736245809 / 500000000000 : ℝ)
  ledger := by
    have h : (237933799 / 200000000000 : ℚ) +
        (5110451241 / 500000000000000000 : ℚ) / (2080761399 / 1000000000000 : ℚ) ^ 2 +
        (57610449 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1900456289 / 1000000000000 : ℚ) + (2178109883 / 1000000000000 : ℚ) ≤
        (4736245809 / 500000000000 : ℚ) := by norm_num only
    have hc : (((237933799 / 200000000000 : ℚ) +
        (5110451241 / 500000000000000000 : ℚ) / (2080761399 / 1000000000000 : ℚ) ^ 2 +
        (57610449 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1900456289 / 1000000000000 : ℚ) + (2178109883 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4736245809 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12316]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12316 :
    2 * 160 < 12316 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (1099999457 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12316 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12317 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12317. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12317 : WorldParameters where
  hiddenCharge := (23792413 / 20000000000 : ℝ)
  frame := (631097108083 / 1000000000000 : ℝ)
  moment := (1021873131 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12317 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1842831091 / 1000000000000 : ℝ)
    frame := (291256480317 / 200000000000 : ℝ)
    root := (4391125703 / 500000000000 : ℝ) }

noncomputable def scalar12317 : ScalarCertificate 12317 world12317 agent12317 where
  dimensionLo := 12317
  dimensionHi := 12317
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2081117299 / 1000000000000 : ℝ)
  frameLo := (631097108083 / 1000000000000 : ℝ)
  frameHi := (291256480317 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12317]
  agentFrame_pos := by norm_num only [agent12317]
  worldRadius := (2081117299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12317]
  retainedCharge := (1842831091 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1898781139 / 1000000000000 : ℝ)
  lowerTail := (1088158049 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9466962393 / 1000000000000 : ℝ)
  ledger := by
    have h : (23792413 / 20000000000 : ℚ) +
        (1021873131 / 100000000000000000 : ℚ) / (2081117299 / 1000000000000 : ℚ) ^ 2 +
        (1842831091 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1898781139 / 1000000000000 : ℚ) + (1088158049 / 500000000000 : ℚ) ≤
        (9466962393 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((23792413 / 20000000000 : ℚ) +
        (1021873131 / 100000000000000000 : ℚ) / (2081117299 / 1000000000000 : ℚ) ^ 2 +
        (1842831091 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1898781139 / 1000000000000 : ℚ) + (1088158049 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9466962393 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12317]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12317 :
    2 * 160 < 12317 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499997551 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12317 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12318 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12318. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12318 : WorldParameters where
  hiddenCharge := (594786159 / 500000000000 : ℝ)
  frame := (78885296457 / 125000000000 : ℝ)
  moment := (10216560781 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12318 : AgentParameters :=
  { agentLedgerParameters with
    charge := (460532111 / 250000000000 : ℝ)
    frame := (364060532909 / 250000000000 : ℝ)
    root := (8781527383 / 1000000000000 : ℝ) }

noncomputable def scalar12318 : ScalarCertificate 12318 world12318 agent12318 where
  dimensionLo := 12318
  dimensionHi := 12318
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2081473299 / 1000000000000 : ℝ)
  frameLo := (78885296457 / 125000000000 : ℝ)
  frameHi := (364060532909 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12318]
  agentFrame_pos := by norm_num only [agent12318]
  worldRadius := (2081473299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12318]
  retainedCharge := (460532111 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (948553639 / 500000000000 : ℝ)
  lowerTail := (271815439 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4730718489 / 500000000000 : ℝ)
  ledger := by
    have h : (594786159 / 500000000000 : ℚ) +
        (10216560781 / 1000000000000000000 : ℚ) / (2081473299 / 1000000000000 : ℚ) ^ 2 +
        (460532111 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (948553639 / 500000000000 : ℚ) + (271815439 / 125000000000 : ℚ) ≤
        (4730718489 / 500000000000 : ℚ) := by norm_num only
    have hc : (((594786159 / 500000000000 : ℚ) +
        (10216560781 / 1000000000000000000 : ℚ) / (2081473299 / 1000000000000 : ℚ) ^ 2 +
        (460532111 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (948553639 / 500000000000 : ℚ) + (271815439 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4730718489 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12318]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12318 :
    2 * 160 < 12318 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995857 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12318 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12319 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12319. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12319 : WorldParameters where
  hiddenCharge := (1189523999 / 1000000000000 : ℝ)
  frame := (631067637683 / 1000000000000 : ℝ)
  moment := (10214390897 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12319 : AgentParameters :=
  { agentLedgerParameters with
    charge := (460356607 / 250000000000 : ℝ)
    frame := (728100823721 / 500000000000 : ℝ)
    root := (878080351 / 100000000000 : ℝ) }

noncomputable def scalar12319 : ScalarCertificate 12319 world12319 agent12319 where
  dimensionLo := 12319
  dimensionHi := 12319
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2081829699 / 1000000000000 : ℝ)
  frameLo := (631067637683 / 1000000000000 : ℝ)
  frameHi := (728100823721 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12319]
  agentFrame_pos := by norm_num only [agent12319]
  worldRadius := (2081829699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12319]
  retainedCharge := (460356607 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (379086831 / 200000000000 : ℝ)
  lowerTail := (2172731453 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (18468581 / 1953125000 : ℝ)
  ledger := by
    have h : (1189523999 / 1000000000000 : ℚ) +
        (10214390897 / 1000000000000000000 : ℚ) / (2081829699 / 1000000000000 : ℚ) ^ 2 +
        (460356607 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (379086831 / 200000000000 : ℚ) + (2172731453 / 1000000000000 : ℚ) ≤
        (18468581 / 1953125000 : ℚ) := by norm_num only
    have hc : (((1189523999 / 1000000000000 : ℚ) +
        (10214390897 / 1000000000000000000 : ℚ) / (2081829699 / 1000000000000 : ℚ) ^ 2 +
        (460356607 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (379086831 / 200000000000 : ℚ) + (2172731453 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((18468581 / 1953125000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12319]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12319 :
    2 * 160 < 12319 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (1099999949 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12319 {← IO.monoMsNow}" : IO Unit)
