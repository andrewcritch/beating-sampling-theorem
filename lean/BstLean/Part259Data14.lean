import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12295 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12295. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12295 : WorldParameters where
  hiddenCharge := (238137461 / 200000000000 : ℝ)
  frame := (631421931603 / 1000000000000 : ℝ)
  moment := (5133323197 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12295 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1858450049 / 1000000000000 : ℝ)
    frame := (1457170717107 / 1000000000000 : ℝ)
    root := (1099779687 / 125000000000 : ℝ) }

noncomputable def scalar12295 : ScalarCertificate 12295 world12295 agent12295 where
  dimensionLo := 12295
  dimensionHi := 12295
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2073291499 / 1000000000000 : ℝ)
  frameLo := (631421931603 / 1000000000000 : ℝ)
  frameHi := (1457170717107 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12295]
  agentFrame_pos := by norm_num only [agent12295]
  worldRadius := (2073291499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12295]
  retainedCharge := (1858450049 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1936028931 / 1000000000000 : ℝ)
  lowerTail := (1108089441 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2397437651 / 250000000000 : ℝ)
  ledger := by
    have h : (238137461 / 200000000000 : ℚ) +
        (5133323197 / 500000000000000000 : ℚ) / (2073291499 / 1000000000000 : ℚ) ^ 2 +
        (1858450049 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1936028931 / 1000000000000 : ℚ) + (1108089441 / 500000000000 : ℚ) ≤
        (2397437651 / 250000000000 : ℚ) := by norm_num only
    have hc : (((238137461 / 200000000000 : ℚ) +
        (5133323197 / 500000000000000000 : ℚ) / (2073291499 / 1000000000000 : ℚ) ^ 2 +
        (1858450049 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1936028931 / 1000000000000 : ℚ) + (1108089441 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2397437651 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12295]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12295 :
    2 * 160 < 12295 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998333 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12295 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12296 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12296. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12296 : WorldParameters where
  hiddenCharge := (1190638681 / 1000000000000 : ℝ)
  frame := (631407141027 / 1000000000000 : ℝ)
  moment := (10264461633 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12296 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1857733377 / 1000000000000 : ℝ)
    frame := (728565069939 / 500000000000 : ℝ)
    root := (274922141 / 31250000000 : ℝ) }

noncomputable def scalar12296 : ScalarCertificate 12296 world12296 agent12296 where
  dimensionLo := 12296
  dimensionHi := 12296
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2073647099 / 1000000000000 : ℝ)
  frameLo := (631407141027 / 1000000000000 : ℝ)
  frameHi := (728565069939 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12296]
  agentFrame_pos := by norm_num only [agent12296]
  worldRadius := (2073647099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12296]
  retainedCharge := (1857733377 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1934317807 / 1000000000000 : ℝ)
  lowerTail := (2214348669 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1916823361 / 200000000000 : ℝ)
  ledger := by
    have h : (1190638681 / 1000000000000 : ℚ) +
        (10264461633 / 1000000000000000000 : ℚ) / (2073647099 / 1000000000000 : ℚ) ^ 2 +
        (1857733377 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1934317807 / 1000000000000 : ℚ) + (2214348669 / 1000000000000 : ℚ) ≤
        (1916823361 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1190638681 / 1000000000000 : ℚ) +
        (10264461633 / 1000000000000000000 : ℚ) / (2073647099 / 1000000000000 : ℚ) ^ 2 +
        (1857733377 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1934317807 / 1000000000000 : ℚ) + (2214348669 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1916823361 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12296]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12296 :
    2 * 160 < 12296 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999643 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12296 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12297 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12297. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12297 : WorldParameters where
  hiddenCharge := (1190590071 / 1000000000000 : ℝ)
  frame := (15784808823 / 25000000000 : ℝ)
  moment := (10262277521 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12297 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1857017349 / 1000000000000 : ℝ)
    frame := (91068099311 / 62500000000 : ℝ)
    root := (1759355951 / 200000000000 : ℝ) }

noncomputable def scalar12297 : ScalarCertificate 12297 world12297 agent12297 where
  dimensionLo := 12297
  dimensionHi := 12297
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2074002599 / 1000000000000 : ℝ)
  frameLo := (15784808823 / 25000000000 : ℝ)
  frameHi := (91068099311 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12297]
  agentFrame_pos := by norm_num only [agent12297]
  worldRadius := (2074002599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12297]
  retainedCharge := (1857017349 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (966304167 / 500000000000 : ℝ)
  lowerTail := (221252013 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (478924407 / 50000000000 : ℝ)
  ledger := by
    have h : (1190590071 / 1000000000000 : ℚ) +
        (10262277521 / 1000000000000000000 : ℚ) / (2074002599 / 1000000000000 : ℚ) ^ 2 +
        (1857017349 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (966304167 / 500000000000 : ℚ) + (221252013 / 100000000000 : ℚ) ≤
        (478924407 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1190590071 / 1000000000000 : ℚ) +
        (10262277521 / 1000000000000000000 : ℚ) / (2074002599 / 1000000000000 : ℚ) ^ 2 +
        (1857017349 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (966304167 / 500000000000 : ℚ) + (221252013 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((478924407 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12297]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12297 :
    2 * 160 < 12297 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499997521 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12297 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12298 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12298. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12298 : WorldParameters where
  hiddenCharge := (595270737 / 500000000000 : ℝ)
  frame := (7892219591 / 12500000000 : ℝ)
  moment := (10260094059 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12298 : AgentParameters :=
  { agentLedgerParameters with
    charge := (464075491 / 250000000000 : ℝ)
    frame := (291409810531 / 200000000000 : ℝ)
    root := (549753197 / 62500000000 : ℝ) }

noncomputable def scalar12298 : ScalarCertificate 12298 world12298 agent12298 where
  dimensionLo := 12298
  dimensionHi := 12298
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2074358299 / 1000000000000 : ℝ)
  frameLo := (7892219591 / 12500000000 : ℝ)
  frameHi := (291409810531 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12298]
  agentFrame_pos := by norm_num only [agent12298]
  worldRadius := (2074358299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12298]
  retainedCharge := (464075491 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (965450349 / 500000000000 : ℝ)
  lowerTail := (1105346729 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1196608037 / 125000000000 : ℝ)
  ledger := by
    have h : (595270737 / 500000000000 : ℚ) +
        (10260094059 / 1000000000000000000 : ℚ) / (2074358299 / 1000000000000 : ℚ) ^ 2 +
        (464075491 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (965450349 / 500000000000 : ℚ) + (1105346729 / 500000000000 : ℚ) ≤
        (1196608037 / 125000000000 : ℚ) := by norm_num only
    have hc : (((595270737 / 500000000000 : ℚ) +
        (10260094059 / 1000000000000000000 : ℚ) / (2074358299 / 1000000000000 : ℚ) ^ 2 +
        (464075491 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (965450349 / 500000000000 : ℚ) + (1105346729 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1196608037 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12298]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12298 :
    2 * 160 < 12298 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994851 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12298 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12299 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12299. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12299 : WorldParameters where
  hiddenCharge := (119049289 / 100000000000 : ℝ)
  frame := (631362784107 / 1000000000000 : ℝ)
  moment := (5128955623 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12299 : AgentParameters :=
  { agentLedgerParameters with
    charge := (927793611 / 500000000000 : ℝ)
    frame := (1457008530907 / 1000000000000 : ℝ)
    root := (8795322849 / 1000000000000 : ℝ) }

noncomputable def scalar12299 : ScalarCertificate 12299 world12299 agent12299 where
  dimensionLo := 12299
  dimensionHi := 12299
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2074713899 / 1000000000000 : ℝ)
  frameLo := (631362784107 / 1000000000000 : ℝ)
  frameHi := (1457008530907 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12299]
  agentFrame_pos := by norm_num only [agent12299]
  worldRadius := (2074713899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12299]
  retainedCharge := (927793611 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (77167789 / 40000000000 : ℝ)
  lowerTail := (441773691 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (956724559 / 100000000000 : ℝ)
  ledger := by
    have h : (119049289 / 100000000000 : ℚ) +
        (5128955623 / 500000000000000000 : ℚ) / (2074713899 / 1000000000000 : ℚ) ^ 2 +
        (927793611 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77167789 / 40000000000 : ℚ) + (441773691 / 200000000000 : ℚ) ≤
        (956724559 / 100000000000 : ℚ) := by norm_num only
    have hc : (((119049289 / 100000000000 : ℚ) +
        (5128955623 / 500000000000000000 : ℚ) / (2074713899 / 1000000000000 : ℚ) ^ 2 +
        (927793611 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77167789 / 40000000000 : ℚ) + (441773691 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((956724559 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12299]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12299 :
    2 * 160 < 12299 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499999523 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12299 {← IO.monoMsNow}" : IO Unit)
