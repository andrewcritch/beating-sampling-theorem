import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12250 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12250. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12250 : WorldParameters where
  hiddenCharge := (298222307 / 250000000000 : ℝ)
  frame := (31604503639 / 50000000000 : ℝ)
  moment := (1295704619 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12250 : AgentParameters :=
  { agentLedgerParameters with
    charge := (945688859 / 500000000000 : ℝ)
    frame := (5836035389 / 4000000000 : ℝ)
    root := (8831279739 / 1000000000000 : ℝ) }

noncomputable def scalar12250 : ScalarCertificate 12250 world12250 agent12250 where
  dimensionLo := 12250
  dimensionHi := 12250
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2057313599 / 1000000000000 : ℝ)
  frameLo := (31604503639 / 50000000000 : ℝ)
  frameHi := (5836035389 / 4000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12250]
  agentFrame_pos := by norm_num only [agent12250]
  worldRadius := (2057313599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12250]
  retainedCharge := (945688859 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2014827873 / 1000000000000 : ℝ)
  lowerTail := (2300349179 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9848480039 / 1000000000000 : ℝ)
  ledger := by
    have h : (298222307 / 250000000000 : ℚ) +
        (1295704619 / 125000000000000000 : ℚ) / (2057313599 / 1000000000000 : ℚ) ^ 2 +
        (945688859 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2014827873 / 1000000000000 : ℚ) + (2300349179 / 1000000000000 : ℚ) ≤
        (9848480039 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((298222307 / 250000000000 : ℚ) +
        (1295704619 / 125000000000000000 : ℚ) / (2057313599 / 1000000000000 : ℚ) ^ 2 +
        (945688859 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2014827873 / 1000000000000 : ℚ) + (2300349179 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9848480039 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12250]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12250 :
    2 * 160 < 12250 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995873 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12250 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12251 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12251. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12251 : WorldParameters where
  hiddenCharge := (29821 / 25000000 : ℝ)
  frame := (158018792613 / 250000000000 : ℝ)
  moment := (647713919 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12251 : AgentParameters :=
  { agentLedgerParameters with
    charge := (945315687 / 500000000000 : ℝ)
    frame := (1458967745683 / 1000000000000 : ℝ)
    root := (275954387 / 31250000000 : ℝ) }

noncomputable def scalar12251 : ScalarCertificate 12251 world12251 agent12251 where
  dimensionLo := 12251
  dimensionHi := 12251
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2057668199 / 1000000000000 : ℝ)
  frameLo := (158018792613 / 250000000000 : ℝ)
  frameHi := (1458967745683 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12251]
  agentFrame_pos := by norm_num only [agent12251]
  worldRadius := (2057668199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12251]
  retainedCharge := (945315687 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1006519013 / 500000000000 : ℝ)
  lowerTail := (459687949 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9842618203 / 1000000000000 : ℝ)
  ledger := by
    have h : (29821 / 25000000 : ℚ) +
        (647713919 / 62500000000000000 : ℚ) / (2057668199 / 1000000000000 : ℚ) ^ 2 +
        (945315687 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1006519013 / 500000000000 : ℚ) + (459687949 / 200000000000 : ℚ) ≤
        (9842618203 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((29821 / 25000000 : ℚ) +
        (647713919 / 62500000000000000 : ℚ) / (2057668199 / 1000000000000 : ℚ) ^ 2 +
        (945315687 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1006519013 / 500000000000 : ℚ) + (459687949 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9842618203 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12251]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12251 :
    2 * 160 < 12251 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994327 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12251 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12252 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12252. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12252 : WorldParameters where
  hiddenCharge := (596395393 / 500000000000 : ℝ)
  frame := (316030135311 / 500000000000 : ℝ)
  moment := (2590302279 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12252 : AgentParameters :=
  { agentLedgerParameters with
    charge := (944942853 / 500000000000 : ℝ)
    frame := (145892665909 / 100000000000 : ℝ)
    root := (8829801263 / 1000000000000 : ℝ) }

noncomputable def scalar12252 : ScalarCertificate 12252 world12252 agent12252 where
  dimensionLo := 12252
  dimensionHi := 12252
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2058022899 / 1000000000000 : ℝ)
  frameLo := (316030135311 / 500000000000 : ℝ)
  frameHi := (145892665909 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12252]
  agentFrame_pos := by norm_num only [agent12252]
  worldRadius := (2058022899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12252]
  retainedCharge := (944942853 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2011250081 / 1000000000000 : ℝ)
  lowerTail := (2296532231 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (983676159 / 100000000000 : ℝ)
  ledger := by
    have h : (596395393 / 500000000000 : ℚ) +
        (2590302279 / 250000000000000000 : ℚ) / (2058022899 / 1000000000000 : ℚ) ^ 2 +
        (944942853 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2011250081 / 1000000000000 : ℚ) + (2296532231 / 1000000000000 : ℚ) ≤
        (983676159 / 100000000000 : ℚ) := by norm_num only
    have hc : (((596395393 / 500000000000 : ℚ) +
        (2590302279 / 250000000000000000 : ℚ) / (2058022899 / 1000000000000 : ℚ) ^ 2 +
        (944942853 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2011250081 / 1000000000000 : ℚ) + (2296532231 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((983676159 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12252]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12252 :
    2 * 160 < 12252 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2749999331 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12252 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12253 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12253. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12253 : WorldParameters where
  hiddenCharge := (596370793 / 500000000000 : ℝ)
  frame := (63204537329 / 100000000000 : ℝ)
  moment := (10358996189 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12253 : AgentParameters :=
  { agentLedgerParameters with
    charge := (188914071 / 100000000000 : ℝ)
    frame := (729442796669 / 500000000000 : ℝ)
    root := (1103632797 / 125000000000 : ℝ) }

noncomputable def scalar12253 : ScalarCertificate 12253 world12253 agent12253 where
  dimensionLo := 12253
  dimensionHi := 12253
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2058377399 / 1000000000000 : ℝ)
  frameLo := (63204537329 / 100000000000 : ℝ)
  frameHi := (729442796669 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12253]
  agentFrame_pos := by norm_num only [agent12253]
  worldRadius := (2058377399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12253]
  retainedCharge := (188914071 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (502365931 / 250000000000 : ℝ)
  lowerTail := (2294626309 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9830910271 / 1000000000000 : ℝ)
  ledger := by
    have h : (596370793 / 500000000000 : ℚ) +
        (10358996189 / 1000000000000000000 : ℚ) / (2058377399 / 1000000000000 : ℚ) ^ 2 +
        (188914071 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (502365931 / 250000000000 : ℚ) + (2294626309 / 1000000000000 : ℚ) ≤
        (9830910271 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((596370793 / 500000000000 : ℚ) +
        (10358996189 / 1000000000000000000 : ℚ) / (2058377399 / 1000000000000 : ℚ) ^ 2 +
        (188914071 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (502365931 / 250000000000 : ℚ) + (2294626309 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9830910271 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12253]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12253 :
    2 * 160 < 12253 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499999423 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12253 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12254 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12254. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12254 : WorldParameters where
  hiddenCharge := (596346199 / 500000000000 : ℝ)
  frame := (316015239227 / 500000000000 : ℝ)
  moment := (5178391961 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12254 : AgentParameters :=
  { agentLedgerParameters with
    charge := (944198193 / 500000000000 : ℝ)
    frame := (72942227421 / 50000000000 : ℝ)
    root := (4414161861 / 500000000000 : ℝ) }

noncomputable def scalar12254 : ScalarCertificate 12254 world12254 agent12254 where
  dimensionLo := 12254
  dimensionHi := 12254
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2058731999 / 1000000000000 : ℝ)
  frameLo := (316015239227 / 500000000000 : ℝ)
  frameHi := (72942227421 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12254]
  agentFrame_pos := by norm_num only [agent12254]
  worldRadius := (2058731999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12254]
  retainedCharge := (944198193 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2007679299 / 1000000000000 : ℝ)
  lowerTail := (286590293 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9825064241 / 1000000000000 : ℝ)
  ledger := by
    have h : (596346199 / 500000000000 : ℚ) +
        (5178391961 / 500000000000000000 : ℚ) / (2058731999 / 1000000000000 : ℚ) ^ 2 +
        (944198193 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2007679299 / 1000000000000 : ℚ) + (286590293 / 125000000000 : ℚ) ≤
        (9825064241 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((596346199 / 500000000000 : ℚ) +
        (5178391961 / 500000000000000000 : ℚ) / (2058731999 / 1000000000000 : ℚ) ^ 2 +
        (944198193 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2007679299 / 1000000000000 : ℚ) + (286590293 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9825064241 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12254]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12254 :
    2 * 160 < 12254 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499999433 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12254 {← IO.monoMsNow}" : IO Unit)
