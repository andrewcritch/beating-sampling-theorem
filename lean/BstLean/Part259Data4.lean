import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12245 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12245. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12245 : WorldParameters where
  hiddenCharge := (119313557 / 100000000000 : ℝ)
  frame := (632164621913 / 1000000000000 : ℝ)
  moment := (2075343623 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12245 : AgentParameters :=
  { agentLedgerParameters with
    charge := (118444973 / 62500000000 : ℝ)
    frame := (1459214656439 / 1000000000000 : ℝ)
    root := (4417490013 / 500000000000 : ℝ) }

noncomputable def scalar12245 : ScalarCertificate 12245 world12245 agent12245 where
  dimensionLo := 12245
  dimensionHi := 12245
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2055541099 / 1000000000000 : ℝ)
  frameLo := (632164621913 / 1000000000000 : ℝ)
  frameHi := (1459214656439 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12245]
  agentFrame_pos := by norm_num only [agent12245]
  worldRadius := (2055541099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12245]
  retainedCharge := (118444973 / 62500000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1011902501 / 500000000000 : ℝ)
  lowerTail := (577481133 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4938934381 / 500000000000 : ℝ)
  ledger := by
    have h : (119313557 / 100000000000 : ℚ) +
        (2075343623 / 200000000000000000 : ℚ) / (2055541099 / 1000000000000 : ℚ) ^ 2 +
        (118444973 / 62500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1011902501 / 500000000000 : ℚ) + (577481133 / 250000000000 : ℚ) ≤
        (4938934381 / 500000000000 : ℚ) := by norm_num only
    have hc : (((119313557 / 100000000000 : ℚ) +
        (2075343623 / 200000000000000000 : ℚ) / (2055541099 / 1000000000000 : ℚ) ^ 2 +
        (118444973 / 62500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1011902501 / 500000000000 : ℚ) + (577481133 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4938934381 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12245]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12245 :
    2 * 160 < 12245 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199998963 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12245 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12246 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12246. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12246 : WorldParameters where
  hiddenCharge := (596543137 / 500000000000 : ℝ)
  frame := (126429941417 / 200000000000 : ℝ)
  moment := (10374500559 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12246 : AgentParameters :=
  { agentLedgerParameters with
    charge := (378873969 / 200000000000 : ℝ)
    frame := (1459173456349 / 1000000000000 : ℝ)
    root := (8834239499 / 1000000000000 : ℝ) }

noncomputable def scalar12246 : ScalarCertificate 12246 world12246 agent12246 where
  dimensionLo := 12246
  dimensionHi := 12246
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2055895599 / 1000000000000 : ℝ)
  frameLo := (126429941417 / 200000000000 : ℝ)
  frameHi := (1459173456349 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12246]
  agentFrame_pos := by norm_num only [agent12246]
  worldRadius := (2055895599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12246]
  retainedCharge := (378873969 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2022005939 / 1000000000000 : ℝ)
  lowerTail := (72125181 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9871980419 / 1000000000000 : ℝ)
  ledger := by
    have h : (596543137 / 500000000000 : ℚ) +
        (10374500559 / 1000000000000000000 : ℚ) / (2055895599 / 1000000000000 : ℚ) ^ 2 +
        (378873969 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2022005939 / 1000000000000 : ℚ) + (72125181 / 31250000000 : ℚ) ≤
        (9871980419 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((596543137 / 500000000000 : ℚ) +
        (10374500559 / 1000000000000000000 : ℚ) / (2055895599 / 1000000000000 : ℚ) ^ 2 +
        (378873969 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2022005939 / 1000000000000 : ℚ) + (72125181 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((9871980419 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12246]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12246 :
    2 * 160 < 12246 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994111 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12246 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12247 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12247. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12247 : WorldParameters where
  hiddenCharge := (18641203 / 15625000000 : ℝ)
  frame := (632134794759 / 1000000000000 : ℝ)
  moment := (2074456733 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12247 : AgentParameters :=
  { agentLedgerParameters with
    charge := (946810399 / 500000000000 : ℝ)
    frame := (729566135639 / 500000000000 : ℝ)
    root := (1104187401 / 125000000000 : ℝ) }

noncomputable def scalar12247 : ScalarCertificate 12247 world12247 agent12247 where
  dimensionLo := 12247
  dimensionHi := 12247
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2056250099 / 1000000000000 : ℝ)
  frameLo := (632134794759 / 1000000000000 : ℝ)
  frameHi := (729566135639 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12247]
  agentFrame_pos := by norm_num only [agent12247]
  worldRadius := (2056250099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12247]
  retainedCharge := (946810399 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (63131521 / 31250000000 : ℝ)
  lowerTail := (115304443 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9866097327 / 1000000000000 : ℝ)
  ledger := by
    have h : (18641203 / 15625000000 : ℚ) +
        (2074456733 / 200000000000000000 : ℚ) / (2056250099 / 1000000000000 : ℚ) ^ 2 +
        (946810399 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (63131521 / 31250000000 : ℚ) + (115304443 / 50000000000 : ℚ) ≤
        (9866097327 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((18641203 / 15625000000 : ℚ) +
        (2074456733 / 200000000000000000 : ℚ) / (2056250099 / 1000000000000 : ℚ) ^ 2 +
        (946810399 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (63131521 / 31250000000 : ℚ) + (115304443 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9866097327 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12247]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12247 :
    2 * 160 < 12247 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (17187497 / 1562500000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12247 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12248 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12248. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12248 : WorldParameters where
  hiddenCharge := (298246931 / 250000000000 : ℝ)
  frame := (632119884933 / 1000000000000 : ℝ)
  moment := (10370067433 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12248 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1892872429 / 1000000000000 : ℝ)
    frame := (1459091112977 / 1000000000000 : ℝ)
    root := (176655183 / 20000000000 : ℝ) }

noncomputable def scalar12248 : ScalarCertificate 12248 world12248 agent12248 where
  dimensionLo := 12248
  dimensionHi := 12248
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2056604599 / 1000000000000 : ℝ)
  frameLo := (632119884933 / 1000000000000 : ℝ)
  frameHi := (1459091112977 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12248]
  agentFrame_pos := by norm_num only [agent12248]
  worldRadius := (2056604599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12248]
  retainedCharge := (1892872429 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2018413269 / 1000000000000 : ℝ)
  lowerTail := (288021727 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4930109817 / 500000000000 : ℝ)
  ledger := by
    have h : (298246931 / 250000000000 : ℚ) +
        (10370067433 / 1000000000000000000 : ℚ) / (2056604599 / 1000000000000 : ℚ) ^ 2 +
        (1892872429 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2018413269 / 1000000000000 : ℚ) + (288021727 / 125000000000 : ℚ) ≤
        (4930109817 / 500000000000 : ℚ) := by norm_num only
    have hc : (((298246931 / 250000000000 : ℚ) +
        (10370067433 / 1000000000000000000 : ℚ) / (2056604599 / 1000000000000 : ℚ) ^ 2 +
        (1892872429 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2018413269 / 1000000000000 : ℚ) + (288021727 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4930109817 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12248]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12248 :
    2 * 160 < 12248 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994729 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12248 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12249 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12249. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12249 : WorldParameters where
  hiddenCharge := (1192938469 / 1000000000000 : ℝ)
  frame := (632104977607 / 1000000000000 : ℝ)
  moment := (5183925931 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12249 : AgentParameters :=
  { agentLedgerParameters with
    charge := (29564449 / 15625000000 : ℝ)
    frame := (729524984839 / 500000000000 : ℝ)
    root := (69000151 / 7812500000 : ℝ) }

noncomputable def scalar12249 : ScalarCertificate 12249 world12249 agent12249 where
  dimensionLo := 12249
  dimensionHi := 12249
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2056959099 / 1000000000000 : ℝ)
  frameLo := (632104977607 / 1000000000000 : ℝ)
  frameHi := (729524984839 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12249]
  agentFrame_pos := by norm_num only [agent12249]
  worldRadius := (2056959099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12249]
  retainedCharge := (29564449 / 15625000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1008309829 / 500000000000 : ℝ)
  lowerTail := (71945643 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9854347181 / 1000000000000 : ℝ)
  ledger := by
    have h : (1192938469 / 1000000000000 : ℚ) +
        (5183925931 / 500000000000000000 : ℚ) / (2056959099 / 1000000000000 : ℚ) ^ 2 +
        (29564449 / 15625000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1008309829 / 500000000000 : ℚ) + (71945643 / 31250000000 : ℚ) ≤
        (9854347181 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1192938469 / 1000000000000 : ℚ) +
        (5183925931 / 500000000000000000 : ℚ) / (2056959099 / 1000000000000 : ℚ) ^ 2 +
        (29564449 / 15625000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1008309829 / 500000000000 : ℚ) + (71945643 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((9854347181 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12249]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12249 :
    2 * 160 < 12249 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995997 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12249 {← IO.monoMsNow}" : IO Unit)
