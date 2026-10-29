import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12340 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12340. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12340 : WorldParameters where
  hiddenCharge := (594256173 / 500000000000 : ℝ)
  frame := (63075878993 / 100000000000 : ℝ)
  moment := (10168971679 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12340 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1826828563 / 1000000000000 : ℝ)
    frame := (727677972587 / 500000000000 : ℝ)
    root := (2191413589 / 250000000000 : ℝ) }

noncomputable def scalar12340 : ScalarCertificate 12340 world12340 agent12340 where
  dimensionLo := 12340
  dimensionHi := 12340
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2089315399 / 1000000000000 : ℝ)
  frameLo := (63075878993 / 100000000000 : ℝ)
  frameHi := (727677972587 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12340]
  agentFrame_pos := by norm_num only [agent12340]
  worldRadius := (2089315399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12340]
  retainedCharge := (1826828563 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (465171599 / 250000000000 : ℝ)
  lowerTail := (1067745729 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9341053617 / 1000000000000 : ℝ)
  ledger := by
    have h : (594256173 / 500000000000 : ℚ) +
        (10168971679 / 1000000000000000000 : ℚ) / (2089315399 / 1000000000000 : ℚ) ^ 2 +
        (1826828563 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (465171599 / 250000000000 : ℚ) + (1067745729 / 500000000000 : ℚ) ≤
        (9341053617 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((594256173 / 500000000000 : ℚ) +
        (10168971679 / 1000000000000000000 : ℚ) / (2089315399 / 1000000000000 : ℚ) ^ 2 +
        (1826828563 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (465171599 / 250000000000 : ℚ) + (1067745729 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9341053617 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12340]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12340 :
    2 * 160 < 12340 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995449 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12340 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12341 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12341. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12341 : WorldParameters where
  hiddenCharge := (1188464317 / 1000000000000 : ℝ)
  frame := (39421506861 / 62500000000 : ℝ)
  moment := (10166815903 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12341 : AgentParameters :=
  { agentLedgerParameters with
    charge := (913070127 / 500000000000 : ℝ)
    frame := (145531587579 / 100000000000 : ℝ)
    root := (876493537 / 100000000000 : ℝ) }

noncomputable def scalar12341 : ScalarCertificate 12341 world12341 agent12341 where
  dimensionLo := 12341
  dimensionHi := 12341
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2089671999 / 1000000000000 : ℝ)
  frameLo := (39421506861 / 62500000000 : ℝ)
  frameHi := (145531587579 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12341]
  agentFrame_pos := by norm_num only [agent12341]
  worldRadius := (2089671999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12341]
  retainedCharge := (913070127 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (929525001 / 500000000000 : ℝ)
  lowerTail := (426747329 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (583477337 / 62500000000 : ℝ)
  ledger := by
    have h : (1188464317 / 1000000000000 : ℚ) +
        (10166815903 / 1000000000000000000 : ℚ) / (2089671999 / 1000000000000 : ℚ) ^ 2 +
        (913070127 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (929525001 / 500000000000 : ℚ) + (426747329 / 200000000000 : ℚ) ≤
        (583477337 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1188464317 / 1000000000000 : ℚ) +
        (10166815903 / 1000000000000000000 : ℚ) / (2089671999 / 1000000000000 : ℚ) ^ 2 +
        (913070127 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (929525001 / 500000000000 : ℚ) + (426747329 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((583477337 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12341]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12341 :
    2 * 160 < 12341 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499999549 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12341 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12342 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12342. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12342 : WorldParameters where
  hiddenCharge := (11884163 / 10000000000 : ℝ)
  frame := (630729432061 / 1000000000000 : ℝ)
  moment := (2032932153 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12342 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1825452561 / 1000000000000 : ℝ)
    frame := (29105516647 / 20000000000 : ℝ)
    root := (4382108339 / 500000000000 : ℝ) }

noncomputable def scalar12342 : ScalarCertificate 12342 world12342 agent12342 where
  dimensionLo := 12342
  dimensionHi := 12342
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2090028599 / 1000000000000 : ℝ)
  frameLo := (630729432061 / 1000000000000 : ℝ)
  frameHi := (29105516647 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12342]
  agentFrame_pos := by norm_num only [agent12342]
  worldRadius := (2090028599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12342]
  retainedCharge := (1825452561 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1857415363 / 1000000000000 : ℝ)
  lowerTail := (8328061 / 3906250000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9330226227 / 1000000000000 : ℝ)
  ledger := by
    have h : (11884163 / 10000000000 : ℚ) +
        (2032932153 / 200000000000000000 : ℚ) / (2090028599 / 1000000000000 : ℚ) ^ 2 +
        (1825452561 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1857415363 / 1000000000000 : ℚ) + (8328061 / 3906250000 : ℚ) ≤
        (9330226227 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((11884163 / 10000000000 : ℚ) +
        (2032932153 / 200000000000000000 : ℚ) / (2090028599 / 1000000000000 : ℚ) ^ 2 +
        (1825452561 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1857415363 / 1000000000000 : ℚ) + (8328061 / 3906250000 : ℚ) : ℚ) : ℝ) ≤
        ((9330226227 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12342]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12342 :
    2 * 160 < 12342 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995041 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12342 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12343 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12343. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12343 : WorldParameters where
  hiddenCharge := (1188368297 / 1000000000000 : ℝ)
  frame := (126142951357 / 200000000000 : ℝ)
  moment := (5081253133 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12343 : AgentParameters :=
  { agentLedgerParameters with
    charge := (456191371 / 250000000000 : ℝ)
    frame := (145523580313 / 100000000000 : ℝ)
    root := (4381749067 / 500000000000 : ℝ) }

noncomputable def scalar12343 : ScalarCertificate 12343 world12343 agent12343 where
  dimensionLo := 12343
  dimensionHi := 12343
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2090385199 / 1000000000000 : ℝ)
  frameLo := (126142951357 / 200000000000 : ℝ)
  frameHi := (145523580313 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12343]
  agentFrame_pos := by norm_num only [agent12343]
  worldRadius := (2090385199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12343]
  retainedCharge := (456191371 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1855782257 / 1000000000000 : ℝ)
  lowerTail := (1065116071 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4662409833 / 500000000000 : ℝ)
  ledger := by
    have h : (1188368297 / 1000000000000 : ℚ) +
        (5081253133 / 500000000000000000 : ℚ) / (2090385199 / 1000000000000 : ℚ) ^ 2 +
        (456191371 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1855782257 / 1000000000000 : ℚ) + (1065116071 / 500000000000 : ℚ) ≤
        (4662409833 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1188368297 / 1000000000000 : ℚ) +
        (5081253133 / 500000000000000000 : ℚ) / (2090385199 / 1000000000000 : ℚ) ^ 2 +
        (456191371 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1855782257 / 1000000000000 : ℚ) + (1065116071 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4662409833 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12343]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12343 :
    2 * 160 < 12343 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999059 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12343 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12344 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12344. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12344 : WorldParameters where
  hiddenCharge := (1188320307 / 1000000000000 : ℝ)
  frame := (315350041973 / 500000000000 : ℝ)
  moment := (2032070481 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12344 : AgentParameters :=
  { agentLedgerParameters with
    charge := (91203951 / 50000000000 : ℝ)
    frame := (1455195788123 / 1000000000000 : ℝ)
    root := (876277981 / 100000000000 : ℝ) }

noncomputable def scalar12344 : ScalarCertificate 12344 world12344 agent12344 where
  dimensionLo := 12344
  dimensionHi := 12344
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2090741899 / 1000000000000 : ℝ)
  frameLo := (315350041973 / 500000000000 : ℝ)
  frameHi := (1455195788123 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12344]
  agentFrame_pos := by norm_num only [agent12344]
  worldRadius := (2090741899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12344]
  retainedCharge := (91203951 / 50000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1854150869 / 1000000000000 : ℝ)
  lowerTail := (2128482409 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9319417859 / 1000000000000 : ℝ)
  ledger := by
    have h : (1188320307 / 1000000000000 : ℚ) +
        (2032070481 / 200000000000000000 : ℚ) / (2090741899 / 1000000000000 : ℚ) ^ 2 +
        (91203951 / 50000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1854150869 / 1000000000000 : ℚ) + (2128482409 / 1000000000000 : ℚ) ≤
        (9319417859 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1188320307 / 1000000000000 : ℚ) +
        (2032070481 / 200000000000000000 : ℚ) / (2090741899 / 1000000000000 : ℚ) ^ 2 +
        (91203951 / 50000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1854150869 / 1000000000000 : ℚ) + (2128482409 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9319417859 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12344]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12344 :
    2 * 160 < 12344 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (68749999 / 6250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12344 {← IO.monoMsNow}" : IO Unit)
