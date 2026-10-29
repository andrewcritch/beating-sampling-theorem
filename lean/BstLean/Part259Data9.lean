import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12270 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12270. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12270 : WorldParameters where
  hiddenCharge := (1191907239 / 1000000000000 : ℝ)
  frame := (631792500081 / 1000000000000 : ℝ)
  moment := (80636541 / 7812500000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12270 : AgentParameters :=
  { agentLedgerParameters with
    charge := (469144537 / 250000000000 : ℝ)
    frame := (1458190437779 / 1000000000000 : ℝ)
    root := (4408268373 / 500000000000 : ℝ) }

noncomputable def scalar12270 : ScalarCertificate 12270 world12270 agent12270 where
  dimensionLo := 12270
  dimensionHi := 12270
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2064407399 / 1000000000000 : ℝ)
  frameLo := (631792500081 / 1000000000000 : ℝ)
  frameHi := (1458190437779 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12270]
  agentFrame_pos := by norm_num only [agent12270]
  worldRadius := (2064407399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12270]
  retainedCharge := (469144537 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1979374457 / 1000000000000 : ℝ)
  lowerTail := (2262507277 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2433059833 / 250000000000 : ℝ)
  ledger := by
    have h : (1191907239 / 1000000000000 : ℚ) +
        (80636541 / 7812500000000000 : ℚ) / (2064407399 / 1000000000000 : ℚ) ^ 2 +
        (469144537 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1979374457 / 1000000000000 : ℚ) + (2262507277 / 1000000000000 : ℚ) ≤
        (2433059833 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1191907239 / 1000000000000 : ℚ) +
        (80636541 / 7812500000000000 : ℚ) / (2064407399 / 1000000000000 : ℚ) ^ 2 +
        (469144537 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1979374457 / 1000000000000 : ℚ) + (2262507277 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2433059833 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12270]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12270 :
    2 * 160 < 12270 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199998943 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12270 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12271 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12271. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12271 : WorldParameters where
  hiddenCharge := (1191858281 / 1000000000000 : ℝ)
  frame := (631777647587 / 1000000000000 : ℝ)
  moment := (1289909521 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12271 : AgentParameters :=
  { agentLedgerParameters with
    charge := (937922579 / 500000000000 : ℝ)
    frame := (729074858093 / 500000000000 : ℝ)
    root := (4407901019 / 500000000000 : ℝ) }

noncomputable def scalar12271 : ScalarCertificate 12271 world12271 agent12271 where
  dimensionLo := 12271
  dimensionHi := 12271
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2064762199 / 1000000000000 : ℝ)
  frameLo := (631777647587 / 1000000000000 : ℝ)
  frameHi := (729074858093 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12271]
  agentFrame_pos := by norm_num only [agent12271]
  worldRadius := (2064762199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12271]
  retainedCharge := (937922579 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1977620651 / 1000000000000 : ℝ)
  lowerTail := (2260634231 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9726481981 / 1000000000000 : ℝ)
  ledger := by
    have h : (1191858281 / 1000000000000 : ℚ) +
        (1289909521 / 125000000000000000 : ℚ) / (2064762199 / 1000000000000 : ℚ) ^ 2 +
        (937922579 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1977620651 / 1000000000000 : ℚ) + (2260634231 / 1000000000000 : ℚ) ≤
        (9726481981 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1191858281 / 1000000000000 : ℚ) +
        (1289909521 / 125000000000000000 : ℚ) / (2064762199 / 1000000000000 : ℚ) ^ 2 +
        (937922579 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1977620651 / 1000000000000 : ℚ) + (2260634231 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9726481981 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12271]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12271 :
    2 * 160 < 12271 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (1374999387 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12271 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12272 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12272. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12272 : WorldParameters where
  hiddenCharge := (148976167 / 125000000000 : ℝ)
  frame := (631762797577 / 1000000000000 : ℝ)
  moment := (10317075743 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12272 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1875112827 / 1000000000000 : ℝ)
    frame := (1458109009381 / 1000000000000 : ℝ)
    root := (8815067561 / 1000000000000 : ℝ) }

noncomputable def scalar12272 : ScalarCertificate 12272 world12272 agent12272 where
  dimensionLo := 12272
  dimensionHi := 12272
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2065117099 / 1000000000000 : ℝ)
  frameLo := (631762797577 / 1000000000000 : ℝ)
  frameHi := (1458109009381 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12272]
  agentFrame_pos := by norm_num only [agent12272]
  worldRadius := (2065117099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12272]
  retainedCharge := (1875112827 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1975868703 / 1000000000000 : ℝ)
  lowerTail := (282345383 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1944145949 / 200000000000 : ℝ)
  ledger := by
    have h : (148976167 / 125000000000 : ℚ) +
        (10317075743 / 1000000000000000000 : ℚ) / (2065117099 / 1000000000000 : ℚ) ^ 2 +
        (1875112827 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1975868703 / 1000000000000 : ℚ) + (282345383 / 125000000000 : ℚ) ≤
        (1944145949 / 200000000000 : ℚ) := by norm_num only
    have hc : (((148976167 / 125000000000 : ℚ) +
        (10317075743 / 1000000000000000000 : ℚ) / (2065117099 / 1000000000000 : ℚ) ^ 2 +
        (1875112827 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1975868703 / 1000000000000 : ℚ) + (282345383 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1944145949 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12272]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12272 :
    2 * 160 < 12272 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499999761 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12272 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12273 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12273. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12273 : WorldParameters where
  hiddenCharge := (238352081 / 200000000000 : ℝ)
  frame := (631747950051 / 1000000000000 : ℝ)
  moment := (5157437987 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12273 : AgentParameters :=
  { agentLedgerParameters with
    charge := (937190579 / 500000000000 : ℝ)
    frame := (1458068211627 / 1000000000000 : ℝ)
    root := (1762866663 / 200000000000 : ℝ) }

noncomputable def scalar12273 : ScalarCertificate 12273 world12273 agent12273 where
  dimensionLo := 12273
  dimensionHi := 12273
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2065471999 / 1000000000000 : ℝ)
  frameLo := (631747950051 / 1000000000000 : ℝ)
  frameHi := (1458068211627 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12273]
  agentFrame_pos := by norm_num only [agent12273]
  worldRadius := (2065471999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12273]
  retainedCharge := (937190579 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1974117887 / 1000000000000 : ℝ)
  lowerTail := (2256892921 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2428745319 / 250000000000 : ℝ)
  ledger := by
    have h : (238352081 / 200000000000 : ℚ) +
        (5157437987 / 500000000000000000 : ℚ) / (2065471999 / 1000000000000 : ℚ) ^ 2 +
        (937190579 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1974117887 / 1000000000000 : ℚ) + (2256892921 / 1000000000000 : ℚ) ≤
        (2428745319 / 250000000000 : ℚ) := by norm_num only
    have hc : (((238352081 / 200000000000 : ℚ) +
        (5157437987 / 500000000000000000 : ℚ) / (2065471999 / 1000000000000 : ℚ) ^ 2 +
        (937190579 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1974117887 / 1000000000000 : ℚ) + (2256892921 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2428745319 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12273]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12273 :
    2 * 160 < 12273 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (1374999733 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12273 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12274 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12274. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12274 : WorldParameters where
  hiddenCharge := (1191711487 / 1000000000000 : ℝ)
  frame := (39483319063 / 62500000000 : ℝ)
  moment := (515633843 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12274 : AgentParameters :=
  { agentLedgerParameters with
    charge := (936825073 / 500000000000 : ℝ)
    frame := (364506802833 / 250000000000 : ℝ)
    root := (8813599299 / 1000000000000 : ℝ) }

noncomputable def scalar12274 : ScalarCertificate 12274 world12274 agent12274 where
  dimensionLo := 12274
  dimensionHi := 12274
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2065827399 / 1000000000000 : ℝ)
  frameLo := (39483319063 / 62500000000 : ℝ)
  frameHi := (364506802833 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12274]
  agentFrame_pos := by norm_num only [agent12274]
  worldRadius := (2065827399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12274]
  retainedCharge := (936825073 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1972368129 / 1000000000000 : ℝ)
  lowerTail := (1127511817 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (242730879 / 25000000000 : ℝ)
  ledger := by
    have h : (1191711487 / 1000000000000 : ℚ) +
        (515633843 / 50000000000000000 : ℚ) / (2065827399 / 1000000000000 : ℚ) ^ 2 +
        (936825073 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1972368129 / 1000000000000 : ℚ) + (1127511817 / 500000000000 : ℚ) ≤
        (242730879 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1191711487 / 1000000000000 : ℚ) +
        (515633843 / 50000000000000000 : ℚ) / (2065827399 / 1000000000000 : ℚ) ^ 2 +
        (936825073 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1972368129 / 1000000000000 : ℚ) + (1127511817 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((242730879 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12274]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12274 :
    2 * 160 < 12274 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998359 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12274 {← IO.monoMsNow}" : IO Unit)
