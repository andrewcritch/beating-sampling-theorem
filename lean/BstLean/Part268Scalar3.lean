import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12425 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12425. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12425 : WorldParameters where
  hiddenCharge := (1184476141 / 1000000000000 : ℝ)
  frame := (629519620311 / 1000000000000 : ℝ)
  moment := (9987986403 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12425 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487683276057 / 1000000000000 : ℝ)
    root := (4345137431 / 500000000000 : ℝ) }

noncomputable def scalar12425 : ScalarCertificate 12425 world12425 agent12425 where
  dimensionLo := 12425
  dimensionHi := 12425
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2076794999 / 1000000000000 : ℝ)
  frameLo := (629519620311 / 1000000000000 : ℝ)
  frameHi := (1487683276057 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12425]
  agentFrame_pos := by norm_num only [agent12425]
  worldRadius := (2076794999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12425]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (927891323 / 500000000000 : ℝ)
  lowerTail := (2157548721 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9312698229 / 1000000000000 : ℝ)
  ledger := by
    have h : (1184476141 / 1000000000000 : ℚ) +
        (9987986403 / 1000000000000000000 : ℚ) / (2076794999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (927891323 / 500000000000 : ℚ) + (2157548721 / 1000000000000 : ℚ) ≤
        (9312698229 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1184476141 / 1000000000000 : ℚ) +
        (9987986403 / 1000000000000000000 : ℚ) / (2076794999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (927891323 / 500000000000 : ℚ) + (2157548721 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9312698229 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12425]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12425 :
    2 * 160 < 12425 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997563 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12425 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12426 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12426. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12426 : WorldParameters where
  hiddenCharge := (1184429209 / 1000000000000 : ℝ)
  frame := (314752572589 / 500000000000 : ℝ)
  moment := (2496471011 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12426 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (743823838799 / 500000000000 : ℝ)
    root := (8689538821 / 1000000000000 : ℝ) }

noncomputable def scalar12426 : ScalarCertificate 12426 world12426 agent12426 where
  dimensionLo := 12426
  dimensionHi := 12426
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2077145799 / 1000000000000 : ℝ)
  frameLo := (314752572589 / 500000000000 : ℝ)
  frameHi := (743823838799 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12426]
  agentFrame_pos := by norm_num only [agent12426]
  worldRadius := (2077145799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12426]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (927081607 / 500000000000 : ℝ)
  lowerTail := (538949747 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2327003183 / 250000000000 : ℝ)
  ledger := by
    have h : (1184429209 / 1000000000000 : ℚ) +
        (2496471011 / 250000000000000000 : ℚ) / (2077145799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (927081607 / 500000000000 : ℚ) + (538949747 / 250000000000 : ℚ) ≤
        (2327003183 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1184429209 / 1000000000000 : ℚ) +
        (2496471011 / 250000000000000000 : ℚ) / (2077145799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (927081607 / 500000000000 : ℚ) + (538949747 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2327003183 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12426]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12426 :
    2 * 160 < 12426 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997739 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12426 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12427 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12427. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12427 : WorldParameters where
  hiddenCharge := (1184382289 / 1000000000000 : ℝ)
  frame := (62949067243 / 100000000000 : ℝ)
  moment := (9983782303 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12427 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46487878199 / 31250000000 : ℝ)
    root := (8688803019 / 1000000000000 : ℝ) }

noncomputable def scalar12427 : ScalarCertificate 12427 world12427 agent12427 where
  dimensionLo := 12427
  dimensionHi := 12427
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2077496699 / 1000000000000 : ℝ)
  frameLo := (62949067243 / 100000000000 : ℝ)
  frameHi := (46487878199 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12427]
  agentFrame_pos := by norm_num only [agent12427]
  worldRadius := (2077496699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12427]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (926272773 / 500000000000 : ℝ)
  lowerTail := (1077025531 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1162916433 / 125000000000 : ℝ)
  ledger := by
    have h : (1184382289 / 1000000000000 : ℚ) +
        (9983782303 / 1000000000000000000 : ℚ) / (2077496699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (926272773 / 500000000000 : ℚ) + (1077025531 / 500000000000 : ℚ) ≤
        (1162916433 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1184382289 / 1000000000000 : ℚ) +
        (9983782303 / 1000000000000000000 : ℚ) / (2077496699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (926272773 / 500000000000 : ℚ) + (1077025531 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1162916433 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12427]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12427 :
    2 * 160 < 12427 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999651 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12427 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12428 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12428. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12428 : WorldParameters where
  hiddenCharge := (1184335381 / 1000000000000 : ℝ)
  frame := (314738101033 / 500000000000 : ℝ)
  moment := (499084059 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12428 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487576550353 / 1000000000000 : ℝ)
    root := (1086008423 / 125000000000 : ℝ) }

noncomputable def scalar12428 : ScalarCertificate 12428 world12428 agent12428 where
  dimensionLo := 12428
  dimensionHi := 12428
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2077847499 / 1000000000000 : ℝ)
  frameLo := (314738101033 / 500000000000 : ℝ)
  frameHi := (1487576550353 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12428]
  agentFrame_pos := by norm_num only [agent12428]
  worldRadius := (2077847499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12428]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1850929349 / 1000000000000 : ℝ)
  lowerTail := (538076159 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9298654271 / 1000000000000 : ℝ)
  ledger := by
    have h : (1184335381 / 1000000000000 : ℚ) +
        (499084059 / 50000000000000000 : ℚ) / (2077847499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1850929349 / 1000000000000 : ℚ) + (538076159 / 250000000000 : ℚ) ≤
        (9298654271 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1184335381 / 1000000000000 : ℚ) +
        (499084059 / 50000000000000000 : ℚ) / (2077847499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1850929349 / 1000000000000 : ℚ) + (538076159 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9298654271 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12428]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12428 :
    2 * 160 < 12428 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998847 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12428 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12429 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12429. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12429 : WorldParameters where
  hiddenCharge := (1184288487 / 1000000000000 : ℝ)
  frame := (314730867043 / 500000000000 : ℝ)
  moment := (399183227 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12429 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (74377051077 / 50000000000 : ℝ)
    root := (8687332057 / 1000000000000 : ℝ) }

noncomputable def scalar12429 : ScalarCertificate 12429 world12429 agent12429 where
  dimensionLo := 12429
  dimensionHi := 12429
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2078198299 / 1000000000000 : ℝ)
  frameLo := (314730867043 / 500000000000 : ℝ)
  frameHi := (74377051077 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12429]
  agentFrame_pos := by norm_num only [agent12429]
  worldRadius := (2078198299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12429]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (5779109 / 3125000000 : ℝ)
  lowerTail := (2150559971 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4646990723 / 500000000000 : ℝ)
  ledger := by
    have h : (1184288487 / 1000000000000 : ℚ) +
        (399183227 / 40000000000000000 : ℚ) / (2078198299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (5779109 / 3125000000 : ℚ) + (2150559971 / 1000000000000 : ℚ) ≤
        (4646990723 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1184288487 / 1000000000000 : ℚ) +
        (399183227 / 40000000000000000 : ℚ) / (2078198299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (5779109 / 3125000000 : ℚ) + (2150559971 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4646990723 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12429]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12429 :
    2 * 160 < 12429 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999749 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12429 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12430 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12430. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12430 : WorldParameters where
  hiddenCharge := (236848321 / 200000000000 : ℝ)
  frame := (78680908561 / 125000000000 : ℝ)
  moment := (9977480787 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12430 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148742089163 / 100000000000 : ℝ)
    root := (8686596967 / 1000000000000 : ℝ) }

noncomputable def scalar12430 : ScalarCertificate 12430 world12430 agent12430 where
  dimensionLo := 12430
  dimensionHi := 12430
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2078657599 / 1000000000000 : ℝ)
  frameLo := (78680908561 / 125000000000 : ℝ)
  frameHi := (148742089163 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12430]
  agentFrame_pos := by norm_num only [agent12430]
  worldRadius := (2078657599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12430]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (92368117 / 50000000000 : ℝ)
  lowerTail := (2148387347 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2322075597 / 250000000000 : ℝ)
  ledger := by
    have h : (236848321 / 200000000000 : ℚ) +
        (9977480787 / 1000000000000000000 : ℚ) / (2078657599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (92368117 / 50000000000 : ℚ) + (2148387347 / 1000000000000 : ℚ) ≤
        (2322075597 / 250000000000 : ℚ) := by norm_num only
    have hc : (((236848321 / 200000000000 : ℚ) +
        (9977480787 / 1000000000000000000 : ℚ) / (2078657599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (92368117 / 50000000000 : ℚ) + (2148387347 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2322075597 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12430]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12430 :
    2 * 160 < 12430 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996483 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12430 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12431 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12431. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12431 : WorldParameters where
  hiddenCharge := (74012171 / 62500000000 : ℝ)
  frame := (629432805273 / 1000000000000 : ℝ)
  moment := (9975381517 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12431 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (743692702119 / 500000000000 : ℝ)
    root := (1737172423 / 200000000000 : ℝ) }

noncomputable def scalar12431 : ScalarCertificate 12431 world12431 agent12431 where
  dimensionLo := 12431
  dimensionHi := 12431
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2079008599 / 1000000000000 : ℝ)
  frameLo := (629432805273 / 1000000000000 : ℝ)
  frameHi := (743692702119 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12431]
  agentFrame_pos := by norm_num only [agent12431]
  worldRadius := (2079008599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12431]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (230718949 / 125000000000 : ℝ)
  lowerTail := (2146646527 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1160454827 / 125000000000 : ℝ)
  ledger := by
    have h : (74012171 / 62500000000 : ℚ) +
        (9975381517 / 1000000000000000000 : ℚ) / (2079008599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (230718949 / 125000000000 : ℚ) + (2146646527 / 1000000000000 : ℚ) ≤
        (1160454827 / 125000000000 : ℚ) := by norm_num only
    have hc : (((74012171 / 62500000000 : ℚ) +
        (9975381517 / 1000000000000000000 : ℚ) / (2079008599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (230718949 / 125000000000 : ℚ) + (2146646527 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1160454827 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12431]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12431 :
    2 * 160 < 12431 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999613 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12431 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12432 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12432. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12432 : WorldParameters where
  hiddenCharge := (1184147879 / 1000000000000 : ℝ)
  frame := (15735458611 / 25000000000 : ℝ)
  moment := (9973282863 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12432 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (59493997361 / 40000000000 : ℝ)
    root := (2171281857 / 250000000000 : ℝ) }

noncomputable def scalar12432 : ScalarCertificate 12432 world12432 agent12432 where
  dimensionLo := 12432
  dimensionHi := 12432
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2079359399 / 1000000000000 : ℝ)
  frameLo := (15735458611 / 25000000000 : ℝ)
  frameHi := (59493997361 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12432]
  agentFrame_pos := by norm_num only [agent12432]
  worldRadius := (2079359399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12432]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (184414217 / 100000000000 : ℝ)
  lowerTail := (536226761 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2319744707 / 250000000000 : ℝ)
  ledger := by
    have h : (1184147879 / 1000000000000 : ℚ) +
        (9973282863 / 1000000000000000000 : ℚ) / (2079359399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (184414217 / 100000000000 : ℚ) + (536226761 / 250000000000 : ℚ) ≤
        (2319744707 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1184147879 / 1000000000000 : ℚ) +
        (9973282863 / 1000000000000000000 : ℚ) / (2079359399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (184414217 / 100000000000 : ℚ) + (536226761 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2319744707 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12432]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12432 :
    2 * 160 < 12432 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999947 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12432 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12433 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12433. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12433 : WorldParameters where
  hiddenCharge := (296025259 / 250000000000 : ℝ)
  frame := (629403885987 / 1000000000000 : ℝ)
  moment := (9971184827 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12433 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487314492939 / 1000000000000 : ℝ)
    root := (173687861 / 20000000000 : ℝ) }

noncomputable def scalar12433 : ScalarCertificate 12433 world12433 agent12433 where
  dimensionLo := 12433
  dimensionHi := 12433
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2079710299 / 1000000000000 : ℝ)
  frameLo := (629403885987 / 1000000000000 : ℝ)
  frameHi := (1487314492939 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12433]
  agentFrame_pos := by norm_num only [agent12433]
  worldRadius := (2079710299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12433]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (921267303 / 500000000000 : ℝ)
  lowerTail := (2143169469 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4637161731 / 500000000000 : ℝ)
  ledger := by
    have h : (296025259 / 250000000000 : ℚ) +
        (9971184827 / 1000000000000000000 : ℚ) / (2079710299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (921267303 / 500000000000 : ℚ) + (2143169469 / 1000000000000 : ℚ) ≤
        (4637161731 / 500000000000 : ℚ) := by norm_num only
    have hc : (((296025259 / 250000000000 : ℚ) +
        (9971184827 / 1000000000000000000 : ℚ) / (2079710299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (921267303 / 500000000000 : ℚ) + (2143169469 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4637161731 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12433]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12433 :
    2 * 160 < 12433 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995801 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12433 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12434 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12434. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12434 : WorldParameters where
  hiddenCharge := (296013551 / 250000000000 : ℝ)
  frame := (125877885983 / 200000000000 : ℝ)
  moment := (9969087407 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12434 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (743639534503 / 500000000000 : ℝ)
    root := (2170914727 / 250000000000 : ℝ) }

noncomputable def scalar12434 : ScalarCertificate 12434 world12434 agent12434 where
  dimensionLo := 12434
  dimensionHi := 12434
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2080061099 / 1000000000000 : ℝ)
  frameLo := (125877885983 / 200000000000 : ℝ)
  frameHi := (743639534503 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12434]
  agentFrame_pos := by norm_num only [agent12434]
  worldRadius := (2080061099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12434]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (368185709 / 200000000000 : ℝ)
  lowerTail := (1070716709 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9269672219 / 1000000000000 : ℝ)
  ledger := by
    have h : (296013551 / 250000000000 : ℚ) +
        (9969087407 / 1000000000000000000 : ℚ) / (2080061099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (368185709 / 200000000000 : ℚ) + (1070716709 / 500000000000 : ℚ) ≤
        (9269672219 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((296013551 / 250000000000 : ℚ) +
        (9969087407 / 1000000000000000000 : ℚ) / (2080061099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (368185709 / 200000000000 : ℚ) + (1070716709 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9269672219 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12434]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12434 :
    2 * 160 < 12434 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998943 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12434 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12435 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12435. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12435 : WorldParameters where
  hiddenCharge := (592003693 / 500000000000 : ℝ)
  frame := (629374976223 / 1000000000000 : ℝ)
  moment := (2491747651 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12435 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (371810915553 / 250000000000 : ℝ)
    root := (8682925003 / 1000000000000 : ℝ) }

noncomputable def scalar12435 : ScalarCertificate 12435 world12435 agent12435 where
  dimensionLo := 12435
  dimensionHi := 12435
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2080411999 / 1000000000000 : ℝ)
  frameLo := (629374976223 / 1000000000000 : ℝ)
  frameHi := (371810915553 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12435]
  agentFrame_pos := by norm_num only [agent12435]
  worldRadius := (2080411999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12435]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (919662099 / 500000000000 : ℝ)
  lowerTail := (1069849559 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9265025097 / 1000000000000 : ℝ)
  ledger := by
    have h : (592003693 / 500000000000 : ℚ) +
        (2491747651 / 250000000000000000 : ℚ) / (2080411999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (919662099 / 500000000000 : ℚ) + (1069849559 / 500000000000 : ℚ) ≤
        (9265025097 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((592003693 / 500000000000 : ℚ) +
        (2491747651 / 250000000000000000 : ℚ) / (2080411999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (919662099 / 500000000000 : ℚ) + (1069849559 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9265025097 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12435]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12435 :
    2 * 160 < 12435 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999839 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12435 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12436 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12436. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12436 : WorldParameters where
  hiddenCharge := (59198029 / 50000000000 : ℝ)
  frame := (629360524909 / 1000000000000 : ℝ)
  moment := (9964894417 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12436 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185901035563 / 125000000000 : ℝ)
    root := (8682191263 / 1000000000000 : ℝ) }

noncomputable def scalar12436 : ScalarCertificate 12436 world12436 agent12436 where
  dimensionLo := 12436
  dimensionHi := 12436
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2080762899 / 1000000000000 : ℝ)
  frameLo := (629360524909 / 1000000000000 : ℝ)
  frameHi := (185901035563 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12436]
  agentFrame_pos := by norm_num only [agent12436]
  worldRadius := (2080762899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12436]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (229715181 / 125000000000 : ℝ)
  lowerTail := (1068983229 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4630191043 / 500000000000 : ℝ)
  ledger := by
    have h : (59198029 / 50000000000 : ℚ) +
        (9964894417 / 1000000000000000000 : ℚ) / (2080762899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (229715181 / 125000000000 : ℚ) + (1068983229 / 500000000000 : ℚ) ≤
        (4630191043 / 500000000000 : ℚ) := by norm_num only
    have hc : (((59198029 / 50000000000 : ℚ) +
        (9964894417 / 1000000000000000000 : ℚ) / (2080762899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (229715181 / 125000000000 : ℚ) + (1068983229 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4630191043 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12436]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12436 :
    2 * 160 < 12436 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997929 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12436 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12437 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12437. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12437 : WorldParameters where
  hiddenCharge := (1183913787 / 1000000000000 : ℝ)
  frame := (25173843039 / 40000000000 : ℝ)
  moment := (1992559769 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12437 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487172923909 / 1000000000000 : ℝ)
    root := (8681457831 / 1000000000000 : ℝ) }

noncomputable def scalar12437 : ScalarCertificate 12437 world12437 agent12437 where
  dimensionLo := 12437
  dimensionHi := 12437
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2081113699 / 1000000000000 : ℝ)
  frameLo := (25173843039 / 40000000000 : ℝ)
  frameHi := (1487172923909 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12437]
  agentFrame_pos := by norm_num only [agent12437]
  worldRadius := (2081113699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12437]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1836120269 / 1000000000000 : ℝ)
  lowerTail := (213623539 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4627871667 / 500000000000 : ℝ)
  ledger := by
    have h : (1183913787 / 1000000000000 : ℚ) +
        (1992559769 / 200000000000000000 : ℚ) / (2081113699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1836120269 / 1000000000000 : ℚ) + (213623539 / 100000000000 : ℚ) ≤
        (4627871667 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1183913787 / 1000000000000 : ℚ) +
        (1992559769 / 200000000000000000 : ℚ) / (2081113699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1836120269 / 1000000000000 : ℚ) + (213623539 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4627871667 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12437]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12437 :
    2 * 160 < 12437 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997961 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12437 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12438 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12438. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12438 : WorldParameters where
  hiddenCharge := (1183867007 / 1000000000000 : ℝ)
  frame := (314665814709 / 500000000000 : ℝ)
  moment := (996070389 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12438 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487137586393 / 1000000000000 : ℝ)
    root := (4340362317 / 500000000000 : ℝ) }

noncomputable def scalar12438 : ScalarCertificate 12438 world12438 agent12438 where
  dimensionLo := 12438
  dimensionHi := 12438
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2081464699 / 1000000000000 : ℝ)
  frameLo := (314665814709 / 500000000000 : ℝ)
  frameHi := (1487137586393 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12438]
  agentFrame_pos := by norm_num only [agent12438]
  worldRadius := (2081464699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12438]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (917260469 / 500000000000 : ℝ)
  lowerTail := (1067253111 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9251108761 / 1000000000000 : ℝ)
  ledger := by
    have h : (1183867007 / 1000000000000 : ℚ) +
        (996070389 / 100000000000000000 : ℚ) / (2081464699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (917260469 / 500000000000 : ℚ) + (1067253111 / 500000000000 : ℚ) ≤
        (9251108761 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1183867007 / 1000000000000 : ℚ) +
        (996070389 / 100000000000000000 : ℚ) / (2081464699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (917260469 / 500000000000 : ℚ) + (1067253111 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9251108761 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12438]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12438 :
    2 * 160 < 12438 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999993943 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12438 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12439 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12439. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12439 : WorldParameters where
  hiddenCharge := (1183820239 / 1000000000000 : ℝ)
  frame := (314658592619 / 500000000000 : ℝ)
  moment := (199172191 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12439 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487102265963 / 1000000000000 : ℝ)
    root := (4339995837 / 500000000000 : ℝ) }

noncomputable def scalar12439 : ScalarCertificate 12439 world12439 agent12439 where
  dimensionLo := 12439
  dimensionHi := 12439
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2081815599 / 1000000000000 : ℝ)
  frameLo := (314658592619 / 500000000000 : ℝ)
  frameHi := (1487102265963 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12439]
  agentFrame_pos := by norm_num only [agent12439]
  worldRadius := (2081815599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12439]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1832923101 / 1000000000000 : ℝ)
  lowerTail := (266597321 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (577904893 / 62500000000 : ℝ)
  ledger := by
    have h : (1183820239 / 1000000000000 : ℚ) +
        (199172191 / 20000000000000000 : ℚ) / (2081815599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1832923101 / 1000000000000 : ℚ) + (266597321 / 125000000000 : ℚ) ≤
        (577904893 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1183820239 / 1000000000000 : ℚ) +
        (199172191 / 20000000000000000 : ℚ) / (2081815599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1832923101 / 1000000000000 : ℚ) + (266597321 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((577904893 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12439]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12439 :
    2 * 160 < 12439 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997981 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12439 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12440 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12440. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12440 : WorldParameters where
  hiddenCharge := (295943371 / 250000000000 : ℝ)
  frame := (125860548687 / 200000000000 : ℝ)
  moment := (398260633 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12440 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486982475551 / 1000000000000 : ℝ)
    root := (4339629439 / 500000000000 : ℝ) }

noncomputable def scalar12440 : ScalarCertificate 12440 world12440 agent12440 where
  dimensionLo := 12440
  dimensionHi := 12440
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2082275099 / 1000000000000 : ℝ)
  frameLo := (125860548687 / 200000000000 : ℝ)
  frameHi := (1486982475551 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12440]
  agentFrame_pos := by norm_num only [agent12440]
  worldRadius := (2082275099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12440]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1830990299 / 1000000000000 : ℝ)
  lowerTail := (2130626637 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (577553119 / 62500000000 : ℝ)
  ledger := by
    have h : (295943371 / 250000000000 : ℚ) +
        (398260633 / 40000000000000000 : ℚ) / (2082275099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1830990299 / 1000000000000 : ℚ) + (2130626637 / 1000000000000 : ℚ) ≤
        (577553119 / 62500000000 : ℚ) := by norm_num only
    have hc : (((295943371 / 250000000000 : ℚ) +
        (398260633 / 40000000000000000 : ℚ) / (2082275099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1830990299 / 1000000000000 : ℚ) + (2130626637 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((577553119 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12440]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12440 :
    2 * 160 < 12440 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995887 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12440 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12441 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12441. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12441 : WorldParameters where
  hiddenCharge := (1183726741 / 1000000000000 : ℝ)
  frame := (629288304009 / 1000000000000 : ℝ)
  moment := (1990884543 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12441 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (743473598133 / 500000000000 : ℝ)
    root := (8678526389 / 1000000000000 : ℝ) }

noncomputable def scalar12441 : ScalarCertificate 12441 world12441 agent12441 where
  dimensionLo := 12441
  dimensionHi := 12441
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2082625999 / 1000000000000 : ℝ)
  frameLo := (629288304009 / 1000000000000 : ℝ)
  frameHi := (743473598133 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12441]
  agentFrame_pos := by norm_num only [agent12441]
  worldRadius := (2082625999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12441]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1829395929 / 1000000000000 : ℝ)
  lowerTail := (532225639 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4618114193 / 500000000000 : ℝ)
  ledger := by
    have h : (1183726741 / 1000000000000 : ℚ) +
        (1990884543 / 200000000000000000 : ℚ) / (2082625999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1829395929 / 1000000000000 : ℚ) + (532225639 / 250000000000 : ℚ) ≤
        (4618114193 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1183726741 / 1000000000000 : ℚ) +
        (1990884543 / 200000000000000000 : ℚ) / (2082625999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1829395929 / 1000000000000 : ℚ) + (532225639 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4618114193 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12441]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12441 :
    2 * 160 < 12441 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999763 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12441 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12442 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12442. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12442 : WorldParameters where
  hiddenCharge := (1183680011 / 1000000000000 : ℝ)
  frame := (629273866957 / 1000000000000 : ℝ)
  moment := (497616511 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12442 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297382389197 / 200000000000 : ℝ)
    root := (1084724267 / 125000000000 : ℝ) }

noncomputable def scalar12442 : ScalarCertificate 12442 world12442 agent12442 where
  dimensionLo := 12442
  dimensionHi := 12442
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2082976899 / 1000000000000 : ℝ)
  frameLo := (629273866957 / 1000000000000 : ℝ)
  frameHi := (297382389197 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12442]
  agentFrame_pos := by norm_num only [agent12442]
  worldRadius := (2082976899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12442]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1827803217 / 1000000000000 : ℝ)
  lowerTail := (132948761 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (92316111 / 10000000000 : ℝ)
  ledger := by
    have h : (1183680011 / 1000000000000 : ℚ) +
        (497616511 / 50000000000000000 : ℚ) / (2082976899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1827803217 / 1000000000000 : ℚ) + (132948761 / 62500000000 : ℚ) ≤
        (92316111 / 10000000000 : ℚ) := by norm_num only
    have hc : (((1183680011 / 1000000000000 : ℚ) +
        (497616511 / 50000000000000000 : ℚ) / (2082976899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1827803217 / 1000000000000 : ℚ) + (132948761 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((92316111 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12442]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12442 :
    2 * 160 < 12442 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997711 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12442 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12443 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12443. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12443 : WorldParameters where
  hiddenCharge := (591816647 / 500000000000 : ℝ)
  frame := (15731485807 / 25000000000 : ℝ)
  moment := (9950238339 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12443 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46464897273 / 31250000000 : ℝ)
    root := (8677062047 / 1000000000000 : ℝ) }

noncomputable def scalar12443 : ScalarCertificate 12443 world12443 agent12443 where
  dimensionLo := 12443
  dimensionHi := 12443
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2083327899 / 1000000000000 : ℝ)
  frameLo := (15731485807 / 25000000000 : ℝ)
  frameHi := (46464897273 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12443]
  agentFrame_pos := by norm_num only [agent12443]
  worldRadius := (2083327899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12443]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (182621213 / 100000000000 : ℝ)
  lowerTail := (2125459459 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (36907991 / 4000000000 : ℝ)
  ledger := by
    have h : (591816647 / 500000000000 : ℚ) +
        (9950238339 / 1000000000000000000 : ℚ) / (2083327899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (182621213 / 100000000000 : ℚ) + (2125459459 / 1000000000000 : ℚ) ≤
        (36907991 / 4000000000 : ℚ) := by norm_num only
    have hc : (((591816647 / 500000000000 : ℚ) +
        (9950238339 / 1000000000000000000 : ℚ) / (2083327899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (182621213 / 100000000000 : ℚ) + (2125459459 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((36907991 / 4000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12443]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12443 :
    2 * 160 < 12443 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999749 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12443 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12444 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12444. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12444 : WorldParameters where
  hiddenCharge := (1183586589 / 1000000000000 : ℝ)
  frame := (314622499989 / 500000000000 : ℝ)
  moment := (9948147073 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12444 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (371710374127 / 250000000000 : ℝ)
    root := (1084541283 / 125000000000 : ℝ) }

noncomputable def scalar12444 : ScalarCertificate 12444 world12444 agent12444 where
  dimensionLo := 12444
  dimensionHi := 12444
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2083678799 / 1000000000000 : ℝ)
  frameLo := (314622499989 / 500000000000 : ℝ)
  frameHi := (371710374127 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12444]
  agentFrame_pos := by norm_num only [agent12444]
  worldRadius := (2083678799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12444]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1824622601 / 1000000000000 : ℝ)
  lowerTail := (2123740321 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9222388627 / 1000000000000 : ℝ)
  ledger := by
    have h : (1183586589 / 1000000000000 : ℚ) +
        (9948147073 / 1000000000000000000 : ℚ) / (2083678799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1824622601 / 1000000000000 : ℚ) + (2123740321 / 1000000000000 : ℚ) ≤
        (9222388627 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1183586589 / 1000000000000 : ℚ) +
        (9948147073 / 1000000000000000000 : ℚ) / (2083678799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1824622601 / 1000000000000 : ℚ) + (2123740321 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9222388627 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12444]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12444 :
    2 * 160 < 12444 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998417 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12444 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12445 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12445. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12445 : WorldParameters where
  hiddenCharge := (1183539897 / 1000000000000 : ℝ)
  frame := (629230570049 / 1000000000000 : ℝ)
  moment := (9946056421 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12445 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297361260653 / 200000000000 : ℝ)
    root := (2168899679 / 250000000000 : ℝ) }

noncomputable def scalar12445 : ScalarCertificate 12445 world12445 agent12445 where
  dimensionLo := 12445
  dimensionHi := 12445
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2084029799 / 1000000000000 : ℝ)
  frameLo := (629230570049 / 1000000000000 : ℝ)
  frameHi := (297361260653 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12445]
  agentFrame_pos := by norm_num only [agent12445]
  worldRadius := (2084029799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12445]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1823034799 / 1000000000000 : ℝ)
  lowerTail := (1061011477 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9217783651 / 1000000000000 : ℝ)
  ledger := by
    have h : (1183539897 / 1000000000000 : ℚ) +
        (9946056421 / 1000000000000000000 : ℚ) / (2084029799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1823034799 / 1000000000000 : ℚ) + (1061011477 / 500000000000 : ℚ) ≤
        (9217783651 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1183539897 / 1000000000000 : ℚ) +
        (9946056421 / 1000000000000000000 : ℚ) / (2084029799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1823034799 / 1000000000000 : ℚ) + (1061011477 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9217783651 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12445]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12445 :
    2 * 160 < 12445 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999633 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12445 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12446 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12446. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12446 : WorldParameters where
  hiddenCharge := (591746609 / 500000000000 : ℝ)
  frame := (629216142493 / 1000000000000 : ℝ)
  moment := (9943966383 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12446 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486771132993 / 1000000000000 : ℝ)
    root := (2168716833 / 250000000000 : ℝ) }

noncomputable def scalar12446 : ScalarCertificate 12446 world12446 agent12446 where
  dimensionLo := 12446
  dimensionHi := 12446
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2084380699 / 1000000000000 : ℝ)
  frameLo := (629216142493 / 1000000000000 : ℝ)
  frameHi := (1486771132993 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12446]
  agentFrame_pos := by norm_num only [agent12446]
  worldRadius := (2084380699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12446]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (455362109 / 250000000000 : ℝ)
  lowerTail := (424061411 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2303295667 / 250000000000 : ℝ)
  ledger := by
    have h : (591746609 / 500000000000 : ℚ) +
        (9943966383 / 1000000000000000000 : ℚ) / (2084380699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (455362109 / 250000000000 : ℚ) + (424061411 / 200000000000 : ℚ) ≤
        (2303295667 / 250000000000 : ℚ) := by norm_num only
    have hc : (((591746609 / 500000000000 : ℚ) +
        (9943966383 / 1000000000000000000 : ℚ) / (2084380699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (455362109 / 250000000000 : ℚ) + (424061411 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2303295667 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12446]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12446 :
    2 * 160 < 12446 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998599 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12446 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12447 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12447. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12447 : WorldParameters where
  hiddenCharge := (1183446551 / 1000000000000 : ℝ)
  frame := (629201717309 / 1000000000000 : ℝ)
  moment := (4970938479 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12447 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486735985679 / 1000000000000 : ℝ)
    root := (4337068127 / 500000000000 : ℝ) }

noncomputable def scalar12447 : ScalarCertificate 12447 world12447 agent12447 where
  dimensionLo := 12447
  dimensionHi := 12447
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2084731599 / 1000000000000 : ℝ)
  frameLo := (629201717309 / 1000000000000 : ℝ)
  frameHi := (1486735985679 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12447]
  agentFrame_pos := by norm_num only [agent12447]
  worldRadius := (2084731599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12447]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1819863763 / 1000000000000 : ℝ)
  lowerTail := (1059296441 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (920858597 / 100000000000 : ℝ)
  ledger := by
    have h : (1183446551 / 1000000000000 : ℚ) +
        (4970938479 / 500000000000000000 : ℚ) / (2084731599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1819863763 / 1000000000000 : ℚ) + (1059296441 / 500000000000 : ℚ) ≤
        (920858597 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1183446551 / 1000000000000 : ℚ) +
        (4970938479 / 500000000000000000 : ℚ) / (2084731599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1819863763 / 1000000000000 : ℚ) + (1059296441 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((920858597 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12447]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12447 :
    2 * 160 < 12447 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999529 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12447 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12448 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12448. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12448 : WorldParameters where
  hiddenCharge := (1183399897 / 1000000000000 : ℝ)
  frame := (629187294497 / 1000000000000 : ℝ)
  moment := (9939788147 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12448 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (371675213833 / 250000000000 : ℝ)
    root := (867340541 / 100000000000 : ℝ) }

noncomputable def scalar12448 : ScalarCertificate 12448 world12448 agent12448 where
  dimensionLo := 12448
  dimensionHi := 12448
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2085082599 / 1000000000000 : ℝ)
  frameLo := (629187294497 / 1000000000000 : ℝ)
  frameHi := (371675213833 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12448]
  agentFrame_pos := by norm_num only [agent12448]
  worldRadius := (2085082599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12448]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (90914039 / 50000000000 : ℝ)
  lowerTail := (529220109 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1840798667 / 200000000000 : ℝ)
  ledger := by
    have h : (1183399897 / 1000000000000 : ℚ) +
        (9939788147 / 1000000000000000000 : ℚ) / (2085082599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (90914039 / 50000000000 : ℚ) + (529220109 / 250000000000 : ℚ) ≤
        (1840798667 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1183399897 / 1000000000000 : ℚ) +
        (9939788147 / 1000000000000000000 : ℚ) / (2085082599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (90914039 / 50000000000 : ℚ) + (529220109 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1840798667 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12448]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12448 :
    2 * 160 < 12448 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995763 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12448 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12449 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12449. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12449 : WorldParameters where
  hiddenCharge := (147919157 / 125000000000 : ℝ)
  frame := (78646609257 / 125000000000 : ℝ)
  moment := (9937699949 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12449 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486665741941 / 1000000000000 : ℝ)
    root := (867267473 / 100000000000 : ℝ) }

noncomputable def scalar12449 : ScalarCertificate 12449 world12449 agent12449 where
  dimensionLo := 12449
  dimensionHi := 12449
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2085433599 / 1000000000000 : ℝ)
  frameLo := (78646609257 / 125000000000 : ℝ)
  frameHi := (1486665741941 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12449]
  agentFrame_pos := by norm_num only [agent12449]
  worldRadius := (2085433599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12449]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (227087413 / 125000000000 : ℝ)
  lowerTail := (2115169527 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (919940461 / 100000000000 : ℝ)
  ledger := by
    have h : (147919157 / 125000000000 : ℚ) +
        (9937699949 / 1000000000000000000 : ℚ) / (2085433599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (227087413 / 125000000000 : ℚ) + (2115169527 / 1000000000000 : ℚ) ≤
        (919940461 / 100000000000 : ℚ) := by norm_num only
    have hc : (((147919157 / 125000000000 : ℚ) +
        (9937699949 / 1000000000000000000 : ℚ) / (2085433599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (227087413 / 125000000000 : ℚ) + (2115169527 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((919940461 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12449]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12449 :
    2 * 160 < 12449 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999999 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12449 {← IO.monoMsNow}" : IO Unit)
