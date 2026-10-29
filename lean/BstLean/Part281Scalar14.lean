import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12209 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12209. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12209 : WorldParameters where
  hiddenCharge := (119491927 / 100000000000 : ℝ)
  frame := (79087903409 / 125000000000 : ℝ)
  moment := (10456993229 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12209 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748765604059 / 500000000000 : ℝ)
    root := (7458760251 / 1000000000000 : ℝ) }

noncomputable def scalar12209 : ScalarCertificate 12209 world12209 agent12209 where
  dimensionLo := 12209
  dimensionHi := 12209
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2353308599 / 1000000000000 : ℝ)
  frameLo := (79087903409 / 125000000000 : ℝ)
  frameHi := (748765604059 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12209]
  agentFrame_pos := by norm_num only [agent12209]
  worldRadius := (2353308599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12209]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (249527657 / 200000000000 : ℝ)
  lowerTail := (794313431 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (964816883 / 125000000000 : ℝ)
  ledger := by
    have h : (119491927 / 100000000000 : ℚ) +
        (10456993229 / 1000000000000000000 : ℚ) / (2353308599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (249527657 / 200000000000 : ℚ) + (794313431 / 500000000000 : ℚ) ≤
        (964816883 / 125000000000 : ℚ) := by norm_num only
    have hc : (((119491927 / 100000000000 : ℚ) +
        (10456993229 / 1000000000000000000 : ℚ) / (2353308599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (249527657 / 200000000000 : ℚ) + (794313431 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((964816883 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12209]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12209 :
    2 * 160 < 12209 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999723 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12209 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12210 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12210. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12210 : WorldParameters where
  hiddenCharge := (298717371 / 250000000000 : ℝ)
  frame := (158172055487 / 250000000000 : ℝ)
  moment := (10454751669 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12210 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1497483553287 / 1000000000000 : ℝ)
    root := (7458100943 / 1000000000000 : ℝ) }

noncomputable def scalar12210 : ScalarCertificate 12210 world12210 agent12210 where
  dimensionLo := 12210
  dimensionHi := 12210
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2353712799 / 1000000000000 : ℝ)
  frameLo := (158172055487 / 250000000000 : ℝ)
  frameHi := (1497483553287 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12210]
  agentFrame_pos := by norm_num only [agent12210]
  worldRadius := (2353712799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12210]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1246528813 / 1000000000000 : ℝ)
  lowerTail := (1587317543 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (241094169 / 31250000000 : ℝ)
  ledger := by
    have h : (298717371 / 250000000000 : ℚ) +
        (10454751669 / 1000000000000000000 : ℚ) / (2353712799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1246528813 / 1000000000000 : ℚ) + (1587317543 / 1000000000000 : ℚ) ≤
        (241094169 / 31250000000 : ℚ) := by norm_num only
    have hc : (((298717371 / 250000000000 : ℚ) +
        (10454751669 / 1000000000000000000 : ℚ) / (2353712799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1246528813 / 1000000000000 : ℚ) + (1587317543 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((241094169 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12210]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12210 :
    2 * 160 < 12210 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999291 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12210 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12211 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12211. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12211 : WorldParameters where
  hiddenCharge := (1194819711 / 1000000000000 : ℝ)
  frame := (12653464383 / 20000000000 : ℝ)
  moment := (10452510779 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12211 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1497435920341 / 1000000000000 : ℝ)
    root := (1864360479 / 250000000000 : ℝ) }

noncomputable def scalar12211 : ScalarCertificate 12211 world12211 agent12211 where
  dimensionLo := 12211
  dimensionHi := 12211
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2354116799 / 1000000000000 : ℝ)
  frameLo := (12653464383 / 20000000000 : ℝ)
  frameHi := (1497435920341 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12211]
  agentFrame_pos := by norm_num only [agent12211]
  worldRadius := (2354116799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12211]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1245420381 / 1000000000000 : ℝ)
  lowerTail := (198251171 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7711495003 / 1000000000000 : ℝ)
  ledger := by
    have h : (1194819711 / 1000000000000 : ℚ) +
        (10452510779 / 1000000000000000000 : ℚ) / (2354116799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1245420381 / 1000000000000 : ℚ) + (198251171 / 125000000000 : ℚ) ≤
        (7711495003 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1194819711 / 1000000000000 : ℚ) +
        (10452510779 / 1000000000000000000 : ℚ) / (2354116799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1245420381 / 1000000000000 : ℚ) + (198251171 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7711495003 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12211]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12211 :
    2 * 160 < 12211 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997713 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12211 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12212 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12212. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12212 : WorldParameters where
  hiddenCharge := (37336561 / 31250000000 : ℝ)
  frame := (632658218877 / 1000000000000 : ℝ)
  moment := (10450270561 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12212 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748694157651 / 500000000000 : ℝ)
    root := (7456783019 / 1000000000000 : ℝ) }

noncomputable def scalar12212 : ScalarCertificate 12212 world12212 agent12212 where
  dimensionLo := 12212
  dimensionHi := 12212
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2354520899 / 1000000000000 : ℝ)
  frameLo := (632658218877 / 1000000000000 : ℝ)
  frameHi := (748694157651 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12212]
  agentFrame_pos := by norm_num only [agent12212]
  worldRadius := (2354520899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12212]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (311078281 / 250000000000 : ℝ)
  lowerTail := (1584702507 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (963497459 / 125000000000 : ℝ)
  ledger := by
    have h : (37336561 / 31250000000 : ℚ) +
        (10450270561 / 1000000000000000000 : ℚ) / (2354520899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (311078281 / 250000000000 : ℚ) + (1584702507 / 1000000000000 : ℚ) ≤
        (963497459 / 125000000000 : ℚ) := by norm_num only
    have hc : (((37336561 / 31250000000 : ℚ) +
        (10450270561 / 1000000000000000000 : ℚ) / (2354520899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (311078281 / 250000000000 : ℚ) + (1584702507 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((963497459 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12212]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12212 :
    2 * 160 < 12212 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995067 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12212 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12213 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12213. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12213 : WorldParameters where
  hiddenCharge := (597360103 / 500000000000 : ℝ)
  frame := (79080402641 / 125000000000 : ℝ)
  moment := (10448031013 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12213 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1497340732113 / 1000000000000 : ℝ)
    root := (7456124327 / 1000000000000 : ℝ) }

noncomputable def scalar12213 : ScalarCertificate 12213 world12213 agent12213 where
  dimensionLo := 12213
  dimensionHi := 12213
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2354924999 / 1000000000000 : ℝ)
  frameLo := (79080402641 / 125000000000 : ℝ)
  frameHi := (1497340732113 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12213]
  agentFrame_pos := by norm_num only [agent12213]
  worldRadius := (2354924999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12213]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (621603499 / 500000000000 : ℝ)
  lowerTail := (1583396901 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7704467473 / 1000000000000 : ℝ)
  ledger := by
    have h : (597360103 / 500000000000 : ℚ) +
        (10448031013 / 1000000000000000000 : ℚ) / (2354924999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (621603499 / 500000000000 : ℚ) + (1583396901 / 1000000000000 : ℚ) ≤
        (7704467473 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((597360103 / 500000000000 : ℚ) +
        (10448031013 / 1000000000000000000 : ℚ) / (2354924999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (621603499 / 500000000000 : ℚ) + (1583396901 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7704467473 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12213]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12213 :
    2 * 160 < 12213 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999213 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12213 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12214 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12214. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12214 : WorldParameters where
  hiddenCharge := (47786819 / 40000000000 : ℝ)
  frame := (632628225903 / 1000000000000 : ℝ)
  moment := (1305724017 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12214 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (149729318283 / 100000000000 : ℝ)
    root := (7455465839 / 1000000000000 : ℝ) }

noncomputable def scalar12214 : ScalarCertificate 12214 world12214 agent12214 where
  dimensionLo := 12214
  dimensionHi := 12214
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2355329099 / 1000000000000 : ℝ)
  frameLo := (632628225903 / 1000000000000 : ℝ)
  frameHi := (149729318283 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12214]
  agentFrame_pos := by norm_num only [agent12214]
  worldRadius := (2355329099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12214]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (38815689 / 31250000000 : ℝ)
  lowerTail := (158209261 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1925239627 / 250000000000 : ℝ)
  ledger := by
    have h : (47786819 / 40000000000 : ℚ) +
        (1305724017 / 125000000000000000 : ℚ) / (2355329099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (38815689 / 31250000000 : ℚ) + (158209261 / 100000000000 : ℚ) ≤
        (1925239627 / 250000000000 : ℚ) := by norm_num only
    have hc : (((47786819 / 40000000000 : ℚ) +
        (1305724017 / 125000000000000000 : ℚ) / (2355329099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (38815689 / 31250000000 : ℚ) + (158209261 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1925239627 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12214]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12214 :
    2 * 160 < 12214 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997929 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12214 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12215 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12215. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12215 : WorldParameters where
  hiddenCharge := (1194620757 / 1000000000000 : ℝ)
  frame := (1581533083 / 2500000000 : ℝ)
  moment := (10443553929 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12215 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748622827681 / 500000000000 : ℝ)
    root := (7454807557 / 1000000000000 : ℝ) }

noncomputable def scalar12215 : ScalarCertificate 12215 world12215 agent12215 where
  dimensionLo := 12215
  dimensionHi := 12215
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2355733199 / 1000000000000 : ℝ)
  frameLo := (1581533083 / 2500000000 : ℝ)
  frameHi := (748622827681 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12215]
  agentFrame_pos := by norm_num only [agent12215]
  worldRadius := (2355733199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12215]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (620499113 / 500000000000 : ℝ)
  lowerTail := (158078957 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7697452669 / 1000000000000 : ℝ)
  ledger := by
    have h : (1194620757 / 1000000000000 : ℚ) +
        (10443553929 / 1000000000000000000 : ℚ) / (2355733199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (620499113 / 500000000000 : ℚ) + (158078957 / 100000000000 : ℚ) ≤
        (7697452669 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1194620757 / 1000000000000 : ℚ) +
        (10443553929 / 1000000000000000000 : ℚ) / (2355733199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (620499113 / 500000000000 : ℚ) + (158078957 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7697452669 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12215]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12215 :
    2 * 160 < 12215 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998477 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12215 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12216 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12216. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12216 : WorldParameters where
  hiddenCharge := (1194571053 / 1000000000000 : ℝ)
  frame := (31629912151 / 50000000000 : ℝ)
  moment := (1305164549 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12216 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748599077863 / 500000000000 : ℝ)
    root := (3727074777 / 500000000000 : ℝ) }

noncomputable def scalar12216 : ScalarCertificate 12216 world12216 agent12216 where
  dimensionLo := 12216
  dimensionHi := 12216
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2356137199 / 1000000000000 : ℝ)
  frameLo := (31629912151 / 50000000000 : ℝ)
  frameHi := (748599077863 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12216]
  agentFrame_pos := by norm_num only [agent12216]
  worldRadius := (2356137199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12216]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (247979107 / 200000000000 : ℝ)
  lowerTail := (315897557 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7693950117 / 1000000000000 : ℝ)
  ledger := by
    have h : (1194571053 / 1000000000000 : ℚ) +
        (1305164549 / 125000000000000000 : ℚ) / (2356137199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247979107 / 200000000000 : ℚ) + (315897557 / 200000000000 : ℚ) ≤
        (7693950117 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1194571053 / 1000000000000 : ℚ) +
        (1305164549 / 125000000000000000 : ℚ) / (2356137199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247979107 / 200000000000 : ℚ) + (315897557 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7693950117 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12216]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12216 :
    2 * 160 < 12216 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999297 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12216 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12217 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12217. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12217 : WorldParameters where
  hiddenCharge := (597260681 / 500000000000 : ℝ)
  frame := (632583255361 / 1000000000000 : ℝ)
  moment := (417563181 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12217 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748575341953 / 500000000000 : ℝ)
    root := (46584323 / 6250000000 : ℝ) }

noncomputable def scalar12217 : ScalarCertificate 12217 world12217 agent12217 where
  dimensionLo := 12217
  dimensionHi := 12217
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2356541399 / 1000000000000 : ℝ)
  frameLo := (632583255361 / 1000000000000 : ℝ)
  frameHi := (748575341953 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12217]
  agentFrame_pos := by norm_num only [agent12217]
  worldRadius := (2356541399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12217]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (247758817 / 200000000000 : ℝ)
  lowerTail := (12329589 / 7812500000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3845225311 / 500000000000 : ℝ)
  ledger := by
    have h : (597260681 / 500000000000 : ℚ) +
        (417563181 / 40000000000000000 : ℚ) / (2356541399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247758817 / 200000000000 : ℚ) + (12329589 / 7812500000 : ℚ) ≤
        (3845225311 / 500000000000 : ℚ) := by norm_num only
    have hc : (((597260681 / 500000000000 : ℚ) +
        (417563181 / 40000000000000000 : ℚ) / (2356541399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247758817 / 200000000000 : ℚ) + (12329589 / 7812500000 : ℚ) : ℚ) : ℝ) ≤
        ((3845225311 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12217]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12217 :
    2 * 160 < 12217 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994421 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12217 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12218 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12218. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12218 : WorldParameters where
  hiddenCharge := (238894337 / 200000000000 : ℝ)
  frame := (39535516889 / 62500000000 : ℝ)
  moment := (10436843327 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12218 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (299420646769 / 200000000000 : ℝ)
    root := (745283401 / 100000000000 : ℝ) }

noncomputable def scalar12218 : ScalarCertificate 12218 world12218 agent12218 where
  dimensionLo := 12218
  dimensionHi := 12218
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2356945399 / 1000000000000 : ℝ)
  frameLo := (39535516889 / 62500000000 : ℝ)
  frameHi := (299420646769 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12218]
  agentFrame_pos := by norm_num only [agent12218]
  worldRadius := (2356945399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12218]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (309423403 / 250000000000 : ℝ)
  lowerTail := (63075523 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3843477121 / 500000000000 : ℝ)
  ledger := by
    have h : (238894337 / 200000000000 : ℚ) +
        (10436843327 / 1000000000000000000 : ℚ) / (2356945399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (309423403 / 250000000000 : ℚ) + (63075523 / 40000000000 : ℚ) ≤
        (3843477121 / 500000000000 : ℚ) := by norm_num only
    have hc : (((238894337 / 200000000000 : ℚ) +
        (10436843327 / 1000000000000000000 : ℚ) / (2356945399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (309423403 / 250000000000 : ℚ) + (63075523 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3843477121 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12218]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12218 :
    2 * 160 < 12218 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998367 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12218 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12219 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12219. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12219 : WorldParameters where
  hiddenCharge := (597211011 / 500000000000 : ℝ)
  frame := (316276643803 / 500000000000 : ℝ)
  moment := (10434607799 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12219 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1497055811563 / 1000000000000 : ℝ)
    root := (1490435309 / 200000000000 : ℝ) }

noncomputable def scalar12219 : ScalarCertificate 12219 world12219 agent12219 where
  dimensionLo := 12219
  dimensionHi := 12219
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2357349499 / 1000000000000 : ℝ)
  frameLo := (316276643803 / 500000000000 : ℝ)
  frameHi := (1497055811563 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12219]
  agentFrame_pos := by norm_num only [agent12219]
  worldRadius := (2357349499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12219]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1236594359 / 1000000000000 : ℝ)
  lowerTail := (1575590121 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3841730513 / 500000000000 : ℝ)
  ledger := by
    have h : (597211011 / 500000000000 : ℚ) +
        (10434607799 / 1000000000000000000 : ℚ) / (2357349499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1236594359 / 1000000000000 : ℚ) + (1575590121 / 1000000000000 : ℚ) ≤
        (3841730513 / 500000000000 : ℚ) := by norm_num only
    have hc : (((597211011 / 500000000000 : ℚ) +
        (10434607799 / 1000000000000000000 : ℚ) / (2357349499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1236594359 / 1000000000000 : ℚ) + (1575590121 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3841730513 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12219]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12219 :
    2 * 160 < 12219 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997399 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12219 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12220 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12220. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12220 : WorldParameters where
  hiddenCharge := (1194372373 / 1000000000000 : ℝ)
  frame := (158134576877 / 250000000000 : ℝ)
  moment := (10432372939 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12220 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748504208521 / 500000000000 : ℝ)
    root := (1862879821 / 250000000000 : ℝ) }

noncomputable def scalar12220 : ScalarCertificate 12220 world12220 agent12220 where
  dimensionLo := 12220
  dimensionHi := 12220
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2357753599 / 1000000000000 : ℝ)
  frameLo := (158134576877 / 250000000000 : ℝ)
  frameHi := (748504208521 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12220]
  agentFrame_pos := by norm_num only [agent12220]
  worldRadius := (2357753599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12220]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (988397 / 800000000 : ℝ)
  lowerTail := (1574293443 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7679970971 / 1000000000000 : ℝ)
  ledger := by
    have h : (1194372373 / 1000000000000 : ℚ) +
        (10432372939 / 1000000000000000000 : ℚ) / (2357753599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (988397 / 800000000 : ℚ) + (1574293443 / 1000000000000 : ℚ) ≤
        (7679970971 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1194372373 / 1000000000000 : ℚ) +
        (10432372939 / 1000000000000000000 : ℚ) / (2357753599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (988397 / 800000000 : ℚ) + (1574293443 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7679970971 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12220]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12220 :
    2 * 160 < 12220 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999639 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12220 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12221 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12221. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12221 : WorldParameters where
  hiddenCharge := (1194322737 / 1000000000000 : ℝ)
  frame := (79065416241 / 125000000000 : ℝ)
  moment := (2607534687 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12221 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1496961044227 / 1000000000000 : ℝ)
    root := (7450862301 / 1000000000000 : ℝ) }

noncomputable def scalar12221 : ScalarCertificate 12221 world12221 agent12221 where
  dimensionLo := 12221
  dimensionHi := 12221
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2358157699 / 1000000000000 : ℝ)
  frameLo := (79065416241 / 125000000000 : ℝ)
  frameHi := (1496961044227 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12221]
  agentFrame_pos := by norm_num only [agent12221]
  worldRadius := (2358157699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12221]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (308599829 / 250000000000 : ℝ)
  lowerTail := (786499033 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1919121033 / 250000000000 : ℝ)
  ledger := by
    have h : (1194322737 / 1000000000000 : ℚ) +
        (2607534687 / 250000000000000000 : ℚ) / (2358157699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (308599829 / 250000000000 : ℚ) + (786499033 / 500000000000 : ℚ) ≤
        (1919121033 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1194322737 / 1000000000000 : ℚ) +
        (2607534687 / 250000000000000000 : ℚ) / (2358157699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (308599829 / 250000000000 : ℚ) + (786499033 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1919121033 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12221]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12221 :
    2 * 160 < 12221 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999683 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12221 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12222 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12222. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12222 : WorldParameters where
  hiddenCharge := (238854623 / 200000000000 : ℝ)
  frame := (632508354867 / 1000000000000 : ℝ)
  moment := (5213952613 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12222 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (374228426293 / 250000000000 : ℝ)
    root := (931275681 / 125000000000 : ℝ) }

noncomputable def scalar12222 : ScalarCertificate 12222 world12222 agent12222 where
  dimensionLo := 12222
  dimensionHi := 12222
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2358561799 / 1000000000000 : ℝ)
  frameLo := (632508354867 / 1000000000000 : ℝ)
  frameHi := (374228426293 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12222]
  agentFrame_pos := by norm_num only [agent12222]
  worldRadius := (2358561799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12222]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (308325873 / 250000000000 : ℝ)
  lowerTail := (1571703933 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7673000387 / 1000000000000 : ℝ)
  ledger := by
    have h : (238854623 / 200000000000 : ℚ) +
        (5213952613 / 500000000000000000 : ℚ) / (2358561799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (308325873 / 250000000000 : ℚ) + (1571703933 / 1000000000000 : ℚ) ≤
        (7673000387 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((238854623 / 200000000000 : ℚ) +
        (5213952613 / 500000000000000000 : ℚ) / (2358561799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (308325873 / 250000000000 : ℚ) + (1571703933 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7673000387 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12222]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12222 :
    2 * 160 < 12222 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997621 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12222 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12223 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12223. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12223 : WorldParameters where
  hiddenCharge := (1194223507 / 1000000000000 : ℝ)
  frame := (632493382323 / 1000000000000 : ℝ)
  moment := (2606418093 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12223 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1496866387787 / 1000000000000 : ℝ)
    root := (3724774399 / 500000000000 : ℝ) }

noncomputable def scalar12223 : ScalarCertificate 12223 world12223 agent12223 where
  dimensionLo := 12223
  dimensionHi := 12223
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2358965799 / 1000000000000 : ℝ)
  frameLo := (632493382323 / 1000000000000 : ℝ)
  frameHi := (1496866387787 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12223]
  agentFrame_pos := by norm_num only [agent12223]
  worldRadius := (2358965799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12223]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (154026089 / 125000000000 : ℝ)
  lowerTail := (314082191 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (383475987 / 50000000000 : ℝ)
  ledger := by
    have h : (1194223507 / 1000000000000 : ℚ) +
        (2606418093 / 250000000000000000 : ℚ) / (2358965799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (154026089 / 125000000000 : ℚ) + (314082191 / 200000000000 : ℚ) ≤
        (383475987 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1194223507 / 1000000000000 : ℚ) +
        (2606418093 / 250000000000000000 : ℚ) / (2358965799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (154026089 / 125000000000 : ℚ) + (314082191 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((383475987 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12223]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12223 :
    2 * 160 < 12223 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995051 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12223 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12209 :
    (597459634810589768117 / 500000000000000000000000 : ℝ) ≤ world12209.hiddenCharge ∧
    (79087903408916449612889 / 125000000000000000000000 : ℝ) ≤ world12209.frame ∧
    (10456993228912329 / 1000000000000000000000000 : ℝ) ≤ world12209.moment ∧
    (748765604058806652953223 / 500000000000000000000000 : ℝ) ≤ agent12209.frame ∧
    (59670082001669458241 / 8000000000000000000000 : ℝ) ≤ agent12209.root ∧
    scalar12209.worldRadius ≤ (2353308599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (628138480883662139349 / 500000000000000000000000 : ℝ) ≤ agent12209.charge ∧
    (1247638284926060937231 / 1000000000000000000000000 : ℝ) ≤ scalar12209.upperTail ∧
    (1588626861932938618251 / 1000000000000000000000000 : ℝ) ≤ scalar12209.lowerTail ∧
    scalar12209.totalBudget ≤ (3859267532491307115461 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12209, agent12209, scalar12209] <;> simp only [true_and]

theorem source_rounding12210 :
    (5974347415583055899 / 5000000000000000000000 : ℝ) ≤ world12210.hiddenCharge ∧
    (126537644389550563291323 / 200000000000000000000000 : ℝ) ≤ world12210.frame ∧
    (418190066727123 / 40000000000000000000000 : ℝ) ≤ world12210.moment ∧
    (1497483553286458479503229 / 1000000000000000000000000 : ℝ) ≤ agent12210.frame ∧
    (7458100942735799033443 / 1000000000000000000000000 : ℝ) ≤ agent12210.root ∧
    scalar12210.worldRadius ≤ (2353712799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1255982466379560084623 / 1000000000000000000000000 : ℝ) ≤ agent12210.charge ∧
    (124652881236518624659 / 100000000000000000000000 : ℝ) ≤ scalar12210.upperTail ∧
    (1587317542710826088739 / 1000000000000000000000000 : ℝ) ≤ scalar12210.lowerTail ∧
    scalar12210.totalBudget ≤ (482188338044416931843 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12210, agent12210, scalar12210] <;> simp only [true_and]

theorem source_rounding12211 :
    (597409855170143677449 / 500000000000000000000000 : ℝ) ≤ world12211.hiddenCharge ∧
    (316336609574876209203391 / 500000000000000000000000 : ℝ) ≤ world12211.frame ∧
    (1306563847340651 / 125000000000000000000000 : ℝ) ≤ world12211.moment ∧
    (1497435920340962953044083 / 1000000000000000000000000 : ℝ) ≤ agent12211.frame ∧
    (7457441915828159456189 / 1000000000000000000000000 : ℝ) ≤ agent12211.root ∧
    scalar12211.worldRadius ≤ (2354116799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1255688328631635163793 / 1000000000000000000000000 : ℝ) ≤ agent12211.charge ∧
    (622710190379153719001 / 500000000000000000000000 : ℝ) ≤ scalar12211.upperTail ∧
    (63440374693489218601 / 40000000000000000000000 : ℝ) ≤ scalar12211.lowerTail ∧
    scalar12211.totalBudget ≤ (3855747501536616854153 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12211, agent12211, scalar12211] <;> simp only [true_and]

theorem source_rounding12212 :
    (119476995128725540797 / 100000000000000000000000 : ℝ) ≤ world12212.hiddenCharge ∧
    (79082277359581589112167 / 125000000000000000000000 : ℝ) ≤ world12212.frame ∧
    (5225135280147889 / 500000000000000000000000 : ℝ) ≤ world12212.moment ∧
    (748694157650783352082383 / 500000000000000000000000 : ℝ) ≤ agent12212.frame ∧
    (1864195754654309156189 / 250000000000000000000000 : ℝ) ≤ agent12212.root ∧
    scalar12212.worldRadius ≤ (2354520899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (25107890960054784129 / 20000000000000000000000 : ℝ) ≤ agent12212.charge ∧
    (1244313123586023586487 / 1000000000000000000000000 : ℝ) ≤ scalar12212.upperTail ∧
    (396175626603143101263 / 250000000000000000000000 : ℝ) ≤ scalar12212.lowerTail ∧
    scalar12212.totalBudget ≤ (7707979672944699205357 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12212, agent12212, scalar12212] <;> simp only [true_and]

theorem source_rounding12213 :
    (29868005148814091763 / 25000000000000000000000 : ℝ) ≤ world12213.hiddenCharge ∧
    (632643221127776279890787 / 1000000000000000000000000 : ℝ) ≤ world12213.frame ∧
    (2612007753157977 / 250000000000000000000000 : ℝ) ≤ world12213.moment ∧
    (74867036605602289268753 / 50000000000000000000000 : ℝ) ≤ agent12213.frame ∧
    (1864031081587264889783 / 250000000000000000000000 : ℝ) ≤ agent12213.root ∧
    scalar12213.worldRadius ≤ (2354924999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (627550561986469579669 / 500000000000000000000000 : ℝ) ≤ agent12213.charge ∧
    (248641399488696766091 / 200000000000000000000000 : ℝ) ≤ scalar12213.upperTail ∧
    (197924612561765584649 / 125000000000000000000000 : ℝ) ≤ scalar12213.lowerTail ∧
    scalar12213.totalBudget ≤ (385223373684678516109 / 50000000000000000000000 : ℝ) := by
  norm_num only [world12213, agent12213, scalar12213] <;> simp only [true_and]

theorem source_rounding12214 :
    (1194670474331264057097 / 1000000000000000000000000 : ℝ) ≤ world12214.hiddenCharge ∧
    (316314112951222945678949 / 500000000000000000000000 : ℝ) ≤ world12214.frame ∧
    (5222896067737949 / 500000000000000000000000 : ℝ) ≤ world12214.moment ∧
    (748646591414938854405793 / 500000000000000000000000 : ℝ) ≤ agent12214.frame ∧
    (7455465838893094421241 / 1000000000000000000000000 : ℝ) ≤ agent12214.root ∧
    scalar12214.worldRadius ≤ (2355329099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (250961611204635514443 / 200000000000000000000000 : ℝ) ≤ agent12214.charge ∧
    (310525511791582085137 / 250000000000000000000000 : ℝ) ≤ scalar12214.upperTail ∧
    (12656740872869629981 / 8000000000000000000000 : ℝ) ≤ scalar12214.lowerTail ∧
    scalar12214.totalBudget ≤ (1925239627136143299019 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12214, agent12214, scalar12214] <;> simp only [true_and]

theorem source_rounding12215 :
    (1194620756418410763333 / 1000000000000000000000000 : ℝ) ≤ world12215.hiddenCharge ∧
    (126522646639996926190107 / 200000000000000000000000 : ℝ) ≤ world12215.frame ∧
    (10443553928570171 / 1000000000000000000000000 : ℝ) ≤ world12215.moment ∧
    (1497245655361350699078299 / 1000000000000000000000000 : ℝ) ≤ agent12215.frame ∧
    (46592547225743359861 / 6250000000000000000000 : ℝ) ≤ agent12215.root ∧
    scalar12215.worldRadius ≤ (2355733199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1254515343635270947777 / 1000000000000000000000000 : ℝ) ≤ agent12215.charge ∧
    (1240998225170212606341 / 1000000000000000000000000 : ℝ) ≤ scalar12215.upperTail ∧
    (316157913962753129487 / 200000000000000000000000 : ℝ) ≤ scalar12215.lowerTail ∧
    scalar12215.totalBudget ≤ (3848726334667285620981 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12215, agent12215, scalar12215] <;> simp only [true_and]

theorem source_rounding12216 :
    (238914210441811534167 / 200000000000000000000000 : ℝ) ≤ world12216.hiddenCharge ∧
    (632598243019715870906461 / 1000000000000000000000000 : ℝ) ≤ world12216.frame ∧
    (1044131639165717 / 100000000000000000000000 : ℝ) ≤ world12216.moment ∧
    (149719815572591457043667 / 100000000000000000000000 : ℝ) ≤ agent12216.frame ∧
    (3727074776589652899623 / 500000000000000000000000 : ℝ) ≤ agent12216.root ∧
    scalar12216.worldRadius ≤ (2356137199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1254222986291908094949 / 1000000000000000000000000 : ℝ) ≤ agent12216.charge ∧
    (1549869417857188597 / 1250000000000000000000 : ℝ) ≤ scalar12216.upperTail ∧
    (1579487784196733317019 / 1000000000000000000000000 : ℝ) ≤ scalar12216.lowerTail ∧
    scalar12216.totalBudget ≤ (1923487529250542338851 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12216, agent12216, scalar12216] <;> simp only [true_and]

theorem source_rounding12217 :
    (597260680849132416657 / 500000000000000000000000 : ℝ) ≤ world12217.hiddenCharge ∧
    (632583255360963030058183 / 1000000000000000000000000 : ℝ) ≤ world12217.frame ∧
    (10439079524479617 / 1000000000000000000000000 : ℝ) ≤ world12217.moment ∧
    (299430136781047784619603 / 200000000000000000000000 : ℝ) ≤ agent12217.frame ∧
    (7453491679362457372461 / 1000000000000000000000000 : ℝ) ≤ agent12217.root ∧
    scalar12217.worldRadius ≤ (2356541399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (156741372934581060697 / 125000000000000000000000 : ℝ) ≤ agent12217.charge ∧
    (619397042171724700189 / 500000000000000000000000 : ℝ) ≤ scalar12217.upperTail ∧
    (1578187391742961437797 / 1000000000000000000000000 : ℝ) ≤ scalar12217.lowerTail ∧
    scalar12217.totalBudget ≤ (7690450622763877742479 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12217, agent12217, scalar12217] <;> simp only [true_and]

theorem source_rounding12218 :
    (1194471684881090692107 / 1000000000000000000000000 : ℝ) ≤ world12218.hiddenCharge ∧
    (158142067555762529828591 / 250000000000000000000000 : ℝ) ≤ world12218.frame ∧
    (2609210831695051 / 250000000000000000000000 : ℝ) ≤ world12218.moment ∧
    (374275808461140163663773 / 250000000000000000000000 : ℝ) ≤ agent12218.frame ∧
    (7452834009836991177457 / 1000000000000000000000000 : ℝ) ≤ agent12218.root ∧
    scalar12218.worldRadius ≤ (2356945399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (156704916834240076809 / 125000000000000000000000 : ℝ) ≤ agent12218.charge ∧
    (154711701465294866507 / 125000000000000000000000 : ℝ) ≤ scalar12218.upperTail ∧
    (1576888074872937367389 / 1000000000000000000000000 : ℝ) ≤ scalar12218.lowerTail ∧
    scalar12218.totalBudget ≤ (384347712133815925401 / 50000000000000000000000 : ℝ) := by
  norm_num only [world12218, agent12218, scalar12218] <;> simp only [true_and]

theorem source_rounding12219 :
    (298605505438149639801 / 250000000000000000000000 : ℝ) ≤ world12219.hiddenCharge ∧
    (632553287605300979050701 / 1000000000000000000000000 : ℝ) ≤ world12219.frame ∧
    (10434607798301847 / 1000000000000000000000000 : ℝ) ≤ world12219.moment ∧
    (74852790578129410219349 / 50000000000000000000000 : ℝ) ≤ agent12219.frame ∧
    (7452176544473022720913 / 1000000000000000000000000 : ℝ) ≤ agent12219.root ∧
    scalar12219.worldRadius ≤ (2357349499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (626674019684510181423 / 500000000000000000000000 : ℝ) ≤ agent12219.charge ∧
    (1236594358421461799607 / 1000000000000000000000000 : ℝ) ≤ scalar12219.upperTail ∧
    (31511802416619684437 / 20000000000000000000000 : ℝ) ≤ scalar12219.lowerTail ∧
    scalar12219.totalBudget ≤ (1920865256558824643237 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12219, agent12219, scalar12219] <;> simp only [true_and]

theorem source_rounding12220 :
    (298593093076963181627 / 250000000000000000000000 : ℝ) ≤ world12220.hiddenCharge ∧
    (632538307507040044248717 / 1000000000000000000000000 : ℝ) ≤ world12220.frame ∧
    (5216186469393769 / 500000000000000000000000 : ℝ) ≤ world12220.moment ∧
    (299401683408211738554983 / 200000000000000000000000 : ℝ) ≤ agent12220.frame ∧
    (7451519283140796877267 / 1000000000000000000000000 : ℝ) ≤ agent12220.root ∧
    scalar12220.worldRadius ≤ (2357753599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1253057097048109365077 / 1000000000000000000000000 : ℝ) ≤ agent12220.charge ∧
    (308874062403961056721 / 250000000000000000000000 : ℝ) ≤ scalar12220.upperTail ∧
    (78714672102647673331 / 50000000000000000000000 : ℝ) ≤ scalar12220.lowerTail ∧
    scalar12220.totalBudget ≤ (7679970971461926052437 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12220, agent12220, scalar12220] <;> simp only [true_and]

theorem source_rounding12221 :
    (597161368270959880677 / 500000000000000000000000 : ℝ) ≤ world12221.hiddenCharge ∧
    (25300933197103673202201 / 40000000000000000000000 : ℝ) ≤ world12221.frame ∧
    (2607534686995097 / 250000000000000000000000 : ℝ) ≤ world12221.moment ∧
    (299392208845216629321793 / 200000000000000000000000 : ℝ) ≤ agent12221.frame ∧
    (29104930862952172153 / 3906250000000000000000 : ℝ) ≤ agent12221.root ∧
    scalar12221.worldRadius ≤ (2358157699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (250553301439642675771 / 200000000000000000000000 : ℝ) ≤ agent12221.charge ∧
    (1234399315311496066367 / 1000000000000000000000000 : ℝ) ≤ scalar12221.upperTail ∧
    (19662475815143875459 / 12500000000000000000000 : ℝ) ≤ scalar12221.lowerTail ∧
    scalar12221.totalBudget ≤ (15352968265814884819 / 2000000000000000000000 : ℝ) := by
  norm_num only [world12221, agent12221, scalar12221] <;> simp only [true_and]

theorem source_rounding12222 :
    (597136557224934252579 / 500000000000000000000000 : ℝ) ≤ world12222.hiddenCharge ∧
    (79063544358285139144237 / 125000000000000000000000 : ℝ) ≤ world12222.frame ∧
    (2085581045124727 / 200000000000000000000000 : ℝ) ≤ world12222.moment ∧
    (187114213146376232655731 / 125000000000000000000000 : ℝ) ≤ agent12222.frame ∧
    (7450205447242675834537 / 1000000000000000000000000 : ℝ) ≤ agent12222.root ∧
    scalar12222.worldRadius ≤ (2358561799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1252476269307220658647 / 1000000000000000000000000 : ℝ) ≤ agent12222.charge ∧
    (154162936415576198967 / 125000000000000000000000 : ℝ) ≤ scalar12222.upperTail ∧
    (1571703932531929464201 / 1000000000000000000000000 : ℝ) ≤ scalar12222.lowerTail ∧
    scalar12222.totalBudget ≤ (1534600077497473652553 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12222, agent12222, scalar12222] <;> simp only [true_and]

theorem source_rounding12223 :
    (597111753013385682303 / 500000000000000000000000 : ℝ) ≤ world12223.hiddenCharge ∧
    (632493382322432955818681 / 1000000000000000000000000 : ℝ) ≤ world12223.frame ∧
    (1042567237146069 / 100000000000000000000000 : ℝ) ≤ world12223.moment ∧
    (1496866387786614558461033 / 1000000000000000000000000 : ℝ) ≤ agent12223.frame ∧
    (297981951888514105991 / 40000000000000000000000 : ℝ) ≤ agent12223.root ∧
    scalar12223.worldRadius ≤ (2358965799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (250437276572776066503 / 200000000000000000000000 : ℝ) ≤ agent12223.charge ∧
    (77013044479100052619 / 62500000000000000000000 : ℝ) ≤ scalar12223.upperTail ∧
    (785205477354362022971 / 500000000000000000000000 : ℝ) ≤ scalar12223.lowerTail ∧
    scalar12223.totalBudget ≤ (3834759870312767305733 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12223, agent12223, scalar12223] <;> simp only [true_and]

noncomputable def paperAgent12209 : AgentParameters :=
  { agent12209 with charge := (251255393 / 200000000000 : ℝ) }

theorem agent_is_repriced12209 : agent12209 =
    BstLean.Part265.agentRepriced 12209 world12209 paperAgent12209 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12209, agent12209]

noncomputable def paperAgent12210 : AgentParameters :=
  { agent12210 with charge := (1255982469 / 1000000000000 : ℝ) }

theorem agent_is_repriced12210 : agent12210 =
    BstLean.Part265.agentRepriced 12210 world12210 paperAgent12210 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12210, agent12210]

noncomputable def paperAgent12211 : AgentParameters :=
  { agent12211 with charge := (313922083 / 250000000000 : ℝ) }

theorem agent_is_repriced12211 : agent12211 =
    BstLean.Part265.agentRepriced 12211 world12211 paperAgent12211 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12211, agent12211]

noncomputable def paperAgent12212 : AgentParameters :=
  { agent12212 with charge := (1255394551 / 1000000000000 : ℝ) }

theorem agent_is_repriced12212 : agent12212 =
    BstLean.Part265.agentRepriced 12212 world12212 paperAgent12212 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12212, agent12212]

noncomputable def paperAgent12213 : AgentParameters :=
  { agent12213 with charge := (1255101127 / 1000000000000 : ℝ) }

theorem agent_is_repriced12213 : agent12213 =
    BstLean.Part265.agentRepriced 12213 world12213 paperAgent12213 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12213, agent12213]

noncomputable def paperAgent12214 : AgentParameters :=
  { agent12214 with charge := (62740403 / 50000000000 : ℝ) }

theorem agent_is_repriced12214 : agent12214 =
    BstLean.Part265.agentRepriced 12214 world12214 paperAgent12214 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12214, agent12214]

noncomputable def paperAgent12215 : AgentParameters :=
  { agent12215 with charge := (1254515347 / 1000000000000 : ℝ) }

theorem agent_is_repriced12215 : agent12215 =
    BstLean.Part265.agentRepriced 12215 world12215 paperAgent12215 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12215, agent12215]

noncomputable def paperAgent12216 : AgentParameters :=
  { agent12216 with charge := (125422299 / 100000000000 : ℝ) }

theorem agent_is_repriced12216 : agent12216 =
    BstLean.Part265.agentRepriced 12216 world12216 paperAgent12216 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12216, agent12216]

noncomputable def paperAgent12217 : AgentParameters :=
  { agent12217 with charge := (1253930987 / 1000000000000 : ℝ) }

theorem agent_is_repriced12217 : agent12217 =
    BstLean.Part265.agentRepriced 12217 world12217 paperAgent12217 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12217, agent12217]

noncomputable def paperAgent12218 : AgentParameters :=
  { agent12218 with charge := (626819669 / 500000000000 : ℝ) }

theorem agent_is_repriced12218 : agent12218 =
    BstLean.Part265.agentRepriced 12218 world12218 paperAgent12218 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12218, agent12218]

noncomputable def paperAgent12219 : AgentParameters :=
  { agent12219 with charge := (1253348043 / 1000000000000 : ℝ) }

theorem agent_is_repriced12219 : agent12219 =
    BstLean.Part265.agentRepriced 12219 world12219 paperAgent12219 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12219, agent12219]

noncomputable def paperAgent12220 : AgentParameters :=
  { agent12220 with charge := (12530571 / 10000000000 : ℝ) }

theorem agent_is_repriced12220 : agent12220 =
    BstLean.Part265.agentRepriced 12220 world12220 paperAgent12220 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12220, agent12220]

noncomputable def paperAgent12221 : AgentParameters :=
  { agent12221 with charge := (125276651 / 100000000000 : ℝ) }

theorem agent_is_repriced12221 : agent12221 =
    BstLean.Part265.agentRepriced 12221 world12221 paperAgent12221 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12221, agent12221]

noncomputable def paperAgent12222 : AgentParameters :=
  { agent12222 with charge := (1252476273 / 1000000000000 : ℝ) }

theorem agent_is_repriced12222 : agent12222 =
    BstLean.Part265.agentRepriced 12222 world12222 paperAgent12222 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12222, agent12222]

noncomputable def paperAgent12223 : AgentParameters :=
  { agent12223 with charge := (626093193 / 500000000000 : ℝ) }

theorem agent_is_repriced12223 : agent12223 =
    BstLean.Part265.agentRepriced 12223 world12223 paperAgent12223 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12223, agent12223]

end BstLean.Part281
