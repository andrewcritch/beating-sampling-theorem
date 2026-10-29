import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12059 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12059. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12059 : WorldParameters where
  hiddenCharge := (120254561 / 100000000000 : ℝ)
  frame := (19843219449 / 31250000000 : ℝ)
  moment := (10800980323 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12059 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504909152093 / 1000000000000 : ℝ)
    root := (1890012349 / 250000000000 : ℝ) }

noncomputable def scalar12059 : ScalarCertificate 12059 world12059 agent12059 where
  dimensionLo := 12059
  dimensionHi := 12059
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2292839999 / 1000000000000 : ℝ)
  frameLo := (19843219449 / 31250000000 : ℝ)
  frameHi := (1504909152093 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12059]
  agentFrame_pos := by norm_num only [agent12059]
  worldRadius := (2292839999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12059]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (17846441 / 12500000000 : ℝ)
  lowerTail := (1800114091 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8284066059 / 1000000000000 : ℝ)
  ledger := by
    have h : (120254561 / 100000000000 : ℚ) +
        (10800980323 / 1000000000000000000 : ℚ) / (2292839999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (17846441 / 12500000000 : ℚ) + (1800114091 / 1000000000000 : ℚ) ≤
        (8284066059 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((120254561 / 100000000000 : ℚ) +
        (10800980323 / 1000000000000000000 : ℚ) / (2292839999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (17846441 / 12500000000 : ℚ) + (1800114091 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8284066059 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12059]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12059 :
    2 * 160 < 12059 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998811 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12059 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12060 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12060. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12060 : WorldParameters where
  hiddenCharge := (601246853 / 500000000000 : ℝ)
  frame := (158741907597 / 250000000000 : ℝ)
  moment := (10798635077 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12060 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752429156463 / 500000000000 : ℝ)
    root := (1889839457 / 250000000000 : ℝ) }

noncomputable def scalar12060 : ScalarCertificate 12060 world12060 agent12060 where
  dimensionLo := 12060
  dimensionHi := 12060
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2293242299 / 1000000000000 : ℝ)
  frameLo := (158741907597 / 250000000000 : ℝ)
  frameHi := (752429156463 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12060]
  agentFrame_pos := by norm_num only [agent12060]
  worldRadius := (2293242299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12060]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (713209607 / 500000000000 : ℝ)
  lowerTail := (35971977 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8280036109 / 1000000000000 : ℝ)
  ledger := by
    have h : (601246853 / 500000000000 : ℚ) +
        (10798635077 / 1000000000000000000 : ℚ) / (2293242299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (713209607 / 500000000000 : ℚ) + (35971977 / 20000000000 : ℚ) ≤
        (8280036109 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((601246853 / 500000000000 : ℚ) +
        (10798635077 / 1000000000000000000 : ℚ) / (2293242299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (713209607 / 500000000000 : ℚ) + (35971977 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8280036109 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12060]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12060 :
    2 * 160 < 12060 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994583 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12060 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12061 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12061. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12061 : WorldParameters where
  hiddenCharge := (601220909 / 500000000000 : ℝ)
  frame := (317476120519 / 500000000000 : ℝ)
  moment := (10796290543 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12061 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (60192299941 / 40000000000 : ℝ)
    root := (3779333243 / 500000000000 : ℝ) }

noncomputable def scalar12061 : ScalarCertificate 12061 world12061 agent12061 where
  dimensionLo := 12061
  dimensionHi := 12061
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2293644699 / 1000000000000 : ℝ)
  frameLo := (317476120519 / 500000000000 : ℝ)
  frameHi := (60192299941 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12061]
  agentFrame_pos := by norm_num only [agent12061]
  worldRadius := (2293644699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12061]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1425124589 / 1000000000000 : ℝ)
  lowerTail := (4492713 / 2500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8276009853 / 1000000000000 : ℝ)
  ledger := by
    have h : (601220909 / 500000000000 : ℚ) +
        (10796290543 / 1000000000000000000 : ℚ) / (2293644699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1425124589 / 1000000000000 : ℚ) + (4492713 / 2500000000 : ℚ) ≤
        (8276009853 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((601220909 / 500000000000 : ℚ) +
        (10796290543 / 1000000000000000000 : ℚ) / (2293644699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1425124589 / 1000000000000 : ℚ) + (4492713 / 2500000000 : ℚ) : ℚ) : ℝ) ≤
        ((8276009853 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12061]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12061 :
    2 * 160 < 12061 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998929 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12061 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12062 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12062. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12062 : WorldParameters where
  hiddenCharge := (150298743 / 125000000000 : ℝ)
  frame := (634936854317 / 1000000000000 : ℝ)
  moment := (10793946721 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12062 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504756714949 / 1000000000000 : ℝ)
    root := (944746931 / 125000000000 : ℝ) }

noncomputable def scalar12062 : ScalarCertificate 12062 world12062 agent12062 where
  dimensionLo := 12062
  dimensionHi := 12062
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2294046999 / 1000000000000 : ℝ)
  frameLo := (634936854317 / 1000000000000 : ℝ)
  frameHi := (1504756714949 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12062]
  agentFrame_pos := by norm_num only [agent12062]
  worldRadius := (2294046999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12062]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1423831327 / 1000000000000 : ℝ)
  lowerTail := (224446631 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8271987479 / 1000000000000 : ℝ)
  ledger := by
    have h : (150298743 / 125000000000 : ℚ) +
        (10793946721 / 1000000000000000000 : ℚ) / (2294046999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1423831327 / 1000000000000 : ℚ) + (224446631 / 125000000000 : ℚ) ≤
        (8271987479 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((150298743 / 125000000000 : ℚ) +
        (10793946721 / 1000000000000000000 : ℚ) / (2294046999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1423831327 / 1000000000000 : ℚ) + (224446631 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8271987479 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12062]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12062 :
    2 * 160 < 12062 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996283 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12062 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12063 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12063. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12063 : WorldParameters where
  hiddenCharge := (300584521 / 250000000000 : ℝ)
  frame := (25396858809 / 40000000000 : ℝ)
  moment := (10791603609 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12063 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (23511030659 / 15625000000 : ℝ)
    root := (3778642279 / 500000000000 : ℝ) }

noncomputable def scalar12063 : ScalarCertificate 12063 world12063 agent12063 where
  dimensionLo := 12063
  dimensionHi := 12063
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2294449399 / 1000000000000 : ℝ)
  frameLo := (25396858809 / 40000000000 : ℝ)
  frameHi := (23511030659 / 15625000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12063]
  agentFrame_pos := by norm_num only [agent12063]
  worldRadius := (2294449399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12063]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (711269733 / 500000000000 : ℝ)
  lowerTail := (1794062449 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (103349609 / 12500000000 : ℝ)
  ledger := by
    have h : (300584521 / 250000000000 : ℚ) +
        (10791603609 / 1000000000000000000 : ℚ) / (2294449399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (711269733 / 500000000000 : ℚ) + (1794062449 / 1000000000000 : ℚ) ≤
        (103349609 / 12500000000 : ℚ) := by norm_num only
    have hc : (((300584521 / 250000000000 : ℚ) +
        (10791603609 / 1000000000000000000 : ℚ) / (2294449399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (711269733 / 500000000000 : ℚ) + (1794062449 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((103349609 / 12500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12063]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12063 :
    2 * 160 < 12063 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999063 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12063 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12064 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12064. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12064 : WorldParameters where
  hiddenCharge := (1202286239 / 1000000000000 : ℝ)
  frame := (634906088761 / 1000000000000 : ℝ)
  moment := (10789261207 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12064 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (188081905023 / 125000000000 : ℝ)
    root := (3778296947 / 500000000000 : ℝ) }

noncomputable def scalar12064 : ScalarCertificate 12064 world12064 agent12064 where
  dimensionLo := 12064
  dimensionHi := 12064
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2294851699 / 1000000000000 : ℝ)
  frameLo := (634906088761 / 1000000000000 : ℝ)
  frameHi := (188081905023 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12064]
  agentFrame_pos := by norm_num only [agent12064]
  worldRadius := (2294851699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12064]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1421248901 / 1000000000000 : ℝ)
  lowerTail := (1792553277 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4131976851 / 500000000000 : ℝ)
  ledger := by
    have h : (1202286239 / 1000000000000 : ℚ) +
        (10789261207 / 1000000000000000000 : ℚ) / (2294851699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1421248901 / 1000000000000 : ℚ) + (1792553277 / 1000000000000 : ℚ) ≤
        (4131976851 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1202286239 / 1000000000000 : ℚ) +
        (10789261207 / 1000000000000000000 : ℚ) / (2294851699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1421248901 / 1000000000000 : ℚ) + (1792553277 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4131976851 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12064]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12064 :
    2 * 160 < 12064 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999449 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12064 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12065 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12065. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12065 : WorldParameters where
  hiddenCharge := (150279301 / 125000000000 : ℝ)
  frame := (25395628397 / 40000000000 : ℝ)
  moment := (2696729879 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12065 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504604548951 / 1000000000000 : ℝ)
    root := (236121983 / 31250000000 : ℝ) }

noncomputable def scalar12065 : ScalarCertificate 12065 world12065 agent12065 where
  dimensionLo := 12065
  dimensionHi := 12065
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2295254099 / 1000000000000 : ℝ)
  frameLo := (25395628397 / 40000000000 : ℝ)
  frameHi := (1504604548951 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12065]
  agentFrame_pos := by norm_num only [agent12065]
  worldRadius := (2295254099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12065]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1419959797 / 1000000000000 : ℝ)
  lowerTail := (1791045721 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8259942423 / 1000000000000 : ℝ)
  ledger := by
    have h : (150279301 / 125000000000 : ℚ) +
        (2696729879 / 250000000000000000 : ℚ) / (2295254099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1419959797 / 1000000000000 : ℚ) + (1791045721 / 1000000000000 : ℚ) ≤
        (8259942423 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((150279301 / 125000000000 : ℚ) +
        (2696729879 / 250000000000000000 : ℚ) / (2295254099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1419959797 / 1000000000000 : ℚ) + (1791045721 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8259942423 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12065]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12065 :
    2 * 160 < 12065 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (439999771 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12065 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12066 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12066. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12066 : WorldParameters where
  hiddenCharge := (18784103 / 15625000000 : ℝ)
  frame := (317437666857 / 500000000000 : ℝ)
  moment := (2156915707 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12066 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504553882377 / 1000000000000 : ℝ)
    root := (7555213321 / 1000000000000 : ℝ) }

noncomputable def scalar12066 : ScalarCertificate 12066 world12066 agent12066 where
  dimensionLo := 12066
  dimensionHi := 12066
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2295656499 / 1000000000000 : ℝ)
  frameLo := (317437666857 / 500000000000 : ℝ)
  frameHi := (1504553882377 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12066]
  agentFrame_pos := by norm_num only [agent12066]
  worldRadius := (2295656499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12066]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (709336053 / 500000000000 : ℝ)
  lowerTail := (894769859 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8255934949 / 1000000000000 : ℝ)
  ledger := by
    have h : (18784103 / 15625000000 : ℚ) +
        (2156915707 / 200000000000000000 : ℚ) / (2295656499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (709336053 / 500000000000 : ℚ) + (894769859 / 500000000000 : ℚ) ≤
        (8255934949 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((18784103 / 15625000000 : ℚ) +
        (2156915707 / 200000000000000000 : ℚ) / (2295656499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (709336053 / 500000000000 : ℚ) + (894769859 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8255934949 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12066]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12066 :
    2 * 160 < 12066 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998181 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12066 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12067 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12067. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12067 : WorldParameters where
  hiddenCharge := (120213079 / 100000000000 : ℝ)
  frame := (63485996013 / 100000000000 : ℝ)
  moment := (10782238263 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12067 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (376125813149 / 250000000000 : ℝ)
    root := (3777261667 / 500000000000 : ℝ) }

noncomputable def scalar12067 : ScalarCertificate 12067 world12067 agent12067 where
  dimensionLo := 12067
  dimensionHi := 12067
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2296058799 / 1000000000000 : ℝ)
  frameLo := (63485996013 / 100000000000 : ℝ)
  frameHi := (376125813149 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12067]
  agentFrame_pos := by norm_num only [agent12067]
  worldRadius := (2296058799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12067]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1417385669 / 1000000000000 : ℝ)
  lowerTail := (55876097 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8251931131 / 1000000000000 : ℝ)
  ledger := by
    have h : (120213079 / 100000000000 : ℚ) +
        (10782238263 / 1000000000000000000 : ℚ) / (2296058799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1417385669 / 1000000000000 : ℚ) + (55876097 / 31250000000 : ℚ) ≤
        (8251931131 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((120213079 / 100000000000 : ℚ) +
        (10782238263 / 1000000000000000000 : ℚ) / (2296058799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1417385669 / 1000000000000 : ℚ) + (55876097 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((8251931131 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12067]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12067 :
    2 * 160 < 12067 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997729 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12067 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12068 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12068. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12068 : WorldParameters where
  hiddenCharge := (1202079003 / 1000000000000 : ℝ)
  frame := (634844589171 / 1000000000000 : ℝ)
  moment := (10779898701 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12068 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504452647431 / 1000000000000 : ℝ)
    root := (1888458393 / 250000000000 : ℝ) }

noncomputable def scalar12068 : ScalarCertificate 12068 world12068 agent12068 where
  dimensionLo := 12068
  dimensionHi := 12068
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2296461099 / 1000000000000 : ℝ)
  frameLo := (634844589171 / 1000000000000 : ℝ)
  frameHi := (1504452647431 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12068]
  agentFrame_pos := by norm_num only [agent12068]
  worldRadius := (2296461099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12068]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1416100579 / 1000000000000 : ℝ)
  lowerTail := (1786531971 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (412396549 / 50000000000 : ℝ)
  ledger := by
    have h : (1202079003 / 1000000000000 : ℚ) +
        (10779898701 / 1000000000000000000 : ℚ) / (2296461099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1416100579 / 1000000000000 : ℚ) + (1786531971 / 1000000000000 : ℚ) ≤
        (412396549 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1202079003 / 1000000000000 : ℚ) +
        (10779898701 / 1000000000000000000 : ℚ) / (2296461099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1416100579 / 1000000000000 : ℚ) + (1786531971 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((412396549 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12068]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12068 :
    2 * 160 < 12068 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997903 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12068 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12069 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12069. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12069 : WorldParameters where
  hiddenCharge := (120202723 / 100000000000 : ℝ)
  frame := (158707305209 / 250000000000 : ℝ)
  moment := (10777559849 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12069 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504402072937 / 1000000000000 : ℝ)
    root := (1510628807 / 200000000000 : ℝ) }

noncomputable def scalar12069 : ScalarCertificate 12069 world12069 agent12069 where
  dimensionLo := 12069
  dimensionHi := 12069
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2296863499 / 1000000000000 : ℝ)
  frameLo := (158707305209 / 250000000000 : ℝ)
  frameHi := (1504402072937 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12069]
  agentFrame_pos := by norm_num only [agent12069]
  worldRadius := (2296863499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12069]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1414816943 / 1000000000000 : ℝ)
  lowerTail := (1785030447 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8243934549 / 1000000000000 : ℝ)
  ledger := by
    have h : (120202723 / 100000000000 : ℚ) +
        (10777559849 / 1000000000000000000 : ℚ) / (2296863499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1414816943 / 1000000000000 : ℚ) + (1785030447 / 1000000000000 : ℚ) ≤
        (8243934549 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((120202723 / 100000000000 : ℚ) +
        (10777559849 / 1000000000000000000 : ℚ) / (2296863499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1414816943 / 1000000000000 : ℚ) + (1785030447 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8243934549 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12069]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12069 :
    2 * 160 < 12069 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999893 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12069 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12070 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12070. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12070 : WorldParameters where
  hiddenCharge := (75123467 / 62500000000 : ℝ)
  frame := (158703463781 / 250000000000 : ℝ)
  moment := (2155044341 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12070 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (150435153517 / 100000000000 : ℝ)
    root := (1888113681 / 250000000000 : ℝ) }

noncomputable def scalar12070 : ScalarCertificate 12070 world12070 agent12070 where
  dimensionLo := 12070
  dimensionHi := 12070
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2297265799 / 1000000000000 : ℝ)
  frameLo := (158703463781 / 250000000000 : ℝ)
  frameHi := (150435153517 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12070]
  agentFrame_pos := by norm_num only [agent12070]
  worldRadius := (2297265799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12070]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1413534619 / 1000000000000 : ℝ)
  lowerTail := (1783530373 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1647988379 / 200000000000 : ℝ)
  ledger := by
    have h : (75123467 / 62500000000 : ℚ) +
        (2155044341 / 200000000000000000 : ℚ) / (2297265799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1413534619 / 1000000000000 : ℚ) + (1783530373 / 1000000000000 : ℚ) ≤
        (1647988379 / 200000000000 : ℚ) := by norm_num only
    have hc : (((75123467 / 62500000000 : ℚ) +
        (2155044341 / 200000000000000000 : ℚ) / (2297265799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1413534619 / 1000000000000 : ℚ) + (1783530373 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1647988379 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12070]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12070 :
    2 * 160 < 12070 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998629 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12070 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12071 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12071. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12071 : WorldParameters where
  hiddenCharge := (75120233 / 62500000000 : ℝ)
  frame := (158699623009 / 250000000000 : ℝ)
  moment := (1077288427 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12071 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752150510977 / 500000000000 : ℝ)
    root := (1510353143 / 200000000000 : ℝ) }

noncomputable def scalar12071 : ScalarCertificate 12071 world12071 agent12071 where
  dimensionLo := 12071
  dimensionHi := 12071
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2297668199 / 1000000000000 : ℝ)
  frameLo := (158699623009 / 250000000000 : ℝ)
  frameHi := (752150510977 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12071]
  agentFrame_pos := by norm_num only [agent12071]
  worldRadius := (2297668199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12071]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1412253781 / 1000000000000 : ℝ)
  lowerTail := (1782031939 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8235953023 / 1000000000000 : ℝ)
  ledger := by
    have h : (75120233 / 62500000000 : ℚ) +
        (1077288427 / 100000000000000000 : ℚ) / (2297668199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1412253781 / 1000000000000 : ℚ) + (1782031939 / 1000000000000 : ℚ) ≤
        (8235953023 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((75120233 / 62500000000 : ℚ) +
        (1077288427 / 100000000000000000 : ℚ) / (2297668199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1412253781 / 1000000000000 : ℚ) + (1782031939 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8235953023 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12071]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12071 :
    2 * 160 < 12071 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994543 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12071 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12072 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12072. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12072 : WorldParameters where
  hiddenCharge := (600935999 / 500000000000 : ℝ)
  frame := (63478313157 / 100000000000 : ℝ)
  moment := (10770547543 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12072 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752125266633 / 500000000000 : ℝ)
    root := (1887769213 / 250000000000 : ℝ) }

noncomputable def scalar12072 : ScalarCertificate 12072 world12072 agent12072 where
  dimensionLo := 12072
  dimensionHi := 12072
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2298070499 / 1000000000000 : ℝ)
  frameLo := (63478313157 / 100000000000 : ℝ)
  frameHi := (752125266633 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12072]
  agentFrame_pos := by norm_num only [agent12072]
  worldRadius := (2298070499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12072]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1410974139 / 1000000000000 : ℝ)
  lowerTail := (55641713 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (823196767 / 100000000000 : ℝ)
  ledger := by
    have h : (600935999 / 500000000000 : ℚ) +
        (10770547543 / 1000000000000000000 : ℚ) / (2298070499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1410974139 / 1000000000000 : ℚ) + (55641713 / 31250000000 : ℚ) ≤
        (823196767 / 100000000000 : ℚ) := by norm_num only
    have hc : (((600935999 / 500000000000 : ℚ) +
        (10770547543 / 1000000000000000000 : ℚ) / (2298070499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1410974139 / 1000000000000 : ℚ) + (55641713 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((823196767 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12072]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12072 :
    2 * 160 < 12072 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999963 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12072 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12073 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12073. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12073 : WorldParameters where
  hiddenCharge := (1201820283 / 1000000000000 : ℝ)
  frame := (25390710949 / 40000000000 : ℝ)
  moment := (2692052881 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12073 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504200081241 / 1000000000000 : ℝ)
    root := (1510077643 / 200000000000 : ℝ) }

noncomputable def scalar12073 : ScalarCertificate 12073 world12073 agent12073 where
  dimensionLo := 12073
  dimensionHi := 12073
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2298472799 / 1000000000000 : ℝ)
  frameLo := (25390710949 / 40000000000 : ℝ)
  frameHi := (1504200081241 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12073]
  agentFrame_pos := by norm_num only [agent12073]
  worldRadius := (2298472799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12073]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (704847943 / 500000000000 : ℝ)
  lowerTail := (889519617 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (51424913 / 6250000000 : ℝ)
  ledger := by
    have h : (1201820283 / 1000000000000 : ℚ) +
        (2692052881 / 250000000000000000 : ℚ) / (2298472799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704847943 / 500000000000 : ℚ) + (889519617 / 500000000000 : ℚ) ≤
        (51424913 / 6250000000 : ℚ) := by norm_num only
    have hc : (((1201820283 / 1000000000000 : ℚ) +
        (2692052881 / 250000000000000000 : ℚ) / (2298472799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704847943 / 500000000000 : ℚ) + (889519617 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((51424913 / 6250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12073]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12073 :
    2 * 160 < 12073 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (109999979 / 10000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12073 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12074 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12074. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12074 : WorldParameters where
  hiddenCharge := (600884291 / 500000000000 : ℝ)
  frame := (317376209251 / 500000000000 : ℝ)
  moment := (10765876213 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12074 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504149659777 / 1000000000000 : ℝ)
    root := (3774849901 / 500000000000 : ℝ) }

noncomputable def scalar12074 : ScalarCertificate 12074 world12074 agent12074 where
  dimensionLo := 12074
  dimensionHi := 12074
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2298875199 / 1000000000000 : ℝ)
  frameLo := (317376209251 / 500000000000 : ℝ)
  frameHi := (1504149659777 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12074]
  agentFrame_pos := by norm_num only [agent12074]
  worldRadius := (2298875199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12074]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (704209539 / 500000000000 : ℝ)
  lowerTail := (444386313 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4015629 / 488281250 : ℝ)
  ledger := by
    have h : (600884291 / 500000000000 : ℚ) +
        (10765876213 / 1000000000000000000 : ℚ) / (2298875199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704209539 / 500000000000 : ℚ) + (444386313 / 250000000000 : ℚ) ≤
        (4015629 / 488281250 : ℚ) := by norm_num only
    have hc : (((600884291 / 500000000000 : ℚ) +
        (10765876213 / 1000000000000000000 : ℚ) / (2298875199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704209539 / 500000000000 : ℚ) + (444386313 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4015629 / 488281250 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12074]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12074 :
    2 * 160 < 12074 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999049 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12074 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12075 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12075. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12075 : WorldParameters where
  hiddenCharge := (37553653 / 31250000000 : ℝ)
  frame := (317368532949 / 500000000000 : ℝ)
  moment := (10763541609 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12075 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752049631389 / 500000000000 : ℝ)
    root := (7549011613 / 1000000000000 : ℝ) }

noncomputable def scalar12075 : ScalarCertificate 12075 world12075 agent12075 where
  dimensionLo := 12075
  dimensionHi := 12075
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2299277599 / 1000000000000 : ℝ)
  frameLo := (317368532949 / 500000000000 : ℝ)
  frameHi := (752049631389 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12075]
  agentFrame_pos := by norm_num only [agent12075]
  worldRadius := (2299277599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12075]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (281428721 / 200000000000 : ℝ)
  lowerTail := (88802637 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8220033939 / 1000000000000 : ℝ)
  ledger := by
    have h : (37553653 / 31250000000 : ℚ) +
        (10763541609 / 1000000000000000000 : ℚ) / (2299277599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (281428721 / 200000000000 : ℚ) + (88802637 / 50000000000 : ℚ) ≤
        (8220033939 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((37553653 / 31250000000 : ℚ) +
        (10763541609 / 1000000000000000000 : ℚ) / (2299277599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (281428721 / 200000000000 : ℚ) + (88802637 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8220033939 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12075]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12075 :
    2 * 160 < 12075 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997567 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12075 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12076 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12076. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12076 : WorldParameters where
  hiddenCharge := (150208153 / 125000000000 : ℝ)
  frame := (317360857957 / 500000000000 : ℝ)
  moment := (10761207713 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12076 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504048896299 / 1000000000000 : ℝ)
    root := (3774161863 / 500000000000 : ℝ) }

noncomputable def scalar12076 : ScalarCertificate 12076 world12076 agent12076 where
  dimensionLo := 12076
  dimensionHi := 12076
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2299679899 / 1000000000000 : ℝ)
  frameLo := (317360857957 / 500000000000 : ℝ)
  frameHi := (1504048896299 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12076]
  agentFrame_pos := by norm_num only [agent12076]
  worldRadius := (2299679899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12076]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (43933421 / 31250000000 : ℝ)
  lowerTail := (17745617 / 10000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8216063507 / 1000000000000 : ℝ)
  ledger := by
    have h : (150208153 / 125000000000 : ℚ) +
        (10761207713 / 1000000000000000000 : ℚ) / (2299679899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (43933421 / 31250000000 : ℚ) + (17745617 / 10000000000 : ℚ) ≤
        (8216063507 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((150208153 / 125000000000 : ℚ) +
        (10761207713 / 1000000000000000000 : ℚ) / (2299679899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (43933421 / 31250000000 : ℚ) + (17745617 / 10000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8216063507 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12076]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12076 :
    2 * 160 < 12076 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998909 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12076 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12077 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12077. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12077 : WorldParameters where
  hiddenCharge := (1201613567 / 1000000000000 : ℝ)
  frame := (158676592137 / 250000000000 : ℝ)
  moment := (2689718631 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12077 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751999280159 / 500000000000 : ℝ)
    root := (1509527197 / 200000000000 : ℝ) }

noncomputable def scalar12077 : ScalarCertificate 12077 world12077 agent12077 where
  dimensionLo := 12077
  dimensionHi := 12077
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2300082199 / 1000000000000 : ℝ)
  frameLo := (158676592137 / 250000000000 : ℝ)
  frameHi := (751999280159 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12077]
  agentFrame_pos := by norm_num only [agent12077]
  worldRadius := (2300082199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12077]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1404596633 / 1000000000000 : ℝ)
  lowerTail := (1773072093 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8212096633 / 1000000000000 : ℝ)
  ledger := by
    have h : (1201613567 / 1000000000000 : ℚ) +
        (2689718631 / 250000000000000000 : ℚ) / (2300082199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1404596633 / 1000000000000 : ℚ) + (1773072093 / 1000000000000 : ℚ) ≤
        (8212096633 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1201613567 / 1000000000000 : ℚ) +
        (2689718631 / 250000000000000000 : ℚ) / (2300082199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1404596633 / 1000000000000 : ℚ) + (1773072093 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8212096633 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12077]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12077 :
    2 * 160 < 12077 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999621 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12077 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12078 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12078. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12078 : WorldParameters where
  hiddenCharge := (300390481 / 250000000000 : ℝ)
  frame := (634691023801 / 1000000000000 : ℝ)
  moment := (10756542041 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12078 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503948254813 / 1000000000000 : ℝ)
    root := (1886737117 / 250000000000 : ℝ) }

noncomputable def scalar12078 : ScalarCertificate 12078 world12078 agent12078 where
  dimensionLo := 12078
  dimensionHi := 12078
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2300484599 / 1000000000000 : ℝ)
  frameLo := (634691023801 / 1000000000000 : ℝ)
  frameHi := (1503948254813 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12078]
  agentFrame_pos := by norm_num only [agent12078]
  worldRadius := (2300484599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12078]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (87707827 / 62500000000 : ℝ)
  lowerTail := (1771584079 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4104066721 / 500000000000 : ℝ)
  ledger := by
    have h : (300390481 / 250000000000 : ℚ) +
        (10756542041 / 1000000000000000000 : ℚ) / (2300484599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (87707827 / 62500000000 : ℚ) + (1771584079 / 1000000000000 : ℚ) ≤
        (4104066721 / 500000000000 : ℚ) := by norm_num only
    have hc : (((300390481 / 250000000000 : ℚ) +
        (10756542041 / 1000000000000000000 : ℚ) / (2300484599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (87707827 / 62500000000 : ℚ) + (1771584079 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4104066721 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12078]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12078 :
    2 * 160 < 12078 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999817 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12078 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12079 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12079. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12079 : WorldParameters where
  hiddenCharge := (240302059 / 200000000000 : ℝ)
  frame := (634675681671 / 1000000000000 : ℝ)
  moment := (2150842053 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12079 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503897979763 / 1000000000000 : ℝ)
    root := (3773130587 / 500000000000 : ℝ) }

noncomputable def scalar12079 : ScalarCertificate 12079 world12079 agent12079 where
  dimensionLo := 12079
  dimensionHi := 12079
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2300886899 / 1000000000000 : ℝ)
  frameLo := (634675681671 / 1000000000000 : ℝ)
  frameHi := (1503897979763 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12079]
  agentFrame_pos := by norm_num only [agent12079]
  worldRadius := (2300886899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12079]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (701027551 / 500000000000 : ℝ)
  lowerTail := (885048733 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8204173931 / 1000000000000 : ℝ)
  ledger := by
    have h : (240302059 / 200000000000 : ℚ) +
        (2150842053 / 200000000000000000 : ℚ) / (2300886899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (701027551 / 500000000000 : ℚ) + (885048733 / 500000000000 : ℚ) ≤
        (8204173931 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((240302059 / 200000000000 : ℚ) +
        (2150842053 / 200000000000000000 : ℚ) / (2300886899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (701027551 / 500000000000 : ℚ) + (885048733 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8204173931 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12079]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12079 :
    2 * 160 < 12079 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998381 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12079 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12080 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12080. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12080 : WorldParameters where
  hiddenCharge := (1201458681 / 1000000000000 : ℝ)
  frame := (634660342157 / 1000000000000 : ℝ)
  moment := (2150375839 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12080 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503847729071 / 1000000000000 : ℝ)
    root := (943196763 / 125000000000 : ℝ) }

noncomputable def scalar12080 : ScalarCertificate 12080 world12080 agent12080 where
  dimensionLo := 12080
  dimensionHi := 12080
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2301289299 / 1000000000000 : ℝ)
  frameLo := (634660342157 / 1000000000000 : ℝ)
  frameHi := (1503847729071 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12080]
  agentFrame_pos := by norm_num only [agent12080]
  worldRadius := (2301289299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12080]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (700393191 / 500000000000 : ℝ)
  lowerTail := (221076551 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4100109017 / 500000000000 : ℝ)
  ledger := by
    have h : (1201458681 / 1000000000000 : ℚ) +
        (2150375839 / 200000000000000000 : ℚ) / (2301289299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (700393191 / 500000000000 : ℚ) + (221076551 / 125000000000 : ℚ) ≤
        (4100109017 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1201458681 / 1000000000000 : ℚ) +
        (2150375839 / 200000000000000000 : ℚ) / (2301289299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (700393191 / 500000000000 : ℚ) + (221076551 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4100109017 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12080]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12080 :
    2 * 160 < 12080 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999979 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12080 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12081 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12081. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12081 : WorldParameters where
  hiddenCharge := (1201407081 / 1000000000000 : ℝ)
  frame := (634645005259 / 1000000000000 : ℝ)
  moment := (1074954883 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12081 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (300759502973 / 200000000000 : ℝ)
    root := (3772443629 / 500000000000 : ℝ) }

noncomputable def scalar12081 : ScalarCertificate 12081 world12081 agent12081 where
  dimensionLo := 12081
  dimensionHi := 12081
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2301691599 / 1000000000000 : ℝ)
  frameLo := (634645005259 / 1000000000000 : ℝ)
  frameHi := (300759502973 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12081]
  agentFrame_pos := by norm_num only [agent12081]
  worldRadius := (2301691599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12081]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (349879739 / 250000000000 : ℝ)
  lowerTail := (883564391 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2049066467 / 250000000000 : ℝ)
  ledger := by
    have h : (1201407081 / 1000000000000 : ℚ) +
        (1074954883 / 100000000000000000 : ℚ) / (2301691599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (349879739 / 250000000000 : ℚ) + (883564391 / 500000000000 : ℚ) ≤
        (2049066467 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1201407081 / 1000000000000 : ℚ) +
        (1074954883 / 100000000000000000 : ℚ) / (2301691599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (349879739 / 250000000000 : ℚ) + (883564391 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2049066467 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12081]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12081 :
    2 * 160 < 12081 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995837 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12081 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12082 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12082. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12082 : WorldParameters where
  hiddenCharge := (150169437 / 125000000000 : ℝ)
  frame := (9916088609 / 15625000000 : ℝ)
  moment := (2686804793 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12082 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751873662487 / 500000000000 : ℝ)
    root := (1508840127 / 200000000000 : ℝ) }

noncomputable def scalar12082 : ScalarCertificate 12082 world12082 agent12082 where
  dimensionLo := 12082
  dimensionHi := 12082
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2302093999 / 1000000000000 : ℝ)
  frameLo := (9916088609 / 15625000000 : ℝ)
  frameHi := (751873662487 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12082]
  agentFrame_pos := by norm_num only [agent12082]
  worldRadius := (2302093999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12082]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (699126467 / 500000000000 : ℝ)
  lowerTail := (1765646707 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8192317311 / 1000000000000 : ℝ)
  ledger := by
    have h : (150169437 / 125000000000 : ℚ) +
        (2686804793 / 250000000000000000 : ℚ) / (2302093999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (699126467 / 500000000000 : ℚ) + (1765646707 / 1000000000000 : ℚ) ≤
        (8192317311 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((150169437 / 125000000000 : ℚ) +
        (2686804793 / 250000000000000000 : ℚ) / (2302093999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (699126467 / 500000000000 : ℚ) + (1765646707 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8192317311 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12082]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12082 :
    2 * 160 < 12082 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999663 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12082 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12083 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12083. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12083 : WorldParameters where
  hiddenCharge := (48052157 / 40000000000 : ℝ)
  frame := (158653584827 / 250000000000 : ℝ)
  moment := (10744890219 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12083 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503697165453 / 1000000000000 : ℝ)
    root := (942939289 / 125000000000 : ℝ) }

noncomputable def scalar12083 : ScalarCertificate 12083 world12083 agent12083 where
  dimensionLo := 12083
  dimensionHi := 12083
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2302496299 / 1000000000000 : ℝ)
  frameLo := (158653584827 / 250000000000 : ℝ)
  frameHi := (1503697165453 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12083]
  agentFrame_pos := by norm_num only [agent12083]
  worldRadius := (2302496299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12083]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1396988241 / 1000000000000 : ℝ)
  lowerTail := (1764166093 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8188372543 / 1000000000000 : ℝ)
  ledger := by
    have h : (48052157 / 40000000000 : ℚ) +
        (10744890219 / 1000000000000000000 : ℚ) / (2302496299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1396988241 / 1000000000000 : ℚ) + (1764166093 / 1000000000000 : ℚ) ≤
        (8188372543 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((48052157 / 40000000000 : ℚ) +
        (10744890219 / 1000000000000000000 : ℚ) / (2302496299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1396988241 / 1000000000000 : ℚ) + (1764166093 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8188372543 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12083]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12083 :
    2 * 160 < 12083 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996243 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12083 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12059 :
    (1202545609008252229337 / 1000000000000000000000000 : ℝ) ≤ world12059.hiddenCharge ∧
    (634983022367830604464009 / 1000000000000000000000000 : ℝ) ≤ world12059.frame ∧
    (10800980322082087 / 1000000000000000000000000 : ℝ) ≤ world12059.moment ∧
    (75245457604636878236091 / 50000000000000000000000 : ℝ) ≤ agent12059.frame ∧
    (3780024697913918508181 / 500000000000000000000000 : ℝ) ≤ agent12059.root ∧
    scalar12059.worldRadius ≤ (2292839999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (65241040802376557287 / 50000000000000000000000 : ℝ) ≤ agent12059.charge ∧
    (1427715279790565161243 / 1000000000000000000000000 : ℝ) ≤ scalar12059.upperTail ∧
    (900057045039858195101 / 500000000000000000000000 : ℝ) ≤ scalar12059.lowerTail ∧
    scalar12059.totalBudget ≤ (8284066059378664440349 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12059, agent12059, scalar12059] <;> simp only [true_and]

theorem source_rounding12060 :
    (37577928308765750749 / 31250000000000000000000 : ℝ) ≤ world12060.hiddenCharge ∧
    (79370953798456246954097 / 125000000000000000000000 : ℝ) ≤ world12060.frame ∧
    (10798635076779561 / 1000000000000000000000000 : ℝ) ≤ world12060.moment ∧
    (376214578231287038147551 / 250000000000000000000000 : ℝ) ≤ agent12060.frame ∧
    (472459864210077260757 / 62500000000000000000000 : ℝ) ≤ agent12060.root ∧
    scalar12060.worldRadius ≤ (2293242299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (652233117207049428293 / 500000000000000000000000 : ℝ) ≤ agent12060.charge ∧
    (1426419213284657305769 / 1000000000000000000000000 : ℝ) ≤ scalar12060.upperTail ∧
    (899299424894040327701 / 500000000000000000000000 : ℝ) ≤ scalar12060.lowerTail ∧
    scalar12060.totalBudget ≤ (2070009027337054953713 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12060, agent12060, scalar12060] <;> simp only [true_and]

theorem source_rounding12061 :
    (1202441817249648680637 / 1000000000000000000000000 : ℝ) ≤ world12061.hiddenCharge ∧
    (634952241037580502207099 / 1000000000000000000000000 : ℝ) ≤ world12061.frame ∧
    (2159258108572459 / 200000000000000000000000 : ℝ) ≤ world12061.moment ∧
    (300961499704836129950747 / 200000000000000000000000 : ℝ) ≤ agent12061.frame ∧
    (7558666485265455409911 / 1000000000000000000000000 : ℝ) ≤ agent12061.root ∧
    scalar12061.worldRadius ≤ (2293644699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (326028024876410481807 / 250000000000000000000000 : ℝ) ≤ agent12061.charge ∧
    (44535143381792164309 / 31250000000000000000000 : ℝ) ≤ scalar12061.upperTail ∧
    (1797085199810511958709 / 1000000000000000000000000 : ℝ) ≤ scalar12061.lowerTail ∧
    scalar12061.totalBudget ≤ (8276009853657342188333 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12061, agent12061, scalar12061] <;> simp only [true_and]

theorem source_rounding12062 :
    (1202389943110391649501 / 1000000000000000000000000 : ℝ) ≤ world12062.hiddenCharge ∧
    (634936854316905831289989 / 1000000000000000000000000 : ℝ) ≤ world12062.frame ∧
    (10793946720053533 / 1000000000000000000000000 : ℝ) ≤ world12062.moment ∧
    (188094589368543310741273 / 125000000000000000000000 : ℝ) ≤ agent12062.frame ∧
    (944746930890939158231 / 125000000000000000000000 : ℝ) ≤ agent12062.root ∧
    scalar12062.worldRadius ≤ (2294046999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (130375841064891121217 / 100000000000000000000000 : ℝ) ≤ agent12062.charge ∧
    (355957831663609492869 / 250000000000000000000000 : ℝ) ≤ scalar12062.upperTail ∧
    (1795573047815281217651 / 1000000000000000000000000 : ℝ) ≤ scalar12062.lowerTail ∧
    scalar12062.totalBudget ≤ (4135993739841108656253 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12062, agent12062, scalar12062] <;> simp only [true_and]

theorem source_rounding12063 :
    (601169041728716934623 / 500000000000000000000000 : ℝ) ≤ world12063.hiddenCharge ∧
    (634921470224910050381297 / 1000000000000000000000000 : ℝ) ≤ world12063.frame ∧
    (2697900902019093 / 250000000000000000000000 : ℝ) ≤ world12063.moment ∧
    (1504705962175560806061417 / 1000000000000000000000000 : ℝ) ≤ agent12063.frame ∧
    (3778642278649963878087 / 500000000000000000000000 : ℝ) ≤ agent12063.root ∧
    scalar12063.worldRadius ≤ (2294449399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (651702583585912995871 / 500000000000000000000000 : ℝ) ≤ agent12063.charge ∧
    (142253946540172329983 / 100000000000000000000000 : ℝ) ≤ scalar12063.upperTail ∧
    (112128903042216600703 / 62500000000000000000000 : ℝ) ≤ scalar12063.lowerTail ∧
    scalar12063.totalBudget ≤ (8267968720954591832549 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12063, agent12063, scalar12063] <;> simp only [true_and]

theorem source_rounding12064 :
    (601143119142742867943 / 500000000000000000000000 : ℝ) ≤ world12064.hiddenCharge ∧
    (2480101909222177083689 / 3906250000000000000000 : ℝ) ≤ world12064.frame ∧
    (431570448266173 / 40000000000000000000000 : ℝ) ≤ world12064.moment ∧
    (1504655240183766317027003 / 1000000000000000000000000 : ℝ) ≤ agent12064.frame ∧
    (7556593893386380584441 / 1000000000000000000000000 : ℝ) ≤ agent12064.root ∧
    scalar12064.worldRadius ≤ (2294851699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (130305236840347171387 / 100000000000000000000000 : ℝ) ≤ agent12064.charge ∧
    (71062445040180016227 / 50000000000000000000000 : ℝ) ≤ scalar12064.upperTail ∧
    (1792553276350914374517 / 1000000000000000000000000 : ℝ) ≤ scalar12064.lowerTail ∧
    scalar12064.totalBudget ≤ (2065988425723180277871 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12064, agent12064, scalar12064] <;> simp only [true_and]

theorem source_rounding12065 :
    (1202234407589254532413 / 1000000000000000000000000 : ℝ) ≤ world12065.hiddenCharge ∧
    (634890709924092212290747 / 1000000000000000000000000 : ℝ) ≤ world12065.frame ∧
    (10786919515510817 / 1000000000000000000000000 : ℝ) ≤ world12065.moment ∧
    (1504604548950933252405433 / 1000000000000000000000000 : ℝ) ≤ agent12065.frame ∧
    (1511180691046985316383 / 200000000000000000000000 : ℝ) ≤ agent12065.root ∧
    scalar12065.worldRadius ≤ (2295254099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (16283750170926221757 / 12500000000000000000000 : ℝ) ≤ agent12065.charge ∧
    (283991959309461781297 / 200000000000000000000000 : ℝ) ≤ scalar12065.upperTail ∧
    (895522860428172552387 / 500000000000000000000000 : ℝ) ≤ scalar12065.lowerTail ∧
    scalar12065.totalBudget ≤ (8259942423586601052231 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12065, agent12065, scalar12065] <;> simp only [true_and]

theorem source_rounding12066 :
    (1202182591363452804743 / 1000000000000000000000000 : ℝ) ≤ world12066.hiddenCharge ∧
    (25395013348553579061021 / 40000000000000000000000 : ℝ) ≤ world12066.frame ∧
    (2696144633592379 / 250000000000000000000000 : ℝ) ≤ world12066.moment ∧
    (1504553882376440217625877 / 1000000000000000000000000 : ℝ) ≤ agent12066.frame ∧
    (1511042664073601978837 / 200000000000000000000000 : ℝ) ≤ agent12066.root ∧
    scalar12066.worldRadius ≤ (2295656499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1302348102315115099127 / 1000000000000000000000000 : ℝ) ≤ agent12066.charge ∧
    (709336052780966810529 / 500000000000000000000000 : ℝ) ≤ scalar12066.upperTail ∧
    (1789539717980544332661 / 1000000000000000000000000 : ℝ) ≤ scalar12066.lowerTail ∧
    scalar12066.totalBudget ≤ (4127967474528435542333 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12066, agent12066, scalar12066] <;> simp only [true_and]

theorem source_rounding12067 :
    (1202130789602792780229 / 1000000000000000000000000 : ℝ) ≤ world12067.hiddenCharge ∧
    (317429980064702092859711 / 500000000000000000000000 : ℝ) ≤ world12067.frame ∧
    (2695559565738529 / 250000000000000000000000 : ℝ) ≤ world12067.moment ∧
    (1504503252595836299336079 / 1000000000000000000000000 : ℝ) ≤ agent12067.frame ∧
    (944315416658652763231 / 125000000000000000000000 : ℝ) ≤ agent12067.root ∧
    scalar12067.worldRadius ≤ (2296058799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1301996633659094238129 / 1000000000000000000000000 : ℝ) ≤ agent12067.charge ∧
    (1417385668857338985131 / 1000000000000000000000000 : ℝ) ≤ scalar12067.upperTail ∧
    (1788035103115332585869 / 1000000000000000000000000 : ℝ) ≤ scalar12067.lowerTail ∧
    scalar12067.totalBudget ≤ (8251931131479595964861 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12067, agent12067, scalar12067] <;> simp only [true_and]

theorem source_rounding12068 :
    (601039501150996668051 / 500000000000000000000000 : ℝ) ≤ world12068.hiddenCharge ∧
    (634844589170071662697567 / 1000000000000000000000000 : ℝ) ≤ world12068.frame ∧
    (2694974675247153 / 250000000000000000000000 : ℝ) ≤ world12068.moment ∧
    (18805658092877765156901 / 12500000000000000000000 : ℝ) ≤ agent12068.frame ∧
    (1510766714295529293987 / 200000000000000000000000 : ℝ) ≤ agent12068.root ∧
    scalar12068.worldRadius ≤ (2296461099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1301645607039762788013 / 1000000000000000000000000 : ℝ) ≤ agent12068.charge ∧
    (1416100578885521031293 / 1000000000000000000000000 : ℝ) ≤ scalar12068.upperTail ∧
    (1786531970021772076603 / 1000000000000000000000000 : ℝ) ≤ scalar12068.lowerTail ∧
    scalar12068.totalBudget ≤ (1649586196055256363779 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12068, agent12068, scalar12068] <;> simp only [true_and]

theorem source_rounding12069 :
    (1202027229455773028057 / 1000000000000000000000000 : ℝ) ≤ world12069.hiddenCharge ∧
    (126965844167025490117751 / 200000000000000000000000 : ℝ) ≤ world12069.frame ∧
    (10777559848197021 / 1000000000000000000000000 : ℝ) ≤ world12069.moment ∧
    (752201036468146760254787 / 500000000000000000000000 : ℝ) ≤ agent12069.frame ∧
    (755314403484196971111 / 100000000000000000000000 : ℝ) ≤ agent12069.root ∧
    scalar12069.worldRadius ≤ (2296863499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (325323755448000831613 / 250000000000000000000000 : ℝ) ≤ agent12069.charge ∧
    (282963388438452757389 / 200000000000000000000000 : ℝ) ≤ scalar12069.upperTail ∧
    (892515223157700423053 / 500000000000000000000000 : ℝ) ≤ scalar12069.lowerTail ∧
    scalar12069.totalBudget ≤ (8243934549347785144801 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12069, agent12069, scalar12069] <;> simp only [true_and]

theorem source_rounding12070 :
    (1201975471058851486801 / 1000000000000000000000000 : ℝ) ≤ world12070.hiddenCharge ∧
    (634813855123857448003317 / 1000000000000000000000000 : ℝ) ≤ world12070.frame ∧
    (10775221704303439 / 1000000000000000000000000 : ℝ) ≤ world12070.moment ∧
    (18804394189620467710651 / 12500000000000000000000 : ℝ) ≤ agent12070.frame ∧
    (944056840401379500369 / 125000000000000000000000 : ℝ) ≤ agent12070.root ∧
    scalar12070.worldRadius ≤ (2297265799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (260188975450370229673 / 200000000000000000000000 : ℝ) ≤ agent12070.charge ∧
    (1413534618135832659221 / 1000000000000000000000000 : ℝ) ≤ scalar12070.upperTail ∧
    (1783530372831540227099 / 1000000000000000000000000 : ℝ) ≤ scalar12070.lowerTail ∧
    scalar12070.totalBudget ≤ (4119970947711472584409 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12070, agent12070, scalar12070] <;> simp only [true_and]

theorem source_rounding12071 :
    (300480931776488050291 / 250000000000000000000000 : ℝ) ≤ world12071.hiddenCharge ∧
    (634798492035547762128869 / 1000000000000000000000000 : ℝ) ≤ world12071.frame ∧
    (10772884269032153 / 1000000000000000000000000 : ℝ) ≤ world12071.moment ∧
    (1504301021953147227951461 / 1000000000000000000000000 : ℝ) ≤ agent12071.frame ∧
    (7551765714026662947501 / 1000000000000000000000000 : ℝ) ≤ agent12071.root ∧
    scalar12071.worldRadius ≤ (2297668199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (650297586378246020309 / 500000000000000000000000 : ℝ) ≤ agent12071.charge ∧
    (1412253780948675514651 / 1000000000000000000000000 : ℝ) ≤ scalar12071.upperTail ∧
    (1782031938310227358863 / 1000000000000000000000000 : ℝ) ≤ scalar12071.lowerTail ∧
    scalar12071.totalBudget ≤ (4117976511731008177819 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12071, agent12071, scalar12071] <;> simp only [true_and]

theorem source_rounding12072 :
    (37558499924743828539 / 31250000000000000000000 : ℝ) ≤ world12072.hiddenCharge ∧
    (634783131569484740681209 / 1000000000000000000000000 : ℝ) ≤ world12072.frame ∧
    (5385273771053819 / 500000000000000000000000 : ℝ) ≤ world12072.moment ∧
    (1504250533265839312789887 / 1000000000000000000000000 : ℝ) ≤ agent12072.frame ∧
    (7551076851936086946397 / 1000000000000000000000000 : ℝ) ≤ agent12072.root ∧
    scalar12072.worldRadius ≤ (2298070499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (650122953822130030689 / 500000000000000000000000 : ℝ) ≤ agent12072.charge ∧
    (1410974138481110390727 / 1000000000000000000000000 : ℝ) ≤ scalar12072.upperTail ∧
    (1780534815873986515011 / 1000000000000000000000000 : ℝ) ≤ scalar12072.lowerTail ∧
    scalar12072.totalBudget ≤ (8231967670448744127167 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12072, agent12072, scalar12072] <;> simp only [true_and]

theorem source_rounding12073 :
    (600910141255565417519 / 500000000000000000000000 : ℝ) ≤ world12073.hiddenCharge ∧
    (79345971715619383522701 / 125000000000000000000000 : ℝ) ≤ world12073.frame ∧
    (10768211523254449 / 1000000000000000000000000 : ℝ) ≤ world12073.moment ∧
    (1504200081240002143147279 / 1000000000000000000000000 : ℝ) ≤ agent12073.frame ∧
    (5898740792498230233 / 781250000000000000000 : ℝ) ≤ agent12073.root ∧
    scalar12073.worldRadius ≤ (2298472799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (649948540627317662067 / 500000000000000000000000 : ℝ) ≤ agent12073.charge ∧
    (1409695885941449038319 / 1000000000000000000000000 : ℝ) ≤ scalar12073.upperTail ∧
    (889519616931074288973 / 500000000000000000000000 : ℝ) ≤ scalar12073.lowerTail ∧
    scalar12073.totalBudget ≤ (2056996520202442851753 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12073, agent12073, scalar12073] <;> simp only [true_and]

theorem source_rounding12074 :
    (1201768581858666650289 / 1000000000000000000000000 : ℝ) ≤ world12074.hiddenCharge ∧
    (634752418501245565595791 / 1000000000000000000000000 : ℝ) ≤ world12074.frame ∧
    (10765876212197217 / 1000000000000000000000000 : ℝ) ≤ world12074.moment ∧
    (752074829888329580680069 / 500000000000000000000000 : ℝ) ≤ agent12074.frame ∧
    (7549699801261078078929 / 1000000000000000000000000 : ℝ) ≤ agent12074.root ∧
    scalar12074.worldRadius ≤ (2298875199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (64977434646412089317 / 50000000000000000000000 : ℝ) ≤ agent12074.charge ∧
    (1408419077857827156381 / 1000000000000000000000000 : ℝ) ≤ scalar12074.upperTail ∧
    (888772625965648412061 / 500000000000000000000000 : ℝ) ≤ scalar12074.lowerTail ∧
    scalar12074.totalBudget ≤ (8224008192137546823159 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12074, agent12074, scalar12074] <;> simp only [true_and]

theorem source_rounding12075 :
    (1201716895629144680181 / 1000000000000000000000000 : ℝ) ≤ world12075.hiddenCharge ∧
    (39671066618602721384023 / 62500000000000000000000 : ℝ) ≤ world12075.frame ∧
    (5381770804330411 / 500000000000000000000000 : ℝ) ≤ world12075.moment ∧
    (752049631388999588391859 / 500000000000000000000000 : ℝ) ≤ agent12075.frame ∧
    (754901161237574536953 / 100000000000000000000000 : ℝ) ≤ agent12075.root ∧
    scalar12075.worldRadius ≤ (2299277599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (649600371003422521359 / 500000000000000000000000 : ℝ) ≤ agent12075.charge ∧
    (281428720931694766901 / 200000000000000000000000 : ℝ) ≤ scalar12075.upperTail ∧
    (888026369650741989633 / 500000000000000000000000 : ℝ) ≤ scalar12075.lowerTail ∧
    scalar12075.totalBudget ≤ (8220033939209545034933 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12075, agent12075, scalar12075] <;> simp only [true_and]

theorem source_rounding12076 :
    (1201665223817299326101 / 1000000000000000000000000 : ℝ) ≤ world12076.hiddenCharge ∧
    (634721715913436302754463 / 1000000000000000000000000 : ℝ) ≤ world12076.frame ∧
    (2690301928092541 / 250000000000000000000000 : ℝ) ≤ world12076.moment ∧
    (30080977925978295907671 / 20000000000000000000000 : ℝ) ≤ agent12076.frame ∧
    (1509664745020612317071 / 200000000000000000000000 : ℝ) ≤ agent12076.root ∧
    scalar12076.worldRadius ≤ (2299679899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1298853227833350123153 / 1000000000000000000000000 : ℝ) ≤ agent12076.charge ∧
    (1405869471177847088101 / 1000000000000000000000000 : ℝ) ≤ scalar12076.upperTail ∧
    (1774561699629923239977 / 1000000000000000000000000 : ℝ) ≤ scalar12076.lowerTail ∧
    scalar12076.totalBudget ≤ (4108031753561226000781 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12076, agent12076, scalar12076] <;> simp only [true_and]

theorem source_rounding12077 :
    (600806783208933724027 / 500000000000000000000000 : ℝ) ≤ world12077.hiddenCharge ∧
    (634706368547911589119019 / 1000000000000000000000000 : ℝ) ≤ world12077.frame ∧
    (2689718630762569 / 250000000000000000000000 : ℝ) ≤ world12077.moment ∧
    (1503998560317702754011087 / 1000000000000000000000000 : ℝ) ≤ agent12077.frame ∧
    (7547635984253624293331 / 1000000000000000000000000 : ℝ) ≤ agent12077.root ∧
    scalar12077.worldRadius ≤ (2300082199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1298506149751799295227 / 1000000000000000000000000 : ℝ) ≤ agent12077.charge ∧
    (1404596632371403166009 / 1000000000000000000000000 : ℝ) ≤ scalar12077.upperTail ∧
    (1773072092675514785507 / 1000000000000000000000000 : ℝ) ≤ scalar12077.lowerTail ∧
    scalar12077.totalBudget ≤ (8212096633003910053503 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12077, agent12077, scalar12077] <;> simp only [true_and]

theorem source_rounding12078 :
    (75097620214099445937 / 62500000000000000000000 : ℝ) ≤ world12078.hiddenCharge ∧
    (317345511900178749987239 / 500000000000000000000000 : ℝ) ≤ world12078.frame ∧
    (5378271020213219 / 500000000000000000000000 : ℝ) ≤ world12078.moment ∧
    (93996765925792928938839 / 62500000000000000000000 : ℝ) ≤ agent12078.frame ∧
    (943368558400667209541 / 125000000000000000000000 : ℝ) ≤ agent12078.root ∧
    scalar12078.worldRadius ≤ (2300484599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (40567484597105308479 / 31250000000000000000000 : ℝ) ≤ agent12078.charge ∧
    (701662615524475622537 / 500000000000000000000000 : ℝ) ≤ scalar12078.upperTail ∧
    (354316815690441494797 / 200000000000000000000000 : ℝ) ≤ scalar12078.lowerTail ∧
    scalar12078.totalBudget ≤ (513008340163615105387 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12078, agent12078, scalar12078] <;> simp only [true_and]

theorem source_rounding12079 :
    (1201510294835212155679 / 1000000000000000000000000 : ℝ) ≤ world12079.hiddenCharge ∧
    (317337840835031026451199 / 500000000000000000000000 : ℝ) ≤ world12079.frame ∧
    (672138141513997 / 62500000000000000000000 : ℝ) ≤ world12079.moment ∧
    (1503897979762217971660941 / 1000000000000000000000000 : ℝ) ≤ agent12079.frame ∧
    (7546261173808453558749 / 1000000000000000000000000 : ℝ) ≤ agent12079.root ∧
    scalar12079.worldRadius ≤ (2300886899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1297813299246372020377 / 1000000000000000000000000 : ℝ) ≤ agent12079.charge ∧
    (1402055101919037698979 / 1000000000000000000000000 : ℝ) ≤ scalar12079.upperTail ∧
    (1770097465254720084177 / 1000000000000000000000000 : ℝ) ≤ scalar12079.lowerTail ∧
    scalar12079.totalBudget ≤ (128190217674225117307 / 15625000000000000000000 : ℝ) := by
  norm_num only [world12079, agent12079, scalar12079] <;> simp only [true_and]

theorem source_rounding12080 :
    (150182335080184514703 / 125000000000000000000000 : ℝ) ≤ world12080.hiddenCharge ∧
    (15866508553907846700521 / 25000000000000000000000 : ℝ) ≤ world12080.frame ∧
    (2687969798542077 / 250000000000000000000000 : ℝ) ≤ world12080.moment ∧
    (75192386453501930624881 / 50000000000000000000000 : ℝ) ≤ agent12080.frame ∧
    (1509114820782675826881 / 200000000000000000000000 : ℝ) ≤ agent12080.root ∧
    scalar12080.worldRadius ≤ (2301289299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (81091720344765411507 / 62500000000000000000000 : ℝ) ≤ agent12080.charge ∧
    (280157276231864128727 / 200000000000000000000000 : ℝ) ≤ scalar12080.upperTail ∧
    (1768612407567353672129 / 1000000000000000000000000 : ℝ) ≤ scalar12080.lowerTail ∧
    scalar12080.totalBudget ≤ (8200218034634812074489 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12080, agent12080, scalar12080] <;> simp only [true_and]

theorem source_rounding12081 :
    (600703540419564155279 / 500000000000000000000000 : ℝ) ≤ world12081.hiddenCharge ∧
    (634645005258401742071121 / 1000000000000000000000000 : ℝ) ≤ world12081.frame ∧
    (537477441499251 / 50000000000000000000000 : ℝ) ≤ world12081.moment ∧
    (751898757432053739396161 / 500000000000000000000000 : ℝ) ≤ agent12081.frame ∧
    (1886221814342669190079 / 250000000000000000000000 : ℝ) ≤ agent12081.root ∧
    scalar12081.worldRadius ≤ (2301691599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (32428054631639072449 / 25000000000000000000000 : ℝ) ≤ agent12081.charge ∧
    (1399518955003463357849 / 1000000000000000000000000 : ℝ) ≤ scalar12081.upperTail ∧
    (1767128781057322751291 / 1000000000000000000000000 : ℝ) ≤ scalar12081.lowerTail ∧
    scalar12081.totalBudget ≤ (8196265868634606876407 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12081, agent12081, scalar12081] <;> simp only [true_and]

theorem source_rounding12082 :
    (300338873855730502759 / 250000000000000000000000 : ℝ) ≤ world12082.hiddenCharge ∧
    (634629670975614574904373 / 1000000000000000000000000 : ℝ) ≤ world12082.frame ∧
    (2686804792849989 / 250000000000000000000000 : ℝ) ≤ world12082.moment ∧
    (751873662486934301829091 / 500000000000000000000000 : ℝ) ≤ agent12082.frame ∧
    (301768025361242550033 / 40000000000000000000000 : ℝ) ≤ agent12082.root ∧
    scalar12082.worldRadius ≤ (2302093999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (162097159730502077057 / 125000000000000000000000 : ℝ) ≤ agent12082.charge ∧
    (34956323344420531059 / 25000000000000000000000 : ℝ) ≤ scalar12082.upperTail ∧
    (1765646706432083589119 / 1000000000000000000000000 : ℝ) ≤ scalar12082.lowerTail ∧
    scalar12082.totalBudget ≤ (1638463462216186889679 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12082, agent12082, scalar12082] <;> simp only [true_and]

theorem source_rounding12083 :
    (1201303924387604641967 / 1000000000000000000000000 : ℝ) ≤ world12083.hiddenCharge ∧
    (634614339307241691053113 / 1000000000000000000000000 : ℝ) ≤ world12083.frame ∧
    (335777819316837 / 31250000000000000000000 : ℝ) ≤ world12083.moment ∧
    (1503697165452415426629299 / 1000000000000000000000000 : ℝ) ≤ agent12083.frame ∧
    (7543514311143353352499 / 1000000000000000000000000 : ℝ) ≤ agent12083.root ∧
    scalar12083.worldRadius ≤ (2302496299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1296432802602427543219 / 1000000000000000000000000 : ℝ) ≤ agent12083.charge ∧
    (1396988240558194531077 / 1000000000000000000000000 : ℝ) ≤ scalar12083.upperTail ∧
    (1764166092438510895829 / 1000000000000000000000000 : ℝ) ≤ scalar12083.lowerTail ∧
    scalar12083.totalBudget ≤ (127943320999106715727 / 15625000000000000000000 : ℝ) := by
  norm_num only [world12083, agent12083, scalar12083] <;> simp only [true_and]

noncomputable def paperAgent12059 : AgentParameters :=
  { agent12059 with charge := (65241041 / 50000000000 : ℝ) }

theorem agent_is_repriced12059 : agent12059 =
    BstLean.Part265.agentRepriced 12059 world12059 paperAgent12059 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12059, agent12059]

noncomputable def paperAgent12060 : AgentParameters :=
  { agent12060 with charge := (652233119 / 500000000000 : ℝ) }

theorem agent_is_repriced12060 : agent12060 =
    BstLean.Part265.agentRepriced 12060 world12060 paperAgent12060 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12060, agent12060]

noncomputable def paperAgent12061 : AgentParameters :=
  { agent12061 with charge := (1304112103 / 1000000000000 : ℝ) }

theorem agent_is_repriced12061 : agent12061 =
    BstLean.Part265.agentRepriced 12061 world12061 paperAgent12061 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12061, agent12061]

noncomputable def paperAgent12062 : AgentParameters :=
  { agent12062 with charge := (651879207 / 500000000000 : ℝ) }

theorem agent_is_repriced12062 : agent12062 =
    BstLean.Part265.agentRepriced 12062 world12062 paperAgent12062 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12062, agent12062]

noncomputable def paperAgent12063 : AgentParameters :=
  { agent12063 with charge := (130340517 / 100000000000 : ℝ) }

theorem agent_is_repriced12063 : agent12063 =
    BstLean.Part265.agentRepriced 12063 world12063 paperAgent12063 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12063, agent12063]

noncomputable def paperAgent12064 : AgentParameters :=
  { agent12064 with charge := (325763093 / 250000000000 : ℝ) }

theorem agent_is_repriced12064 : agent12064 =
    BstLean.Part265.agentRepriced 12064 world12064 paperAgent12064 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12064, agent12064]

noncomputable def paperAgent12065 : AgentParameters :=
  { agent12065 with charge := (1302700017 / 1000000000000 : ℝ) }

theorem agent_is_repriced12065 : agent12065 =
    BstLean.Part265.agentRepriced 12065 world12065 paperAgent12065 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12065, agent12065]

noncomputable def paperAgent12066 : AgentParameters :=
  { agent12066 with charge := (260469621 / 200000000000 : ℝ) }

theorem agent_is_repriced12066 : agent12066 =
    BstLean.Part265.agentRepriced 12066 world12066 paperAgent12066 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12066, agent12066]

noncomputable def paperAgent12067 : AgentParameters :=
  { agent12067 with charge := (1301996637 / 1000000000000 : ℝ) }

theorem agent_is_repriced12067 : agent12067 =
    BstLean.Part265.agentRepriced 12067 world12067 paperAgent12067 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12067, agent12067]

noncomputable def paperAgent12068 : AgentParameters :=
  { agent12068 with charge := (130164561 / 100000000000 : ℝ) }

theorem agent_is_repriced12068 : agent12068 =
    BstLean.Part265.agentRepriced 12068 world12068 paperAgent12068 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12068, agent12068]

noncomputable def paperAgent12069 : AgentParameters :=
  { agent12069 with charge := (52051801 / 40000000000 : ℝ) }

theorem agent_is_repriced12069 : agent12069 =
    BstLean.Part265.agentRepriced 12069 world12069 paperAgent12069 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12069, agent12069]

noncomputable def paperAgent12070 : AgentParameters :=
  { agent12070 with charge := (16261811 / 12500000000 : ℝ) }

theorem agent_is_repriced12070 : agent12070 =
    BstLean.Part265.agentRepriced 12070 world12070 paperAgent12070 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12070, agent12070]

noncomputable def paperAgent12071 : AgentParameters :=
  { agent12071 with charge := (162574397 / 125000000000 : ℝ) }

theorem agent_is_repriced12071 : agent12071 =
    BstLean.Part265.agentRepriced 12071 world12071 paperAgent12071 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12071, agent12071]

noncomputable def paperAgent12072 : AgentParameters :=
  { agent12072 with charge := (1300245911 / 1000000000000 : ℝ) }

theorem agent_is_repriced12072 : agent12072 =
    BstLean.Part265.agentRepriced 12072 world12072 paperAgent12072 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12072, agent12072]

noncomputable def paperAgent12073 : AgentParameters :=
  { agent12073 with charge := (259979417 / 200000000000 : ℝ) }

theorem agent_is_repriced12073 : agent12073 =
    BstLean.Part265.agentRepriced 12073 world12073 paperAgent12073 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12073, agent12073]

noncomputable def paperAgent12074 : AgentParameters :=
  { agent12074 with charge := (162443587 / 125000000000 : ℝ) }

theorem agent_is_repriced12074 : agent12074 =
    BstLean.Part265.agentRepriced 12074 world12074 paperAgent12074 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12074, agent12074]

noncomputable def paperAgent12075 : AgentParameters :=
  { agent12075 with charge := (259840149 / 200000000000 : ℝ) }

theorem agent_is_repriced12075 : agent12075 =
    BstLean.Part265.agentRepriced 12075 world12075 paperAgent12075 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12075, agent12075]

noncomputable def paperAgent12076 : AgentParameters :=
  { agent12076 with charge := (1298853231 / 1000000000000 : ℝ) }

theorem agent_is_repriced12076 : agent12076 =
    BstLean.Part265.agentRepriced 12076 world12076 paperAgent12076 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12076, agent12076]

noncomputable def paperAgent12077 : AgentParameters :=
  { agent12077 with charge := (1298506153 / 1000000000000 : ℝ) }

theorem agent_is_repriced12077 : agent12077 =
    BstLean.Part265.agentRepriced 12077 world12077 paperAgent12077 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12077, agent12077]

noncomputable def paperAgent12078 : AgentParameters :=
  { agent12078 with charge := (129815951 / 100000000000 : ℝ) }

theorem agent_is_repriced12078 : agent12078 =
    BstLean.Part265.agentRepriced 12078 world12078 paperAgent12078 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12078, agent12078]

noncomputable def paperAgent12079 : AgentParameters :=
  { agent12079 with charge := (648906651 / 500000000000 : ℝ) }

theorem agent_is_repriced12079 : agent12079 =
    BstLean.Part265.agentRepriced 12079 world12079 paperAgent12079 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12079, agent12079]

noncomputable def paperAgent12080 : AgentParameters :=
  { agent12080 with charge := (1297467529 / 1000000000000 : ℝ) }

theorem agent_is_repriced12080 : agent12080 =
    BstLean.Part265.agentRepriced 12080 world12080 paperAgent12080 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12080, agent12080]

noncomputable def paperAgent12081 : AgentParameters :=
  { agent12081 with charge := (1297122189 / 1000000000000 : ℝ) }

theorem agent_is_repriced12081 : agent12081 =
    BstLean.Part265.agentRepriced 12081 world12081 paperAgent12081 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12081, agent12081]

noncomputable def paperAgent12082 : AgentParameters :=
  { agent12082 with charge := (1296777281 / 1000000000000 : ℝ) }

theorem agent_is_repriced12082 : agent12082 =
    BstLean.Part265.agentRepriced 12082 world12082 paperAgent12082 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12082, agent12082]

noncomputable def paperAgent12083 : AgentParameters :=
  { agent12083 with charge := (648216403 / 500000000000 : ℝ) }

theorem agent_is_repriced12083 : agent12083 =
    BstLean.Part265.agentRepriced 12083 world12083 paperAgent12083 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12083, agent12083]

end BstLean.Part281
