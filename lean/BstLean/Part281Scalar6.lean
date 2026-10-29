import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12009 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12009. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12009 : WorldParameters where
  hiddenCharge := (1205159367 / 1000000000000 : ℝ)
  frame := (635755990677 / 1000000000000 : ℝ)
  moment := (5459577881 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12009 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (30149492769 / 20000000000 : ℝ)
    root := (151898361 / 20000000000 : ℝ) }

noncomputable def scalar12009 : ScalarCertificate 12009 world12009 agent12009 where
  dimensionLo := 12009
  dimensionHi := 12009
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2272744599 / 1000000000000 : ℝ)
  frameLo := (635755990677 / 1000000000000 : ℝ)
  frameHi := (30149492769 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12009]
  agentFrame_pos := by norm_num only [agent12009]
  worldRadius := (2272744599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12009]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1494265759 / 1000000000000 : ℝ)
  lowerTail := (1877789067 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8490276511 / 1000000000000 : ℝ)
  ledger := by
    have h : (1205159367 / 1000000000000 : ℚ) +
        (5459577881 / 500000000000000000 : ℚ) / (2272744599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1494265759 / 1000000000000 : ℚ) + (1877789067 / 1000000000000 : ℚ) ≤
        (8490276511 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1205159367 / 1000000000000 : ℚ) +
        (5459577881 / 500000000000000000 : ℚ) / (2272744599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1494265759 / 1000000000000 : ℚ) + (1877789067 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8490276511 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12009]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12009 :
    2 * 160 < 12009 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996301 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12009 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12010 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12010. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12010 : WorldParameters where
  hiddenCharge := (301276683 / 250000000000 : ℝ)
  frame := (19866889571 / 31250000000 : ℝ)
  moment := (10916774591 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12010 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753711327781 / 500000000000 : ℝ)
    root := (1898553761 / 250000000000 : ℝ) }

noncomputable def scalar12010 : ScalarCertificate 12010 world12010 agent12010 where
  dimensionLo := 12010
  dimensionHi := 12010
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2273146499 / 1000000000000 : ℝ)
  frameLo := (19866889571 / 31250000000 : ℝ)
  frameHi := (753711327781 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12010]
  agentFrame_pos := by norm_num only [agent12010]
  worldRadius := (2273146499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12010]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1492899869 / 1000000000000 : ℝ)
  lowerTail := (469049309 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8486057901 / 1000000000000 : ℝ)
  ledger := by
    have h : (301276683 / 250000000000 : ℚ) +
        (10916774591 / 1000000000000000000 : ℚ) / (2273146499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1492899869 / 1000000000000 : ℚ) + (469049309 / 250000000000 : ℚ) ≤
        (8486057901 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((301276683 / 250000000000 : ℚ) +
        (10916774591 / 1000000000000000000 : ℚ) / (2273146499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1492899869 / 1000000000000 : ℚ) + (469049309 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8486057901 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12010]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12010 :
    2 * 160 < 12010 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995341 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12010 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12011 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12011. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12011 : WorldParameters where
  hiddenCharge := (37657941 / 31250000000 : ℝ)
  frame := (317862472267 / 500000000000 : ℝ)
  moment := (5457197073 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12011 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1507370668053 / 1000000000000 : ℝ)
    root := (3796756097 / 500000000000 : ℝ) }

noncomputable def scalar12011 : ScalarCertificate 12011 world12011 agent12011 where
  dimensionLo := 12011
  dimensionHi := 12011
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2273548299 / 1000000000000 : ℝ)
  frameLo := (317862472267 / 500000000000 : ℝ)
  frameHi := (1507370668053 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12011]
  agentFrame_pos := by norm_num only [agent12011]
  worldRadius := (2273548299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12011]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (298307027 / 200000000000 : ℝ)
  lowerTail := (937303321 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2120460687 / 250000000000 : ℝ)
  ledger := by
    have h : (37657941 / 31250000000 : ℚ) +
        (5457197073 / 500000000000000000 : ℚ) / (2273548299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (298307027 / 200000000000 : ℚ) + (937303321 / 500000000000 : ℚ) ≤
        (2120460687 / 250000000000 : ℚ) := by norm_num only
    have hc : (((37657941 / 31250000000 : ℚ) +
        (5457197073 / 500000000000000000 : ℚ) / (2273548299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (298307027 / 200000000000 : ℚ) + (937303321 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2120460687 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12011]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12011 :
    2 * 160 < 12011 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997533 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12011 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12012 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12012. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12012 : WorldParameters where
  hiddenCharge := (1205001507 / 1000000000000 : ℝ)
  frame := (635709425461 / 1000000000000 : ℝ)
  moment := (5456007213 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12012 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (188414839059 / 125000000000 : ℝ)
    root := (949101207 / 125000000000 : ℝ) }

noncomputable def scalar12012 : ScalarCertificate 12012 world12012 agent12012 where
  dimensionLo := 12012
  dimensionHi := 12012
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2273950199 / 1000000000000 : ℝ)
  frameLo := (635709425461 / 1000000000000 : ℝ)
  frameHi := (188414839059 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12012]
  agentFrame_pos := by norm_num only [agent12012]
  worldRadius := (2273950199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12012]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (186271503 / 125000000000 : ℝ)
  lowerTail := (1873017837 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4238815849 / 500000000000 : ℝ)
  ledger := by
    have h : (1205001507 / 1000000000000 : ℚ) +
        (5456007213 / 500000000000000000 : ℚ) / (2273950199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (186271503 / 125000000000 : ℚ) + (1873017837 / 1000000000000 : ℚ) ≤
        (4238815849 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1205001507 / 1000000000000 : ℚ) +
        (5456007213 / 500000000000000000 : ℚ) / (2273950199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (186271503 / 125000000000 : ℚ) + (1873017837 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4238815849 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12012]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12012 :
    2 * 160 < 12012 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997277 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12012 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12013 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12013. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12013 : WorldParameters where
  hiddenCharge := (1204948917 / 1000000000000 : ℝ)
  frame := (158923477263 / 250000000000 : ℝ)
  moment := (10909635431 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12013 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1507266782699 / 1000000000000 : ℝ)
    root := (949013419 / 125000000000 : ℝ) }

noncomputable def scalar12013 : ScalarCertificate 12013 world12013 agent12013 where
  dimensionLo := 12013
  dimensionHi := 12013
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2274352099 / 1000000000000 : ℝ)
  frameLo := (158923477263 / 250000000000 : ℝ)
  frameHi := (1507266782699 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12013]
  agentFrame_pos := by norm_num only [agent12013]
  worldRadius := (2274352099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12013]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (744405177 / 500000000000 : ℝ)
  lowerTail := (467857653 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8473424543 / 1000000000000 : ℝ)
  ledger := by
    have h : (1204948917 / 1000000000000 : ℚ) +
        (10909635431 / 1000000000000000000 : ℚ) / (2274352099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (744405177 / 500000000000 : ℚ) + (467857653 / 250000000000 : ℚ) ≤
        (8473424543 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1204948917 / 1000000000000 : ℚ) +
        (10909635431 / 1000000000000000000 : ℚ) / (2274352099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (744405177 / 500000000000 : ℚ) + (467857653 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8473424543 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12013]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12013 :
    2 * 160 < 12013 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999649 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12013 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12014 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12014. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12014 : WorldParameters where
  hiddenCharge := (1204896341 / 1000000000000 : ℝ)
  frame := (158919598827 / 250000000000 : ℝ)
  moment := (10907257161 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12014 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (15072148909 / 10000000000 : ℝ)
    root := (7591405203 / 1000000000000 : ℝ) }

noncomputable def scalar12014 : ScalarCertificate 12014 world12014 agent12014 where
  dimensionLo := 12014
  dimensionHi := 12014
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2274753799 / 1000000000000 : ℝ)
  frameLo := (158919598827 / 250000000000 : ℝ)
  frameHi := (15072148909 / 10000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12014]
  agentFrame_pos := by norm_num only [agent12014]
  worldRadius := (2274753799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12014]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1487449939 / 1000000000000 : ℝ)
  lowerTail := (1869844767 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (846922127 / 100000000000 : ℝ)
  ledger := by
    have h : (1204896341 / 1000000000000 : ℚ) +
        (10907257161 / 1000000000000000000 : ℚ) / (2274753799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1487449939 / 1000000000000 : ℚ) + (1869844767 / 1000000000000 : ℚ) ≤
        (846922127 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1204896341 / 1000000000000 : ℚ) +
        (10907257161 / 1000000000000000000 : ℚ) / (2274753799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1487449939 / 1000000000000 : ℚ) + (1869844767 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((846922127 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12014]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12014 :
    2 * 160 < 12014 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998571 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12014 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12015 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12015. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12015 : WorldParameters where
  hiddenCharge := (60242189 / 50000000000 : ℝ)
  frame := (635662884227 / 1000000000000 : ℝ)
  moment := (5452439807 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12015 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753581515479 / 500000000000 : ℝ)
    root := (7590703367 / 1000000000000 : ℝ) }

noncomputable def scalar12015 : ScalarCertificate 12015 world12015 agent12015 where
  dimensionLo := 12015
  dimensionHi := 12015
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2275155699 / 1000000000000 : ℝ)
  frameLo := (635662884227 / 1000000000000 : ℝ)
  frameHi := (753581515479 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12015]
  agentFrame_pos := by norm_num only [agent12015]
  worldRadius := (2275155699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12015]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1486091227 / 1000000000000 : ℝ)
  lowerTail := (1868260803 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1693004417 / 200000000000 : ℝ)
  ledger := by
    have h : (60242189 / 50000000000 : ℚ) +
        (5452439807 / 500000000000000000 : ℚ) / (2275155699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1486091227 / 1000000000000 : ℚ) + (1868260803 / 1000000000000 : ℚ) ≤
        (1693004417 / 200000000000 : ℚ) := by norm_num only
    have hc : (((60242189 / 50000000000 : ℚ) +
        (5452439807 / 500000000000000000 : ℚ) / (2275155699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1486091227 / 1000000000000 : ℚ) + (1868260803 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1693004417 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12015]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12015 :
    2 * 160 < 12015 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998581 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12015 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12016 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12016. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12016 : WorldParameters where
  hiddenCharge := (602395617 / 500000000000 : ℝ)
  frame := (635647375809 / 1000000000000 : ℝ)
  moment := (1362812849 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12016 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (47097225089 / 31250000000 : ℝ)
    root := (1518000337 / 200000000000 : ℝ) }

noncomputable def scalar12016 : ScalarCertificate 12016 world12016 agent12016 where
  dimensionLo := 12016
  dimensionHi := 12016
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2275557499 / 1000000000000 : ℝ)
  frameLo := (635647375809 / 1000000000000 : ℝ)
  frameHi := (47097225089 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12016]
  agentFrame_pos := by norm_num only [agent12016]
  worldRadius := (2275557499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12016]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (59389353 / 40000000000 : ℝ)
  lowerTail := (46666957 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2115206677 / 250000000000 : ℝ)
  ledger := by
    have h : (602395617 / 500000000000 : ℚ) +
        (1362812849 / 125000000000000000 : ℚ) / (2275557499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (59389353 / 40000000000 : ℚ) + (46666957 / 25000000000 : ℚ) ≤
        (2115206677 / 250000000000 : ℚ) := by norm_num only
    have hc : (((602395617 / 500000000000 : ℚ) +
        (1362812849 / 125000000000000000 : ℚ) / (2275557499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (59389353 / 40000000000 : ℚ) + (46666957 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2115206677 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12016]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12016 :
    2 * 160 < 12016 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995391 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12016 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12017 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12017. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12017 : WorldParameters where
  hiddenCharge := (602369351 / 500000000000 : ℝ)
  frame := (635631870053 / 1000000000000 : ℝ)
  moment := (10900126693 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12017 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (301411880091 / 200000000000 : ℝ)
    root := (1517860063 / 200000000000 : ℝ) }

noncomputable def scalar12017 : ScalarCertificate 12017 world12017 agent12017 where
  dimensionLo := 12017
  dimensionHi := 12017
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2275959399 / 1000000000000 : ℝ)
  frameLo := (635631870053 / 1000000000000 : ℝ)
  frameHi := (301411880091 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12017]
  agentFrame_pos := by norm_num only [agent12017]
  worldRadius := (2275959399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12017]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (148337801 / 100000000000 : ℝ)
  lowerTail := (1865097499 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8456635349 / 1000000000000 : ℝ)
  ledger := by
    have h : (602369351 / 500000000000 : ℚ) +
        (10900126693 / 1000000000000000000 : ℚ) / (2275959399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (148337801 / 100000000000 : ℚ) + (1865097499 / 1000000000000 : ℚ) ≤
        (8456635349 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((602369351 / 500000000000 : ℚ) +
        (10900126693 / 1000000000000000000 : ℚ) / (2275959399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (148337801 / 100000000000 : ℚ) + (1865097499 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8456635349 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12017]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12017 :
    2 * 160 < 12017 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999889 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12017 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12018 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12018. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12018 : WorldParameters where
  hiddenCharge := (240937237 / 200000000000 : ℝ)
  frame := (635616366957 / 1000000000000 : ℝ)
  moment := (5448875659 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12018 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753503817971 / 500000000000 : ℝ)
    root := (3794299589 / 500000000000 : ℝ) }

noncomputable def scalar12018 : ScalarCertificate 12018 world12018 agent12018 where
  dimensionLo := 12018
  dimensionHi := 12018
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2276361199 / 1000000000000 : ℝ)
  frameLo := (635616366957 / 1000000000000 : ℝ)
  frameHi := (753503817971 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12018]
  agentFrame_pos := by norm_num only [agent12018]
  worldRadius := (2276361199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12018]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (296404719 / 200000000000 : ℝ)
  lowerTail := (1863518261 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2113111997 / 250000000000 : ℝ)
  ledger := by
    have h : (240937237 / 200000000000 : ℚ) +
        (5448875659 / 500000000000000000 : ℚ) / (2276361199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296404719 / 200000000000 : ℚ) + (1863518261 / 1000000000000 : ℚ) ≤
        (2113111997 / 250000000000 : ℚ) := by norm_num only
    have hc : (((240937237 / 200000000000 : ℚ) +
        (5448875659 / 500000000000000000 : ℚ) / (2276361199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296404719 / 200000000000 : ℚ) + (1863518261 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2113111997 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12018]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12018 :
    2 * 160 < 12018 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996527 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12018 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12019 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12019. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12019 : WorldParameters where
  hiddenCharge := (1204633683 / 1000000000000 : ℝ)
  frame := (635600866523 / 1000000000000 : ℝ)
  moment := (5447688333 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12019 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506955897099 / 1000000000000 : ℝ)
    root := (1517579639 / 200000000000 : ℝ) }

noncomputable def scalar12019 : ScalarCertificate 12019 world12019 agent12019 where
  dimensionLo := 12019
  dimensionHi := 12019
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2276763099 / 1000000000000 : ℝ)
  frameLo := (635600866523 / 1000000000000 : ℝ)
  frameHi := (1506955897099 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12019]
  agentFrame_pos := by norm_num only [agent12019]
  worldRadius := (2276763099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12019]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1480670629 / 1000000000000 : ℝ)
  lowerTail := (93097031 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8448264361 / 1000000000000 : ℝ)
  ledger := by
    have h : (1204633683 / 1000000000000 : ℚ) +
        (5447688333 / 500000000000000000 : ℚ) / (2276763099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1480670629 / 1000000000000 : ℚ) + (93097031 / 50000000000 : ℚ) ≤
        (8448264361 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1204633683 / 1000000000000 : ℚ) +
        (5447688333 / 500000000000000000 : ℚ) / (2276763099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1480670629 / 1000000000000 : ℚ) + (93097031 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8448264361 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12019]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12019 :
    2 * 160 < 12019 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499961 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12019 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12020 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12020. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12020 : WorldParameters where
  hiddenCharge := (301145299 / 250000000000 : ℝ)
  frame := (158896342187 / 250000000000 : ℝ)
  moment := (680812671 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12020 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (188363024511 / 125000000000 : ℝ)
    root := (1896799381 / 250000000000 : ℝ) }

noncomputable def scalar12020 : ScalarCertificate 12020 world12020 agent12020 where
  dimensionLo := 12020
  dimensionHi := 12020
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2277164899 / 1000000000000 : ℝ)
  frameLo := (158896342187 / 250000000000 : ℝ)
  frameHi := (188363024511 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12020]
  agentFrame_pos := by norm_num only [agent12020]
  worldRadius := (2277164899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12020]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1479319127 / 1000000000000 : ℝ)
  lowerTail := (465091147 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8444084861 / 1000000000000 : ℝ)
  ledger := by
    have h : (301145299 / 250000000000 : ℚ) +
        (680812671 / 62500000000000000 : ℚ) / (2277164899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1479319127 / 1000000000000 : ℚ) + (465091147 / 250000000000 : ℚ) ≤
        (8444084861 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((301145299 / 250000000000 : ℚ) +
        (680812671 / 62500000000000000 : ℚ) / (2277164899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1479319127 / 1000000000000 : ℚ) + (465091147 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8444084861 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12020]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12020 :
    2 * 160 < 12020 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995853 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12020 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12021 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12021. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12021 : WorldParameters where
  hiddenCharge := (1204528723 / 1000000000000 : ℝ)
  frame := (635569873631 / 1000000000000 : ℝ)
  moment := (1089062953 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12021 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753426260351 / 500000000000 : ℝ)
    root := (3793248503 / 500000000000 : ℝ) }

noncomputable def scalar12021 : ScalarCertificate 12021 world12021 agent12021 where
  dimensionLo := 12021
  dimensionHi := 12021
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2277566699 / 1000000000000 : ℝ)
  frameLo := (635569873631 / 1000000000000 : ℝ)
  frameHi := (753426260351 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12021]
  agentFrame_pos := by norm_num only [agent12021]
  worldRadius := (2277566699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12021]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (184746123 / 125000000000 : ℝ)
  lowerTail := (464697513 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1687981817 / 200000000000 : ℝ)
  ledger := by
    have h : (1204528723 / 1000000000000 : ℚ) +
        (1089062953 / 100000000000000000 : ℚ) / (2277566699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (184746123 / 125000000000 : ℚ) + (464697513 / 250000000000 : ℚ) ≤
        (1687981817 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1204528723 / 1000000000000 : ℚ) +
        (1089062953 / 100000000000000000 : ℚ) / (2277566699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (184746123 / 125000000000 : ℚ) + (464697513 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1687981817 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12021]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12021 :
    2 * 160 < 12021 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997707 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12021 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12022 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12022. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12022 : WorldParameters where
  hiddenCharge := (240895253 / 200000000000 : ℝ)
  frame := (317777190587 / 500000000000 : ℝ)
  moment := (2177651409 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12022 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506800877009 / 1000000000000 : ℝ)
    root := (4741123 / 625000000 : ℝ) }

noncomputable def scalar12022 : ScalarCertificate 12022 world12022 agent12022 where
  dimensionLo := 12022
  dimensionHi := 12022
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2277968499 / 1000000000000 : ℝ)
  frameLo := (317777190587 / 500000000000 : ℝ)
  frameHi := (1506800877009 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12022]
  agentFrame_pos := by norm_num only [agent12022]
  worldRadius := (2277968499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12022]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (36915509 / 25000000000 : ℝ)
  lowerTail := (58038037 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4217868683 / 500000000000 : ℝ)
  ledger := by
    have h : (240895253 / 200000000000 : ℚ) +
        (2177651409 / 200000000000000000 : ℚ) / (2277968499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (36915509 / 25000000000 : ℚ) + (58038037 / 31250000000 : ℚ) ≤
        (4217868683 / 500000000000 : ℚ) := by norm_num only
    have hc : (((240895253 / 200000000000 : ℚ) +
        (2177651409 / 200000000000000000 : ℚ) / (2277968499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (36915509 / 25000000000 : ℚ) + (58038037 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((4217868683 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12022]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12022 :
    2 * 160 < 12022 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999019 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12022 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12023 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12023. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12023 : WorldParameters where
  hiddenCharge := (602211911 / 500000000000 : ℝ)
  frame := (635538891373 / 1000000000000 : ℝ)
  moment := (10885885283 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12023 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506749264987 / 1000000000000 : ℝ)
    root := (7585096747 / 1000000000000 : ℝ) }

noncomputable def scalar12023 : ScalarCertificate 12023 world12023 agent12023 where
  dimensionLo := 12023
  dimensionHi := 12023
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2278370399 / 1000000000000 : ℝ)
  frameLo := (635538891373 / 1000000000000 : ℝ)
  frameHi := (1506749264987 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12023]
  agentFrame_pos := by norm_num only [agent12023]
  worldRadius := (2278370399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12023]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (295054641 / 200000000000 : ℝ)
  lowerTail := (927822971 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (337262777 / 40000000000 : ℝ)
  ledger := by
    have h : (602211911 / 500000000000 : ℚ) +
        (10885885283 / 1000000000000000000 : ℚ) / (2278370399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (295054641 / 200000000000 : ℚ) + (927822971 / 500000000000 : ℚ) ≤
        (337262777 / 40000000000 : ℚ) := by norm_num only
    have hc : (((602211911 / 500000000000 : ℚ) +
        (10885885283 / 1000000000000000000 : ℚ) / (2278370399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (295054641 / 200000000000 : ℚ) + (927822971 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((337262777 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12023]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12023 :
    2 * 160 < 12023 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999879 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12023 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12024 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12024. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12024 : WorldParameters where
  hiddenCharge := (1204371393 / 1000000000000 : ℝ)
  frame := (63552340423 / 100000000000 : ℝ)
  moment := (5441757121 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12024 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506697684613 / 1000000000000 : ℝ)
    root := (1516879401 / 200000000000 : ℝ) }

noncomputable def scalar12024 : ScalarCertificate 12024 world12024 agent12024 where
  dimensionLo := 12024
  dimensionHi := 12024
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2278772299 / 1000000000000 : ℝ)
  frameLo := (63552340423 / 100000000000 : ℝ)
  frameHi := (1506697684613 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12024]
  agentFrame_pos := by norm_num only [agent12024]
  worldRadius := (2278772299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12024]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (368481891 / 250000000000 : ℝ)
  lowerTail := (463519091 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8427405531 / 1000000000000 : ℝ)
  ledger := by
    have h : (1204371393 / 1000000000000 : ℚ) +
        (5441757121 / 500000000000000000 : ℚ) / (2278772299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (368481891 / 250000000000 : ℚ) + (463519091 / 250000000000 : ℚ) ≤
        (8427405531 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1204371393 / 1000000000000 : ℚ) +
        (5441757121 / 500000000000000000 : ℚ) / (2278772299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (368481891 / 250000000000 : ℚ) + (463519091 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8427405531 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12024]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12024 :
    2 * 160 < 12024 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999947 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12024 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12025 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12025. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12025 : WorldParameters where
  hiddenCharge := (1204318979 / 1000000000000 : ℝ)
  frame := (317753959871 / 500000000000 : ℝ)
  moment := (10881143923 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12025 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506646135863 / 1000000000000 : ℝ)
    root := (7583697417 / 1000000000000 : ℝ) }

noncomputable def scalar12025 : ScalarCertificate 12025 world12025 agent12025 where
  dimensionLo := 12025
  dimensionHi := 12025
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2279174099 / 1000000000000 : ℝ)
  frameLo := (317753959871 / 500000000000 : ℝ)
  frameHi := (1506646135863 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12025]
  agentFrame_pos := by norm_num only [agent12025]
  worldRadius := (2279174099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12025]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (736291609 / 500000000000 : ℝ)
  lowerTail := (185250821 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4211622703 / 500000000000 : ℝ)
  ledger := by
    have h : (1204318979 / 1000000000000 : ℚ) +
        (10881143923 / 1000000000000000000 : ℚ) / (2279174099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (736291609 / 500000000000 : ℚ) + (185250821 / 100000000000 : ℚ) ≤
        (4211622703 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1204318979 / 1000000000000 : ℚ) +
        (10881143923 / 1000000000000000000 : ℚ) / (2279174099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (736291609 / 500000000000 : ℚ) + (185250821 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4211622703 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12025]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12025 :
    2 * 160 < 12025 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999849 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12025 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12026 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12026. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12026 : WorldParameters where
  hiddenCharge := (60213329 / 50000000000 : ℝ)
  frame := (63549243791 / 100000000000 : ℝ)
  moment := (435150973 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12026 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753297309357 / 500000000000 : ℝ)
    root := (7582998139 / 1000000000000 : ℝ) }

noncomputable def scalar12026 : ScalarCertificate 12026 world12026 agent12026 where
  dimensionLo := 12026
  dimensionHi := 12026
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2279575899 / 1000000000000 : ℝ)
  frameLo := (63549243791 / 100000000000 : ℝ)
  frameHi := (753297309357 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12026]
  agentFrame_pos := by norm_num only [agent12026]
  worldRadius := (2279575899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12026]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1471240383 / 1000000000000 : ℝ)
  lowerTail := (925470859 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8419089319 / 1000000000000 : ℝ)
  ledger := by
    have h : (60213329 / 50000000000 : ℚ) +
        (435150973 / 40000000000000000 : ℚ) / (2279575899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1471240383 / 1000000000000 : ℚ) + (925470859 / 500000000000 : ℚ) ≤
        (8419089319 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((60213329 / 50000000000 : ℚ) +
        (435150973 / 40000000000000000 : ℚ) / (2279575899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1471240383 / 1000000000000 : ℚ) + (925470859 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8419089319 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12026]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12026 :
    2 * 160 < 12026 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998233 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12026 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12027 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12027. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12027 : WorldParameters where
  hiddenCharge := (301053549 / 250000000000 : ℝ)
  frame := (635476958733 / 1000000000000 : ℝ)
  moment := (1359550681 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12027 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506543133143 / 1000000000000 : ℝ)
    root := (7582299013 / 1000000000000 : ℝ) }

noncomputable def scalar12027 : ScalarCertificate 12027 world12027 agent12027 where
  dimensionLo := 12027
  dimensionHi := 12027
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2279977799 / 1000000000000 : ℝ)
  frameLo := (635476958733 / 1000000000000 : ℝ)
  frameHi := (1506543133143 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12027]
  agentFrame_pos := by norm_num only [agent12027]
  worldRadius := (2279977799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12027]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1469899009 / 1000000000000 : ℝ)
  lowerTail := (1849376843 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8414936993 / 1000000000000 : ℝ)
  ledger := by
    have h : (301053549 / 250000000000 : ℚ) +
        (1359550681 / 125000000000000000 : ℚ) / (2279977799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1469899009 / 1000000000000 : ℚ) + (1849376843 / 1000000000000 : ℚ) ≤
        (8414936993 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((301053549 / 250000000000 : ℚ) +
        (1359550681 / 125000000000000000 : ℚ) / (2279977799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1469899009 / 1000000000000 : ℚ) + (1849376843 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8414936993 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12027]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12027 :
    2 * 160 < 12027 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996377 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12027 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12028 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12028. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12028 : WorldParameters where
  hiddenCharge := (602080913 / 500000000000 : ℝ)
  frame := (635461482209 / 1000000000000 : ℝ)
  moment := (10874037291 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12028 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753245836519 / 500000000000 : ℝ)
    root := (3790800099 / 500000000000 : ℝ) }

noncomputable def scalar12028 : ScalarCertificate 12028 world12028 agent12028 where
  dimensionLo := 12028
  dimensionHi := 12028
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2280379599 / 1000000000000 : ℝ)
  frameLo := (635461482209 / 1000000000000 : ℝ)
  frameHi := (753245836519 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12028]
  agentFrame_pos := by norm_num only [agent12028]
  worldRadius := (2280379599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12028]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1468559031 / 1000000000000 : ℝ)
  lowerTail := (1847813491 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1051348579 / 125000000000 : ℝ)
  ledger := by
    have h : (602080913 / 500000000000 : ℚ) +
        (10874037291 / 1000000000000000000 : ℚ) / (2280379599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1468559031 / 1000000000000 : ℚ) + (1847813491 / 1000000000000 : ℚ) ≤
        (1051348579 / 125000000000 : ℚ) := by norm_num only
    have hc : (((602080913 / 500000000000 : ℚ) +
        (10874037291 / 1000000000000000000 : ℚ) / (2280379599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1468559031 / 1000000000000 : ℚ) + (1847813491 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1051348579 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12028]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12028 :
    2 * 160 < 12028 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999703 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12028 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12029 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12029. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12029 : WorldParameters where
  hiddenCharge := (1204109471 / 1000000000000 : ℝ)
  frame := (635446008339 / 1000000000000 : ℝ)
  moment := (2174333971 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12029 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (301288050111 / 200000000000 : ℝ)
    root := (236903173 / 31250000000 : ℝ) }

noncomputable def scalar12029 : ScalarCertificate 12029 world12029 agent12029 where
  dimensionLo := 12029
  dimensionHi := 12029
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2280781499 / 1000000000000 : ℝ)
  frameLo := (635446008339 / 1000000000000 : ℝ)
  frameHi := (301288050111 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12029]
  agentFrame_pos := by norm_num only [agent12029]
  worldRadius := (2280781499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12029]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1467220537 / 1000000000000 : ℝ)
  lowerTail := (461562947 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8406644087 / 1000000000000 : ℝ)
  ledger := by
    have h : (1204109471 / 1000000000000 : ℚ) +
        (2174333971 / 200000000000000000 : ℚ) / (2280781499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1467220537 / 1000000000000 : ℚ) + (461562947 / 250000000000 : ℚ) ≤
        (8406644087 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1204109471 / 1000000000000 : ℚ) +
        (2174333971 / 200000000000000000 : ℚ) / (2280781499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1467220537 / 1000000000000 : ℚ) + (461562947 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8406644087 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12029]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12029 :
    2 * 160 < 12029 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999637 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12029 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12030 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12030. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12030 : WorldParameters where
  hiddenCharge := (120405713 / 100000000000 : ℝ)
  frame := (635430537121 / 1000000000000 : ℝ)
  moment := (5434651569 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12030 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506388853491 / 1000000000000 : ℝ)
    root := (7580203183 / 1000000000000 : ℝ) }

noncomputable def scalar12030 : ScalarCertificate 12030 world12030 agent12030 where
  dimensionLo := 12030
  dimensionHi := 12030
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2281183299 / 1000000000000 : ℝ)
  frameLo := (635430537121 / 1000000000000 : ℝ)
  frameHi := (1506388853491 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12030]
  agentFrame_pos := by norm_num only [agent12030]
  worldRadius := (2281183299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12030]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (293176687 / 200000000000 : ℝ)
  lowerTail := (922345803 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8402503499 / 1000000000000 : ℝ)
  ledger := by
    have h : (120405713 / 100000000000 : ℚ) +
        (5434651569 / 500000000000000000 : ℚ) / (2281183299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (293176687 / 200000000000 : ℚ) + (922345803 / 500000000000 : ℚ) ≤
        (8402503499 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((120405713 / 100000000000 : ℚ) +
        (5434651569 / 500000000000000000 : ℚ) / (2281183299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (293176687 / 200000000000 : ℚ) + (922345803 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8402503499 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12030]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12030 :
    2 * 160 < 12030 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998163 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12030 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12031 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12031. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12031 : WorldParameters where
  hiddenCharge := (301001201 / 250000000000 : ℝ)
  frame := (127083013711 / 200000000000 : ℝ)
  moment := (5433468571 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12031 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (301267497583 / 200000000000 : ℝ)
    root := (7579504983 / 1000000000000 : ℝ) }

noncomputable def scalar12031 : ScalarCertificate 12031 world12031 agent12031 where
  dimensionLo := 12031
  dimensionHi := 12031
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2281585099 / 1000000000000 : ℝ)
  frameLo := (127083013711 / 200000000000 : ℝ)
  frameHi := (301267497583 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12031]
  agentFrame_pos := by norm_num only [agent12031]
  worldRadius := (2281585099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12031]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (732273851 / 500000000000 : ℝ)
  lowerTail := (368626587 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4199183327 / 500000000000 : ℝ)
  ledger := by
    have h : (301001201 / 250000000000 : ℚ) +
        (5433468571 / 500000000000000000 : ℚ) / (2281585099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (732273851 / 500000000000 : ℚ) + (368626587 / 200000000000 : ℚ) ≤
        (4199183327 / 500000000000 : ℚ) := by norm_num only
    have hc : (((301001201 / 250000000000 : ℚ) +
        (5433468571 / 500000000000000000 : ℚ) / (2281585099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (732273851 / 500000000000 : ℚ) + (368626587 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4199183327 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12031]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12031 :
    2 * 160 < 12031 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999573 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12031 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12032 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12032. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12032 : WorldParameters where
  hiddenCharge := (1203952493 / 1000000000000 : ℝ)
  frame := (7942495033 / 12500000000 : ℝ)
  moment := (2172914373 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12032 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753143076901 / 500000000000 : ℝ)
    root := (1894701773 / 250000000000 : ℝ) }

noncomputable def scalar12032 : ScalarCertificate 12032 world12032 agent12032 where
  dimensionLo := 12032
  dimensionHi := 12032
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2281986899 / 1000000000000 : ℝ)
  frameLo := (7942495033 / 12500000000 : ℝ)
  frameHi := (753143076901 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12032]
  agentFrame_pos := by norm_num only [agent12032]
  worldRadius := (2281986899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12032]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1463213469 / 1000000000000 : ℝ)
  lowerTail := (1841575913 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (419711691 / 50000000000 : ℝ)
  ledger := by
    have h : (1203952493 / 1000000000000 : ℚ) +
        (2172914373 / 200000000000000000 : ℚ) / (2281986899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1463213469 / 1000000000000 : ℚ) + (1841575913 / 1000000000000 : ℚ) ≤
        (419711691 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1203952493 / 1000000000000 : ℚ) +
        (2172914373 / 200000000000000000 : ℚ) / (2281986899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1463213469 / 1000000000000 : ℚ) + (1841575913 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((419711691 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12032]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12032 :
    2 * 160 < 12032 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999289 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12032 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12033 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12033. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12033 : WorldParameters where
  hiddenCharge := (1203900197 / 1000000000000 : ℝ)
  frame := (1016614623 / 1600000000 : ℝ)
  moment := (10862207307 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12033 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (150623485113 / 100000000000 : ℝ)
    root := (3789054677 / 500000000000 : ℝ) }

noncomputable def scalar12033 : ScalarCertificate 12033 world12033 agent12033 where
  dimensionLo := 12033
  dimensionHi := 12033
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2282388699 / 1000000000000 : ℝ)
  frameLo := (1016614623 / 1600000000 : ℝ)
  frameHi := (150623485113 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12033]
  agentFrame_pos := by norm_num only [agent12033]
  worldRadius := (2282388699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12033]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (730940301 / 500000000000 : ℝ)
  lowerTail := (1840020399 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8390104721 / 1000000000000 : ℝ)
  ledger := by
    have h : (1203900197 / 1000000000000 : ℚ) +
        (10862207307 / 1000000000000000000 : ℚ) / (2282388699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (730940301 / 500000000000 : ℚ) + (1840020399 / 1000000000000 : ℚ) ≤
        (8390104721 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1203900197 / 1000000000000 : ℚ) +
        (10862207307 / 1000000000000000000 : ℚ) / (2282388699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (730940301 / 500000000000 : ℚ) + (1840020399 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8390104721 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12033]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12033 :
    2 * 160 < 12033 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999281 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12033 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12009 :
    (1205159366724177735973 / 1000000000000000000000000 : ℝ) ≤ world12009.hiddenCharge ∧
    (127151198135345333134803 / 200000000000000000000000 : ℝ) ≤ world12009.frame ∧
    (10919155761526131 / 1000000000000000000000000 : ℝ) ≤ world12009.moment ∧
    (753737319224626134980531 / 500000000000000000000000 : ℝ) ≤ agent12009.frame ∧
    (1898729512400373061731 / 250000000000000000000000 : ℝ) ≤ agent12009.root ∧
    scalar12009.worldRadius ≤ (2272744599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1323134700294678369939 / 1000000000000000000000000 : ℝ) ≤ agent12009.charge ∧
    (1494265758170865833427 / 1000000000000000000000000 : ℝ) ≤ scalar12009.upperTail ∧
    (1877789066689274867501 / 1000000000000000000000000 : ℝ) ≤ scalar12009.lowerTail ∧
    scalar12009.totalBudget ≤ (8490276511191500906699 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12009, agent12009, scalar12009] <;> simp only [true_and]

theorem source_rounding12010 :
    (1205106731943650572953 / 1000000000000000000000000 : ℝ) ≤ world12010.hiddenCharge ∧
    (317870233135904770650621 / 500000000000000000000000 : ℝ) ≤ world12010.frame ∧
    (10916774590993921 / 1000000000000000000000000 : ℝ) ≤ world12010.moment ∧
    (23553478993144950091539 / 15625000000000000000000 : ℝ) ≤ agent12010.frame ∧
    (7594215043658370915887 / 1000000000000000000000000 : ℝ) ≤ agent12010.root ∧
    scalar12010.worldRadius ≤ (2273146499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1322756897521042758069 / 1000000000000000000000000 : ℝ) ≤ agent12010.charge ∧
    (1492899868005314818891 / 1000000000000000000000000 : ℝ) ≤ scalar12010.upperTail ∧
    (1876197235647847510241 / 1000000000000000000000000 : ℝ) ≤ scalar12010.lowerTail ∧
    scalar12010.totalBudget ≤ (8486057901787654415853 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12010, agent12010, scalar12010] <;> simp only [true_and]

theorem source_rounding12011 :
    (602527055963995625767 / 500000000000000000000000 : ℝ) ≤ world12011.hiddenCharge ∧
    (158931236133289981432527 / 250000000000000000000000 : ℝ) ≤ world12011.frame ∧
    (2728598536465221 / 250000000000000000000000 : ℝ) ≤ world12011.moment ∧
    (301474133610588119171913 / 200000000000000000000000 : ℝ) ≤ agent12011.frame ∧
    (189837804832590368283 / 25000000000000000000000 : ℝ) ≤ agent12011.root ∧
    scalar12011.worldRadius ≤ (2273548299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (330594894168977814843 / 250000000000000000000000 : ℝ) ≤ agent12011.charge ∧
    (298307026812629802817 / 200000000000000000000000 : ℝ) ≤ scalar12011.upperTail ∧
    (937303320951404379491 / 500000000000000000000000 : ℝ) ≤ scalar12011.lowerTail ∧
    scalar12011.totalBudget ≤ (8481842748831604196253 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12011, agent12011, scalar12011] <;> simp only [true_and]

theorem source_rounding12012 :
    (301250376667944945217 / 250000000000000000000000 : ℝ) ≤ world12012.hiddenCharge ∧
    (317854712730024036316693 / 500000000000000000000000 : ℝ) ≤ world12012.frame ∧
    (341000450807607 / 31250000000000000000000 : ℝ) ≤ world12012.moment ∧
    (753659356235584118102887 / 500000000000000000000000 : ℝ) ≤ agent12012.frame ∧
    (759280965554838835899 / 100000000000000000000000 : ℝ) ≤ agent12012.root ∧
    scalar12012.worldRadius ≤ (2273950199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (264400547404925260831 / 200000000000000000000000 : ℝ) ≤ agent12012.charge ∧
    (745086011611605136613 / 500000000000000000000000 : ℝ) ≤ scalar12012.upperTail ∧
    (468254459139339562351 / 250000000000000000000000 : ℝ) ≤ scalar12012.lowerTail ∧
    scalar12012.totalBudget ≤ (1695526339638702130051 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12012, agent12012, scalar12012] <;> simp only [true_and]

theorem source_rounding12013 :
    (150618614521200018089 / 125000000000000000000000 : ℝ) ≤ world12013.hiddenCharge ∧
    (6356939090517444630017 / 10000000000000000000000 : ℝ) ≤ world12013.frame ∧
    (340926107208067 / 31250000000000000000000 : ℝ) ≤ world12013.moment ∧
    (376816695674646832727951 / 250000000000000000000000 : ℝ) ≤ agent12013.frame ∧
    (3796053675819038965933 / 500000000000000000000000 : ℝ) ≤ agent12013.root ∧
    scalar12013.worldRadius ≤ (2274352099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (132162637783381794219 / 100000000000000000000000 : ℝ) ≤ agent12013.charge ∧
    (1488810353475060342533 / 1000000000000000000000000 : ℝ) ≤ scalar12013.upperTail ∧
    (374286122357029571843 / 200000000000000000000000 : ℝ) ≤ scalar12013.lowerTail ∧
    scalar12013.totalBudget ≤ (8473424543439668982817 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12013, agent12013, scalar12013] <;> simp only [true_and]

theorem source_rounding12014 :
    (37653010638001169911 / 31250000000000000000000 : ℝ) ≤ world12014.hiddenCharge ∧
    (635678395307519929422809 / 1000000000000000000000000 : ℝ) ≤ world12014.frame ∧
    (10907257160021727 / 1000000000000000000000000 : ℝ) ≤ world12014.moment ∧
    (1507214890899848153082873 / 1000000000000000000000000 : ℝ) ≤ agent12014.frame ∧
    (1518281040576876648053 / 200000000000000000000000 : ℝ) ≤ agent12014.root ∧
    scalar12014.worldRadius ≤ (2274753799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1321250498371401333537 / 1000000000000000000000000 : ℝ) ≤ agent12014.charge ∧
    (1487449938425569380199 / 1000000000000000000000000 : ℝ) ≤ scalar12014.upperTail ∧
    (934922383296904566273 / 500000000000000000000000 : ℝ) ≤ scalar12014.lowerTail ∧
    scalar12014.totalBudget ≤ (423461063518136346981 / 50000000000000000000000 : ℝ) := by
  norm_num only [world12014, agent12014, scalar12014] <;> simp only [true_and]

theorem source_rounding12015 :
    (1204843779405679293479 / 1000000000000000000000000 : ℝ) ≤ world12015.hiddenCharge ∧
    (635662884226645492335137 / 1000000000000000000000000 : ℝ) ≤ world12015.frame ∧
    (5452439806825497 / 500000000000000000000000 : ℝ) ≤ world12015.moment ∧
    (1507163030957344567132807 / 1000000000000000000000000 : ℝ) ≤ agent12015.frame ∧
    (7590703366199702391733 / 1000000000000000000000000 : ℝ) ≤ agent12015.root ∧
    scalar12015.worldRadius ≤ (2275155699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (165109387238321780583 / 125000000000000000000000 : ℝ) ≤ agent12015.charge ∧
    (743045613283799947593 / 500000000000000000000000 : ℝ) ≤ scalar12015.upperTail ∧
    (373652160596818109749 / 200000000000000000000000 : ℝ) ≤ scalar12015.lowerTail ∧
    scalar12015.totalBudget ≤ (8465022085388122587041 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12015, agent12015, scalar12015] <;> simp only [true_and]

theorem source_rounding12016 :
    (1204791233133118745123 / 1000000000000000000000000 : ℝ) ≤ world12016.hiddenCharge ∧
    (317823687904196260463173 / 500000000000000000000000 : ℝ) ≤ world12016.frame ∧
    (545125139563151 / 50000000000000000000000 : ℝ) ≤ world12016.moment ∧
    (376777800711923122533543 / 250000000000000000000000 : ℝ) ≤ agent12016.frame ∧
    (7590001684384661513431 / 1000000000000000000000000 : ℝ) ≤ agent12016.root ∧
    scalar12016.worldRadius ≤ (2275557499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (26410003514196290997 / 20000000000000000000000 : ℝ) ≤ agent12016.charge ∧
    (1484733824927280311497 / 1000000000000000000000000 : ℝ) ≤ scalar12016.upperTail ∧
    (933339139737925588361 / 500000000000000000000000 : ℝ) ≤ scalar12016.lowerTail ∧
    scalar12016.totalBudget ≤ (1692165341714606124073 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12016, agent12016, scalar12016] <;> simp only [true_and]

theorem source_rounding12017 :
    (60236935079647353673 / 50000000000000000000000 : ℝ) ≤ world12017.hiddenCharge ∧
    (317815935026016263414219 / 500000000000000000000000 : ℝ) ≤ world12017.frame ∧
    (10900126692574847 / 1000000000000000000000000 : ℝ) ≤ world12017.moment ∧
    (376764850113701133230849 / 250000000000000000000000 : ℝ) ≤ agent12017.frame ∧
    (7589300314285790524239 / 1000000000000000000000000 : ℝ) ≤ agent12017.root ∧
    scalar12017.worldRadius ≤ (2275959399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1320125731052877737877 / 1000000000000000000000000 : ℝ) ≤ agent12017.charge ∧
    (370844502390722839959 / 250000000000000000000000 : ℝ) ≤ scalar12017.upperTail ∧
    (1865097498869883346089 / 1000000000000000000000000 : ℝ) ≤ scalar12017.lowerTail ∧
    scalar12017.totalBudget ≤ (8456635349062260773861 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12017, agent12017, scalar12017] <;> simp only [true_and]

theorem source_rounding12018 :
    (150585773097469940761 / 125000000000000000000000 : ℝ) ≤ world12018.hiddenCharge ∧
    (635616366956837547596197 / 1000000000000000000000000 : ℝ) ≤ world12018.frame ∧
    (10897751317303709 / 1000000000000000000000000 : ℝ) ≤ world12018.moment ∧
    (75350381797055581365347 / 50000000000000000000000 : ℝ) ≤ agent12018.frame ∧
    (3794299588616038495103 / 500000000000000000000000 : ℝ) ≤ agent12018.root ∧
    scalar12018.worldRadius ≤ (2276361199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (659875881604397211987 / 500000000000000000000000 : ℝ) ≤ agent12018.charge ∧
    (741011797162763176569 / 500000000000000000000000 : ℝ) ≤ scalar12018.upperTail ∧
    (1863518260401332359341 / 1000000000000000000000000 : ℝ) ≤ scalar12018.lowerTail ∧
    scalar12018.totalBudget ≤ (8452447988436308364939 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12018, agent12018, scalar12018] <;> simp only [true_and]

theorem source_rounding12019 :
    (602316841344077655909 / 500000000000000000000000 : ℝ) ≤ world12019.hiddenCharge ∧
    (635600866522079588133027 / 1000000000000000000000000 : ℝ) ≤ world12019.frame ∧
    (10895376665167041 / 1000000000000000000000000 : ℝ) ≤ world12019.moment ∧
    (1506955897098143357830667 / 1000000000000000000000000 : ℝ) ≤ agent12019.frame ∧
    (948487274327338424197 / 125000000000000000000000 : ℝ) ≤ agent12019.root ∧
    scalar12019.worldRadius ≤ (2276763099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1319378271451867867019 / 1000000000000000000000000 : ℝ) ≤ agent12019.charge ∧
    (296134125742911681587 / 200000000000000000000000 : ℝ) ≤ scalar12019.upperTail ∧
    (930970309869929980441 / 500000000000000000000000 : ℝ) ≤ scalar12019.lowerTail ∧
    scalar12019.totalBudget ≤ (168965287234145313593 / 20000000000000000000000 : ℝ) := by
  norm_num only [world12019, agent12019, scalar12019] <;> simp only [true_and]

theorem source_rounding12020 :
    (1204581195312734744757 / 1000000000000000000000000 : ℝ) ≤ world12020.hiddenCharge ∧
    (317792684373515549601997 / 500000000000000000000000 : ℝ) ≤ world12020.frame ∧
    (10893002735882353 / 1000000000000000000000000 : ℝ) ≤ world12020.moment ∧
    (1506904196087222955016083 / 1000000000000000000000000 : ℝ) ≤ agent12020.frame ∧
    (1896799380798403046553 / 250000000000000000000000 : ℝ) ≤ agent12020.root ∧
    scalar12020.worldRadius ≤ (2277164899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1319005255057671491989 / 1000000000000000000000000 : ℝ) ≤ agent12020.charge ∧
    (1479319126030330194513 / 1000000000000000000000000 : ℝ) ≤ scalar12020.upperTail ∧
    (74414583518087229321 / 40000000000000000000000 : ℝ) ≤ scalar12020.lowerTail ∧
    scalar12020.totalBudget ≤ (2111021215296935299577 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12020, agent12020, scalar12020] <;> simp only [true_and]

theorem source_rounding12021 :
    (1204528722648100671007 / 1000000000000000000000000 : ℝ) ≤ world12021.hiddenCharge ∧
    (158892468407741206414781 / 250000000000000000000000 : ℝ) ≤ world12021.frame ∧
    (10890629529167299 / 1000000000000000000000000 : ℝ) ≤ world12021.moment ∧
    (150685252070110347594723 / 100000000000000000000000 : ℝ) ≤ agent12021.frame ∧
    (7586497005923515057853 / 1000000000000000000000000 : ℝ) ≤ agent12021.root ∧
    scalar12021.worldRadius ≤ (2277566699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1318632713303046417621 / 1000000000000000000000000 : ℝ) ≤ agent12021.charge ∧
    (147796898384956803397 / 100000000000000000000000 : ℝ) ≤ scalar12021.upperTail ∧
    (929395025649266492887 / 500000000000000000000000 : ℝ) ≤ scalar12021.lowerTail ∧
    scalar12021.totalBudget ≤ (4219954542737640922819 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12021, agent12021, scalar12021] <;> simp only [true_and]

theorem source_rounding12022 :
    (602238132344428521531 / 500000000000000000000000 : ℝ) ≤ world12022.hiddenCharge ∧
    (317777190586576838349739 / 500000000000000000000000 : ℝ) ≤ world12022.frame ∧
    (10888257044739609 / 1000000000000000000000000 : ℝ) ≤ world12022.moment ∧
    (1506800877008724902141247 / 1000000000000000000000000 : ℝ) ≤ agent12022.frame ∧
    (7585796799490589673193 / 1000000000000000000000000 : ℝ) ≤ agent12022.root ∧
    scalar12022.worldRadius ≤ (2277968499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (5149455646351949177 / 3906250000000000000000 : ℝ) ≤ agent12022.charge ∧
    (738310179823768887667 / 500000000000000000000000 : ℝ) ≤ scalar12022.upperTail ∧
    (1857217183587082474197 / 1000000000000000000000000 : ℝ) ≤ scalar12022.lowerTail ∧
    scalar12022.totalBudget ≤ (8435737366390955669203 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12022, agent12022, scalar12022] <;> simp only [true_and]

theorem source_rounding12023 :
    (1204423821429614615271 / 1000000000000000000000000 : ℝ) ≤ world12023.hiddenCharge ∧
    (19860590355402215391619 / 31250000000000000000000 : ℝ) ≤ world12023.frame ∧
    (2721471320579331 / 250000000000000000000000 : ℝ) ≤ world12023.moment ∧
    (188343658123363312214183 / 125000000000000000000000 : ℝ) ≤ agent12023.frame ∧
    (7585096746927965325751 / 1000000000000000000000000 : ℝ) ≤ agent12023.root ∧
    scalar12023.worldRadius ≤ (2278370399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1317889050826198317203 / 1000000000000000000000000 : ℝ) ≤ agent12023.charge ∧
    (1475273204676439558033 / 1000000000000000000000000 : ℝ) ≤ scalar12023.upperTail ∧
    (1855645941069503776563 / 1000000000000000000000000 : ℝ) ≤ scalar12023.lowerTail ∧
    scalar12023.totalBudget ≤ (8431569425892309385021 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12023, agent12023, scalar12023] <;> simp only [true_and]

theorem source_rounding12024 :
    (37636606027030655409 / 31250000000000000000000 : ℝ) ≤ world12024.hiddenCharge ∧
    (635523404229390041351577 / 1000000000000000000000000 : ℝ) ≤ world12024.frame ∧
    (2720878560404599 / 250000000000000000000000 : ℝ) ≤ world12024.moment ∧
    (376674421153124126954047 / 250000000000000000000000 : ℝ) ≤ agent12024.frame ∧
    (758439700485210341509 / 100000000000000000000000 : ℝ) ≤ agent12024.root ∧
    scalar12024.worldRadius ≤ (2278772299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (658758964331986909739 / 500000000000000000000000 : ℝ) ≤ agent12024.charge ∧
    (184240945471466151497 / 125000000000000000000000 : ℝ) ≤ scalar12024.upperTail ∧
    (927038181692619188139 / 500000000000000000000000 : ℝ) ≤ scalar12024.lowerTail ∧
    scalar12024.totalBudget ≤ (8427405531356782290473 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12024, agent12024, scalar12024] <;> simp only [true_and]

theorem source_rounding12025 :
    (1204318978989569077383 / 1000000000000000000000000 : ℝ) ≤ world12025.hiddenCharge ∧
    (317753959870992387994871 / 500000000000000000000000 : ℝ) ≤ world12025.frame ∧
    (435245756894441 / 40000000000000000000000 : ℝ) ≤ world12025.moment ∧
    (1506646135862372121588687 / 1000000000000000000000000 : ℝ) ≤ agent12025.frame ∧
    (3791848708181246267779 / 500000000000000000000000 : ℝ) ≤ agent12025.root ∧
    scalar12025.worldRadius ≤ (2279174099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1317147278261312770831 / 1000000000000000000000000 : ℝ) ≤ agent12025.charge ∧
    (58903328714239256421 / 40000000000000000000000 : ℝ) ≤ scalar12025.upperTail ∧
    (185250820975501232483 / 100000000000000000000000 : ℝ) ≤ scalar12025.lowerTail ∧
    scalar12025.totalBudget ≤ (263226418946318567143 / 31250000000000000000000 : ℝ) := by
  norm_num only [world12025, agent12025, scalar12025] <;> simp only [true_and]

theorem source_rounding12026 :
    (301066644949498958671 / 250000000000000000000000 : ℝ) ≤ world12026.hiddenCharge ∧
    (317746218954964638933199 / 500000000000000000000000 : ℝ) ≤ world12026.frame ∧
    (10878774324263611 / 1000000000000000000000000 : ℝ) ≤ world12026.moment ∧
    (188324327339179929394321 / 125000000000000000000000 : ℝ) ≤ agent12026.frame ∧
    (947874767251240787919 / 125000000000000000000000 : ℝ) ≤ agent12026.root ∧
    scalar12026.worldRadius ≤ (2279575899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (329194274725339464027 / 250000000000000000000000 : ℝ) ≤ agent12026.charge ∧
    (367810095593341790493 / 250000000000000000000000 : ℝ) ≤ scalar12026.upperTail ∧
    (370188343428504294577 / 200000000000000000000000 : ℝ) ≤ scalar12026.lowerTail ∧
    scalar12026.totalBudget ≤ (8419089319536105270871 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12026, agent12026, scalar12026] <;> simp only [true_and]

theorem source_rounding12027 :
    (1204214195284877830349 / 1000000000000000000000000 : ℝ) ≤ world12027.hiddenCharge ∧
    (127095391746499557056489 / 200000000000000000000000 : ℝ) ≤ world12027.frame ∧
    (2719101361761143 / 250000000000000000000000 : ℝ) ≤ world12027.moment ∧
    (1506543133142633414666511 / 1000000000000000000000000 : ℝ) ≤ agent12027.frame ∧
    (7582299012960206356523 / 1000000000000000000000000 : ℝ) ≤ agent12027.root ∧
    scalar12027.worldRadius ≤ (2279977799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (82275461866781545569 / 62500000000000000000000 : ℝ) ≤ agent12027.charge ∧
    (1469899008845246421403 / 1000000000000000000000000 : ℝ) ≤ scalar12027.upperTail ∧
    (1849376842052638645113 / 1000000000000000000000000 : ℝ) ≤ scalar12027.lowerTail ∧
    scalar12027.totalBudget ≤ (8414936993155430782889 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12027, agent12027, scalar12027] <;> simp only [true_and]

theorem source_rounding12028 :
    (1204161825444835593729 / 1000000000000000000000000 : ℝ) ≤ world12028.hiddenCharge ∧
    (317730741104482444273007 / 500000000000000000000000 : ℝ) ≤ world12028.frame ∧
    (434961491616901 / 40000000000000000000000 : ℝ) ≤ world12028.moment ∧
    (602596669214952711069 / 400000000000000000000 : ℝ) ≤ agent12028.frame ∧
    (3790800098849251484709 / 500000000000000000000000 : ℝ) ≤ agent12028.root ∧
    scalar12028.worldRadius ≤ (2280379599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1316038150448399576519 / 1000000000000000000000000 : ℝ) ≤ agent12028.charge ∧
    (367139757534297501921 / 250000000000000000000000 : ℝ) ≤ scalar12028.upperTail ∧
    (923906745351947286141 / 500000000000000000000000 : ℝ) ≤ scalar12028.lowerTail ∧
    scalar12028.totalBudget ≤ (8410788632984811419447 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12028, agent12028, scalar12028] <;> simp only [true_and]

theorem source_rounding12029 :
    (602054735136245377359 / 500000000000000000000000 : ℝ) ≤ world12029.hiddenCharge ∧
    (635446008338605442214597 / 1000000000000000000000000 : ℝ) ≤ world12029.frame ∧
    (2717917463529041 / 250000000000000000000000 : ℝ) ≤ world12029.moment ∧
    (188305031319254844956541 / 125000000000000000000000 : ℝ) ≤ agent12029.frame ∧
    (7580901535456884612429 / 1000000000000000000000000 : ℝ) ≤ agent12029.root ∧
    scalar12029.worldRadius ≤ (2280781499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (657834689963968343517 / 500000000000000000000000 : ℝ) ≤ agent12029.charge ∧
    (1467220536473931124747 / 1000000000000000000000000 : ℝ) ≤ scalar12029.upperTail ∧
    (923125893953199259401 / 500000000000000000000000 : ℝ) ≤ scalar12029.lowerTail ∧
    scalar12029.totalBudget ≤ (131353813869898509559 / 15625000000000000000000 : ℝ) := by
  norm_num only [world12029, agent12029, scalar12029] <;> simp only [true_and]

theorem source_rounding12030 :
    (1204057129762467464227 / 1000000000000000000000000 : ℝ) ≤ world12030.hiddenCharge ∧
    (9928602142510853335389 / 15625000000000000000000 : ℝ) ≤ world12030.frame ∧
    (10869303137844323 / 1000000000000000000000000 : ℝ) ≤ world12030.moment ∧
    (376597213372710676803851 / 250000000000000000000000 : ℝ) ≤ agent12030.frame ∧
    (3790101591327471309689 / 500000000000000000000000 : ℝ) ≤ agent12030.root ∧
    scalar12030.worldRadius ≤ (2281183299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (328825269398814006381 / 250000000000000000000000 : ℝ) ≤ agent12030.charge ∧
    (732941717030541564917 / 500000000000000000000000 : ℝ) ≤ scalar12030.upperTail ∧
    (922345802553442334361 / 500000000000000000000000 : ℝ) ≤ scalar12030.lowerTail ∧
    scalar12030.totalBudget ≤ (42012517495452749283 / 5000000000000000000000 : ℝ) := by
  norm_num only [world12030, agent12030, scalar12030] <;> simp only [true_and]

theorem source_rounding12031 :
    (1204004803909395228377 / 1000000000000000000000000 : ℝ) ≤ world12031.hiddenCharge ∧
    (635415068554507798214361 / 1000000000000000000000000 : ℝ) ≤ world12031.frame ∧
    (5433468570663043 / 500000000000000000000000 : ℝ) ≤ world12031.moment ∧
    (188292185989297402945343 / 125000000000000000000000 : ℝ) ≤ agent12031.frame ∧
    (3789752491295483063669 / 500000000000000000000000 : ℝ) ≤ agent12031.root ∧
    scalar12031.worldRadius ≤ (2281585099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1314933242739740812379 / 1000000000000000000000000 : ℝ) ≤ agent12031.charge ∧
    (366136925394715161671 / 250000000000000000000000 : ℝ) ≤ scalar12031.upperTail ∧
    (1843132934094981185923 / 1000000000000000000000000 : ℝ) ≤ scalar12031.lowerTail ∧
    scalar12031.totalBudget ≤ (4199183327430707701583 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12031, agent12031, scalar12031] <;> simp only [true_and]

theorem source_rounding12032 :
    (1203952492707901814239 / 1000000000000000000000000 : ℝ) ≤ world12032.hiddenCharge ∧
    (158849900659830161948807 / 250000000000000000000000 : ℝ) ≤ world12032.frame ∧
    (10864571864280503 / 1000000000000000000000000 : ℝ) ≤ world12032.moment ∧
    (753143076900863258280641 / 500000000000000000000000 : ℝ) ≤ agent12032.frame ∧
    (1894701772904752972693 / 250000000000000000000000 : ℝ) ≤ agent12032.root ∧
    scalar12032.worldRadius ≤ (2281986899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (657282937326007553961 / 500000000000000000000000 : ℝ) ≤ agent12032.charge ∧
    (1463213468336073018921 / 1000000000000000000000000 : ℝ) ≤ scalar12032.upperTail ∧
    (57549247260893227621 / 31250000000000000000000 : ℝ) ≤ scalar12032.lowerTail ∧
    scalar12032.totalBudget ≤ (4197116910165189698269 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12032, agent12032, scalar12032] <;> simp only [true_and]

theorem source_rounding12033 :
    (1203900196152620341051 / 1000000000000000000000000 : ℝ) ≤ world12033.hiddenCharge ∧
    (317692069687204569425383 / 500000000000000000000000 : ℝ) ≤ world12033.frame ∧
    (17379531690283 / 1600000000000000000000 : ℝ) ≤ world12033.moment ∧
    (1506234851129991443796599 / 1000000000000000000000000 : ℝ) ≤ agent12033.frame ∧
    (947263669137942949177 / 125000000000000000000000 : ℝ) ≤ agent12033.root ∧
    scalar12033.worldRadius ≤ (2282388699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1314198972623941401927 / 1000000000000000000000000 : ℝ) ≤ agent12033.charge ∧
    (73094030077786219341 / 50000000000000000000000 : ℝ) ≤ scalar12033.upperTail ∧
    (1840020398731942349081 / 1000000000000000000000000 : ℝ) ≤ scalar12033.lowerTail ∧
    scalar12033.totalBudget ≤ (8390104721144272458073 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12033, agent12033, scalar12033] <;> simp only [true_and]

noncomputable def paperAgent12009 : AgentParameters :=
  { agent12009 with charge := (82695919 / 62500000000 : ℝ) }

theorem agent_is_repriced12009 : agent12009 =
    BstLean.Part265.agentRepriced 12009 world12009 paperAgent12009 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12009, agent12009]

noncomputable def paperAgent12010 : AgentParameters :=
  { agent12010 with charge := (1322756901 / 1000000000000 : ℝ) }

theorem agent_is_repriced12010 : agent12010 =
    BstLean.Part265.agentRepriced 12010 world12010 paperAgent12010 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12010, agent12010]

noncomputable def paperAgent12011 : AgentParameters :=
  { agent12011 with charge := (66118979 / 50000000000 : ℝ) }

theorem agent_is_repriced12011 : agent12011 =
    BstLean.Part265.agentRepriced 12011 world12011 paperAgent12011 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12011, agent12011]

noncomputable def paperAgent12012 : AgentParameters :=
  { agent12012 with charge := (66100137 / 50000000000 : ℝ) }

theorem agent_is_repriced12012 : agent12012 =
    BstLean.Part265.agentRepriced 12012 world12012 paperAgent12012 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12012, agent12012]

noncomputable def paperAgent12013 : AgentParameters :=
  { agent12013 with charge := (660813191 / 500000000000 : ℝ) }

theorem agent_is_repriced12013 : agent12013 =
    BstLean.Part265.agentRepriced 12013 world12013 paperAgent12013 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12013, agent12013]

noncomputable def paperAgent12014 : AgentParameters :=
  { agent12014 with charge := (660625251 / 500000000000 : ℝ) }

theorem agent_is_repriced12014 : agent12014 =
    BstLean.Part265.agentRepriced 12014 world12014 paperAgent12014 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12014, agent12014]

noncomputable def paperAgent12015 : AgentParameters :=
  { agent12015 with charge := (1320875101 / 1000000000000 : ℝ) }

theorem agent_is_repriced12015 : agent12015 =
    BstLean.Part265.agentRepriced 12015 world12015 paperAgent12015 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12015, agent12015]

noncomputable def paperAgent12016 : AgentParameters :=
  { agent12016 with charge := (1320500179 / 1000000000000 : ℝ) }

theorem agent_is_repriced12016 : agent12016 =
    BstLean.Part265.agentRepriced 12016 world12016 paperAgent12016 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12016, agent12016]

noncomputable def paperAgent12017 : AgentParameters :=
  { agent12017 with charge := (660062867 / 500000000000 : ℝ) }

theorem agent_is_repriced12017 : agent12017 =
    BstLean.Part265.agentRepriced 12017 world12017 paperAgent12017 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12017, agent12017]

noncomputable def paperAgent12018 : AgentParameters :=
  { agent12018 with charge := (659875883 / 500000000000 : ℝ) }

theorem agent_is_repriced12018 : agent12018 =
    BstLean.Part265.agentRepriced 12018 world12018 paperAgent12018 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12018, agent12018]

noncomputable def paperAgent12019 : AgentParameters :=
  { agent12019 with charge := (659689137 / 500000000000 : ℝ) }

theorem agent_is_repriced12019 : agent12019 =
    BstLean.Part265.agentRepriced 12019 world12019 paperAgent12019 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12019, agent12019]

noncomputable def paperAgent12020 : AgentParameters :=
  { agent12020 with charge := (659502629 / 500000000000 : ℝ) }

theorem agent_is_repriced12020 : agent12020 =
    BstLean.Part265.agentRepriced 12020 world12020 paperAgent12020 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12020, agent12020]

noncomputable def paperAgent12021 : AgentParameters :=
  { agent12021 with charge := (1318632717 / 1000000000000 : ℝ) }

theorem agent_is_repriced12021 : agent12021 =
    BstLean.Part265.agentRepriced 12021 world12021 paperAgent12021 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12021, agent12021]

noncomputable def paperAgent12022 : AgentParameters :=
  { agent12022 with charge := (1318260649 / 1000000000000 : ℝ) }

theorem agent_is_repriced12022 : agent12022 =
    BstLean.Part265.agentRepriced 12022 world12022 paperAgent12022 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12022, agent12022]

noncomputable def paperAgent12023 : AgentParameters :=
  { agent12023 with charge := (658944527 / 500000000000 : ℝ) }

theorem agent_is_repriced12023 : agent12023 =
    BstLean.Part265.agentRepriced 12023 world12023 paperAgent12023 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12023, agent12023]

noncomputable def paperAgent12024 : AgentParameters :=
  { agent12024 with charge := (329379483 / 250000000000 : ℝ) }

theorem agent_is_repriced12024 : agent12024 =
    BstLean.Part265.agentRepriced 12024 world12024 paperAgent12024 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12024, agent12024]

noncomputable def paperAgent12025 : AgentParameters :=
  { agent12025 with charge := (658573641 / 500000000000 : ℝ) }

theorem agent_is_repriced12025 : agent12025 =
    BstLean.Part265.agentRepriced 12025 world12025 paperAgent12025 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12025, agent12025]

noncomputable def paperAgent12026 : AgentParameters :=
  { agent12026 with charge := (658388551 / 500000000000 : ℝ) }

theorem agent_is_repriced12026 : agent12026 =
    BstLean.Part265.agentRepriced 12026 world12026 paperAgent12026 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12026, agent12026]

noncomputable def paperAgent12027 : AgentParameters :=
  { agent12027 with charge := (1316407393 / 1000000000000 : ℝ) }

theorem agent_is_repriced12027 : agent12027 =
    BstLean.Part265.agentRepriced 12027 world12027 paperAgent12027 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12027, agent12027]

noncomputable def paperAgent12028 : AgentParameters :=
  { agent12028 with charge := (658019077 / 500000000000 : ℝ) }

theorem agent_is_repriced12028 : agent12028 =
    BstLean.Part265.agentRepriced 12028 world12028 paperAgent12028 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12028, agent12028]

noncomputable def paperAgent12029 : AgentParameters :=
  { agent12029 with charge := (1315669383 / 1000000000000 : ℝ) }

theorem agent_is_repriced12029 : agent12029 =
    BstLean.Part265.agentRepriced 12029 world12029 paperAgent12029 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12029, agent12029]

noncomputable def paperAgent12030 : AgentParameters :=
  { agent12030 with charge := (1315301081 / 1000000000000 : ℝ) }

theorem agent_is_repriced12030 : agent12030 =
    BstLean.Part265.agentRepriced 12030 world12030 paperAgent12030 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12030, agent12030]

noncomputable def paperAgent12031 : AgentParameters :=
  { agent12031 with charge := (657466623 / 500000000000 : ℝ) }

theorem agent_is_repriced12031 : agent12031 =
    BstLean.Part265.agentRepriced 12031 world12031 paperAgent12031 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12031, agent12031]

noncomputable def paperAgent12032 : AgentParameters :=
  { agent12032 with charge := (657282939 / 500000000000 : ℝ) }

theorem agent_is_repriced12032 : agent12032 =
    BstLean.Part265.agentRepriced 12032 world12032 paperAgent12032 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12032, agent12032]

noncomputable def paperAgent12033 : AgentParameters :=
  { agent12033 with charge := (20534359 / 15625000000 : ℝ) }

theorem agent_is_repriced12033 : agent12033 =
    BstLean.Part265.agentRepriced 12033 world12033 paperAgent12033 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12033, agent12033]

end BstLean.Part281
