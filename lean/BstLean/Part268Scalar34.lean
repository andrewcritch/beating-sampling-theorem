import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13200 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13200. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13200 : WorldParameters where
  hiddenCharge := (575796981 / 500000000000 : ℝ)
  frame := (618971361837 / 1000000000000 : ℝ)
  moment := (2131884173 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13200 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182156730871 / 125000000000 : ℝ)
    root := (8178160303 / 1000000000000 : ℝ) }

noncomputable def scalar13200 : ScalarCertificate 13200 world13200 agent13200 where
  dimensionLo := 13200
  dimensionHi := 13200
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2363743399 / 1000000000000 : ℝ)
  frameLo := (618971361837 / 1000000000000 : ℝ)
  frameHi := (182156730871 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13200]
  agentFrame_pos := by norm_num only [agent13200]
  worldRadius := (2363743399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13200]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (239309447 / 250000000000 : ℝ)
  lowerTail := (1164128887 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (25774793 / 3906250000 : ℝ)
  ledger := by
    have h : (575796981 / 500000000000 : ℚ) +
        (2131884173 / 250000000000000000 : ℚ) / (2363743399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (239309447 / 250000000000 : ℚ) + (1164128887 / 1000000000000 : ℚ) ≤
        (25774793 / 3906250000 : ℚ) := by norm_num only
    have hc : (((575796981 / 500000000000 : ℚ) +
        (2131884173 / 250000000000000000 : ℚ) / (2363743399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (239309447 / 250000000000 : ℚ) + (1164128887 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((25774793 / 3906250000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13200]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13200 :
    2 * 160 < 13200 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (499999849 / 50000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13200 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13201 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13201. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13201 : WorldParameters where
  hiddenCharge := (575777833 / 500000000000 : ℝ)
  frame := (618958562967 / 1000000000000 : ℝ)
  moment := (4262925507 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13201 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364306531387 / 250000000000 : ℝ)
    root := (8177568871 / 1000000000000 : ℝ) }

noncomputable def scalar13201 : ScalarCertificate 13201 world13201 agent13201 where
  dimensionLo := 13201
  dimensionHi := 13201
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2364109599 / 1000000000000 : ℝ)
  frameLo := (618958562967 / 1000000000000 : ℝ)
  frameHi := (364306531387 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13201]
  agentFrame_pos := by norm_num only [agent13201]
  worldRadius := (2364109599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13201]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (191294313 / 200000000000 : ℝ)
  lowerTail := (290815997 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6595903193 / 1000000000000 : ℝ)
  ledger := by
    have h : (575777833 / 500000000000 : ℚ) +
        (4262925507 / 500000000000000000 : ℚ) / (2364109599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (191294313 / 200000000000 : ℚ) + (290815997 / 250000000000 : ℚ) ≤
        (6595903193 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((575777833 / 500000000000 : ℚ) +
        (4262925507 / 500000000000000000 : ℚ) / (2364109599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (191294313 / 200000000000 : ℚ) + (290815997 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6595903193 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13201]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13201 :
    2 * 160 < 13201 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999763 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13201 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13202 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13202. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13202 : WorldParameters where
  hiddenCharge := (57575869 / 50000000000 : ℝ)
  frame := (618945766057 / 1000000000000 : ℝ)
  moment := (4262082901 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13202 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457198420787 / 1000000000000 : ℝ)
    root := (4088488767 / 500000000000 : ℝ) }

noncomputable def scalar13202 : ScalarCertificate 13202 world13202 agent13202 where
  dimensionLo := 13202
  dimensionHi := 13202
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2364475799 / 1000000000000 : ℝ)
  frameLo := (618945766057 / 1000000000000 : ℝ)
  frameHi := (1457198420787 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13202]
  agentFrame_pos := by norm_num only [agent13202]
  worldRadius := (2364475799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13202]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (955706021 / 1000000000000 : ℝ)
  lowerTail := (232479963 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3296730641 / 500000000000 : ℝ)
  ledger := by
    have h : (57575869 / 50000000000 : ℚ) +
        (4262082901 / 500000000000000000 : ℚ) / (2364475799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (955706021 / 1000000000000 : ℚ) + (232479963 / 200000000000 : ℚ) ≤
        (3296730641 / 500000000000 : ℚ) := by norm_num only
    have hc : (((57575869 / 50000000000 : ℚ) +
        (4262082901 / 500000000000000000 : ℚ) / (2364475799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (955706021 / 1000000000000 : ℚ) + (232479963 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3296730641 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13202]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13202 :
    2 * 160 < 13202 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997333 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13202 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13203 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13203. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13203 : WorldParameters where
  hiddenCharge := (1151479103 / 1000000000000 : ℝ)
  frame := (309466485553 / 500000000000 : ℝ)
  moment := (266327533 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13203 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291434145373 / 200000000000 : ℝ)
    root := (1635277283 / 200000000000 : ℝ) }

noncomputable def scalar13203 : ScalarCertificate 13203 world13203 agent13203 where
  dimensionLo := 13203
  dimensionHi := 13203
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2364841999 / 1000000000000 : ℝ)
  frameLo := (309466485553 / 500000000000 : ℝ)
  frameHi := (291434145373 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13203]
  agentFrame_pos := by norm_num only [agent13203]
  worldRadius := (2364841999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13203]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (954941209 / 1000000000000 : ℝ)
  lowerTail := (1161536417 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6591021377 / 1000000000000 : ℝ)
  ledger := by
    have h : (1151479103 / 1000000000000 : ℚ) +
        (266327533 / 31250000000000000 : ℚ) / (2364841999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (954941209 / 1000000000000 : ℚ) + (1161536417 / 1000000000000 : ℚ) ≤
        (6591021377 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1151479103 / 1000000000000 : ℚ) +
        (266327533 / 31250000000000000 : ℚ) / (2364841999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (954941209 / 1000000000000 : ℚ) + (1161536417 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6591021377 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13203]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13203 :
    2 * 160 < 13203 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999779 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13203 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13204 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13204. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13204 : WorldParameters where
  hiddenCharge := (287860209 / 250000000000 : ℝ)
  frame := (309460089057 / 500000000000 : ℝ)
  moment := (340831871 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13204 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182142881199 / 125000000000 : ℝ)
    root := (2043948863 / 250000000000 : ℝ) }

noncomputable def scalar13204 : ScalarCertificate 13204 world13204 agent13204 where
  dimensionLo := 13204
  dimensionHi := 13204
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2365208199 / 1000000000000 : ℝ)
  frameLo := (309460089057 / 500000000000 : ℝ)
  frameHi := (182142881199 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13204]
  agentFrame_pos := by norm_num only [agent13204]
  worldRadius := (2365208199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13204]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (95417711 / 100000000000 : ℝ)
  lowerTail := (1160673781 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3294291723 / 500000000000 : ℝ)
  ledger := by
    have h : (287860209 / 250000000000 : ℚ) +
        (340831871 / 40000000000000000 : ℚ) / (2365208199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (95417711 / 100000000000 : ℚ) + (1160673781 / 1000000000000 : ℚ) ≤
        (3294291723 / 500000000000 : ℚ) := by norm_num only
    have hc : (((287860209 / 250000000000 : ℚ) +
        (340831871 / 40000000000000000 : ℚ) / (2365208199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (95417711 / 100000000000 : ℚ) + (1160673781 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3294291723 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13204]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13204 :
    2 * 160 < 13204 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997887 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13204 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13205 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13205. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13205 : WorldParameters where
  hiddenCharge := (575701289 / 500000000000 : ℝ)
  frame := (618907387079 / 1000000000000 : ℝ)
  moment := (8519112959 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13205 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457115383147 / 1000000000000 : ℝ)
    root := (1021900573 / 125000000000 : ℝ) }

noncomputable def scalar13205 : ScalarCertificate 13205 world13205 agent13205 where
  dimensionLo := 13205
  dimensionHi := 13205
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2365574399 / 1000000000000 : ℝ)
  frameLo := (618907387079 / 1000000000000 : ℝ)
  frameHi := (1457115383147 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13205]
  agentFrame_pos := by norm_num only [agent13205]
  worldRadius := (2365574399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13205]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (953413669 / 1000000000000 : ℝ)
  lowerTail := (231962369 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (658614737 / 100000000000 : ℝ)
  ledger := by
    have h : (575701289 / 500000000000 : ℚ) +
        (8519112959 / 1000000000000000000 : ℚ) / (2365574399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (953413669 / 1000000000000 : ℚ) + (231962369 / 200000000000 : ℚ) ≤
        (658614737 / 100000000000 : ℚ) := by norm_num only
    have hc : (((575701289 / 500000000000 : ℚ) +
        (8519112959 / 1000000000000000000 : ℚ) / (2365574399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (953413669 / 1000000000000 : ℚ) + (231962369 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((658614737 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13205]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13205 :
    2 * 160 < 13205 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997829 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13205 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13206 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13206. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13206 : WorldParameters where
  hiddenCharge := (1151364331 / 1000000000000 : ℝ)
  frame := (309447299001 / 500000000000 : ℝ)
  moment := (1064678701 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13206 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58283509101 / 40000000000 : ℝ)
    root := (8174613933 / 1000000000000 : ℝ) }

noncomputable def scalar13206 : ScalarCertificate 13206 world13206 agent13206 where
  dimensionLo := 13206
  dimensionHi := 13206
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2365940699 / 1000000000000 : ℝ)
  frameLo := (309447299001 / 500000000000 : ℝ)
  frameHi := (58283509101 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13206]
  agentFrame_pos := by norm_num only [agent13206]
  worldRadius := (2365940699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13206]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (476325509 / 500000000000 : ℝ)
  lowerTail := (4635803 / 4000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6583713297 / 1000000000000 : ℝ)
  ledger := by
    have h : (1151364331 / 1000000000000 : ℚ) +
        (1064678701 / 125000000000000000 : ℚ) / (2365940699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (476325509 / 500000000000 : ℚ) + (4635803 / 4000000000 : ℚ) ≤
        (6583713297 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1151364331 / 1000000000000 : ℚ) +
        (1064678701 / 125000000000000000 : ℚ) / (2365940699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (476325509 / 500000000000 : ℚ) + (4635803 / 4000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6583713297 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13206]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13206 :
    2 * 160 < 13206 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997867 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13206 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13207 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13207. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13207 : WorldParameters where
  hiddenCharge := (1151326093 / 1000000000000 : ℝ)
  frame := (618881810883 / 1000000000000 : ℝ)
  moment := (8515746721 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13207 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291412017707 / 200000000000 : ℝ)
    root := (8174023377 / 1000000000000 : ℝ) }

noncomputable def scalar13207 : ScalarCertificate 13207 world13207 agent13207 where
  dimensionLo := 13207
  dimensionHi := 13207
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2366306899 / 1000000000000 : ℝ)
  frameLo := (618881810883 / 1000000000000 : ℝ)
  frameHi := (291412017707 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13207]
  agentFrame_pos := by norm_num only [agent13207]
  worldRadius := (2366306899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13207]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (951888981 / 1000000000000 : ℝ)
  lowerTail := (1158090309 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1645320279 / 250000000000 : ℝ)
  ledger := by
    have h : (1151326093 / 1000000000000 : ℚ) +
        (8515746721 / 1000000000000000000 : ℚ) / (2366306899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (951888981 / 1000000000000 : ℚ) + (1158090309 / 1000000000000 : ℚ) ≤
        (1645320279 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1151326093 / 1000000000000 : ℚ) +
        (8515746721 / 1000000000000000000 : ℚ) / (2366306899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (951888981 / 1000000000000 : ℚ) + (1158090309 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1645320279 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13207]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13207 :
    2 * 160 < 13207 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998329 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13207 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13208 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13208. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13208 : WorldParameters where
  hiddenCharge := (230257573 / 200000000000 : ℝ)
  frame := (15471725643 / 25000000000 : ℝ)
  moment := (85140643 / 10000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13208 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728516230179 / 500000000000 : ℝ)
    root := (4086716519 / 500000000000 : ℝ) }

noncomputable def scalar13208 : ScalarCertificate 13208 world13208 agent13208 where
  dimensionLo := 13208
  dimensionHi := 13208
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2366673099 / 1000000000000 : ℝ)
  frameLo := (15471725643 / 25000000000 : ℝ)
  frameHi := (728516230179 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13208]
  agentFrame_pos := by norm_num only [agent13208]
  worldRadius := (2366673099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13208]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (951127673 / 1000000000000 : ℝ)
  lowerTail := (1157230639 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3289425467 / 500000000000 : ℝ)
  ledger := by
    have h : (230257573 / 200000000000 : ℚ) +
        (85140643 / 10000000000000000 : ℚ) / (2366673099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (951127673 / 1000000000000 : ℚ) + (1157230639 / 1000000000000 : ℚ) ≤
        (3289425467 / 500000000000 : ℚ) := by norm_num only
    have hc : (((230257573 / 200000000000 : ℚ) +
        (85140643 / 10000000000000000 : ℚ) / (2366673099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (951127673 / 1000000000000 : ℚ) + (1157230639 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3289425467 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13208]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13208 :
    2 * 160 < 13208 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997737 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13208 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13209 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13209. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13209 : WorldParameters where
  hiddenCharge := (1151249647 / 1000000000000 : ℝ)
  frame := (618856242513 / 1000000000000 : ℝ)
  moment := (4256191171 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13209 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728502424401 / 500000000000 : ℝ)
    root := (1634568571 / 200000000000 : ℝ) }

noncomputable def scalar13209 : ScalarCertificate 13209 world13209 agent13209 where
  dimensionLo := 13209
  dimensionHi := 13209
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2367039499 / 1000000000000 : ℝ)
  frameLo := (618856242513 / 1000000000000 : ℝ)
  frameHi := (728502424401 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13209]
  agentFrame_pos := by norm_num only [agent13209]
  worldRadius := (2367039499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13209]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (190073439 / 200000000000 : ℝ)
  lowerTail := (144546483 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3288211357 / 500000000000 : ℝ)
  ledger := by
    have h : (1151249647 / 1000000000000 : ℚ) +
        (4256191171 / 500000000000000000 : ℚ) / (2367039499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (190073439 / 200000000000 : ℚ) + (144546483 / 125000000000 : ℚ) ≤
        (3288211357 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1151249647 / 1000000000000 : ℚ) +
        (4256191171 / 500000000000000000 : ℚ) / (2367039499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (190073439 / 200000000000 : ℚ) + (144546483 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3288211357 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13209]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13209 :
    2 * 160 < 13209 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997679 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13209 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13210 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13210. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13210 : WorldParameters where
  hiddenCharge := (575605719 / 500000000000 : ℝ)
  frame := (309421730631 / 500000000000 : ℝ)
  moment := (170214017 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13210 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728450760171 / 500000000000 : ℝ)
    root := (8172252767 / 1000000000000 : ℝ) }

noncomputable def scalar13210 : ScalarCertificate 13210 world13210 agent13210 where
  dimensionLo := 13210
  dimensionHi := 13210
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2367524399 / 1000000000000 : ℝ)
  frameLo := (309421730631 / 500000000000 : ℝ)
  frameHi := (728450760171 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13210]
  agentFrame_pos := by norm_num only [agent13210]
  worldRadius := (2367524399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13210]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (474721173 / 500000000000 : ℝ)
  lowerTail := (288823579 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1643364961 / 250000000000 : ℝ)
  ledger := by
    have h : (575605719 / 500000000000 : ℚ) +
        (170214017 / 20000000000000000 : ℚ) / (2367524399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (474721173 / 500000000000 : ℚ) + (288823579 / 250000000000 : ℚ) ≤
        (1643364961 / 250000000000 : ℚ) := by norm_num only
    have hc : (((575605719 / 500000000000 : ℚ) +
        (170214017 / 20000000000000000 : ℚ) / (2367524399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (474721173 / 500000000000 : ℚ) + (288823579 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1643364961 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13210]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13210 :
    2 * 160 < 13210 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995229 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13210 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13211 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13211. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13211 : WorldParameters where
  hiddenCharge := (1151173239 / 1000000000000 : ℝ)
  frame := (309415340983 / 500000000000 : ℝ)
  moment := (8509019821 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13211 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182109241401 / 125000000000 : ℝ)
    root := (1634332579 / 200000000000 : ℝ) }

noncomputable def scalar13211 : ScalarCertificate 13211 world13211 agent13211 where
  dimensionLo := 13211
  dimensionHi := 13211
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2367890699 / 1000000000000 : ℝ)
  frameLo := (309415340983 / 500000000000 : ℝ)
  frameHi := (182109241401 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13211]
  agentFrame_pos := by norm_num only [agent13211]
  worldRadius := (2367890699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13211]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (474341649 / 500000000000 : ℝ)
  lowerTail := (577218537 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6571035811 / 1000000000000 : ℝ)
  ledger := by
    have h : (1151173239 / 1000000000000 : ℚ) +
        (8509019821 / 1000000000000000000 : ℚ) / (2367890699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (474341649 / 500000000000 : ℚ) + (577218537 / 500000000000 : ℚ) ≤
        (6571035811 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1151173239 / 1000000000000 : ℚ) +
        (8509019821 / 1000000000000000000 : ℚ) / (2367890699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (474341649 / 500000000000 : ℚ) + (577218537 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6571035811 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13211]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13211 :
    2 * 160 < 13211 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998667 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13211 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13212 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13212. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13212 : WorldParameters where
  hiddenCharge := (23022701 / 20000000000 : ℝ)
  frame := (4950543237 / 8000000000 : ℝ)
  moment := (1063417407 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13212 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1456846358679 / 1000000000000 : ℝ)
    root := (4085536559 / 500000000000 : ℝ) }

noncomputable def scalar13212 : ScalarCertificate 13212 world13212 agent13212 where
  dimensionLo := 13212
  dimensionHi := 13212
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2368256899 / 1000000000000 : ℝ)
  frameLo := (4950543237 / 8000000000 : ℝ)
  frameHi := (1456846358679 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13212]
  agentFrame_pos := by norm_num only [agent13212]
  worldRadius := (2368256899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13212]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (947924861 / 1000000000000 : ℝ)
  lowerTail := (576790241 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3284306831 / 500000000000 : ℝ)
  ledger := by
    have h : (23022701 / 20000000000 : ℚ) +
        (1063417407 / 125000000000000000 : ℚ) / (2368256899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (947924861 / 1000000000000 : ℚ) + (576790241 / 500000000000 : ℚ) ≤
        (3284306831 / 500000000000 : ℚ) := by norm_num only
    have hc : (((23022701 / 20000000000 : ℚ) +
        (1063417407 / 125000000000000000 : ℚ) / (2368256899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (947924861 / 1000000000000 : ℚ) + (576790241 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3284306831 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13212]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13212 :
    2 * 160 < 13212 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (124999949 / 12500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13212 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13213 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13213. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13213 : WorldParameters where
  hiddenCharge := (115109687 / 100000000000 : ℝ)
  frame := (309402564619 / 500000000000 : ℝ)
  moment := (1701131831 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13213 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182102349617 / 125000000000 : ℝ)
    root := (8170483557 / 1000000000000 : ℝ) }

noncomputable def scalar13213 : ScalarCertificate 13213 world13213 agent13213 where
  dimensionLo := 13213
  dimensionHi := 13213
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2368623299 / 1000000000000 : ℝ)
  frameLo := (309402564619 / 500000000000 : ℝ)
  frameHi := (182102349617 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13213]
  agentFrame_pos := by norm_num only [agent13213]
  worldRadius := (2368623299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13213]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (947167269 / 1000000000000 : ℝ)
  lowerTail := (576362397 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3283096751 / 500000000000 : ℝ)
  ledger := by
    have h : (115109687 / 100000000000 : ℚ) +
        (1701131831 / 200000000000000000 : ℚ) / (2368623299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (947167269 / 1000000000000 : ℚ) + (576362397 / 500000000000 : ℚ) ≤
        (3283096751 / 500000000000 : ℚ) := by norm_num only
    have hc : (((115109687 / 100000000000 : ℚ) +
        (1701131831 / 200000000000000000 : ℚ) / (2368623299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (947167269 / 1000000000000 : ℚ) + (576362397 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3283096751 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13213]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13213 :
    2 * 160 < 13213 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (312499897 / 31250000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13213 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13214 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13214. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13214 : WorldParameters where
  hiddenCharge := (11510587 / 10000000000 : ℝ)
  frame := (309396177903 / 500000000000 : ℝ)
  moment := (4251989759 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13214 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58271649839 / 40000000000 : ℝ)
    root := (1021236769 / 125000000000 : ℝ) }

noncomputable def scalar13214 : ScalarCertificate 13214 world13214 agent13214 where
  dimensionLo := 13214
  dimensionHi := 13214
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2368989599 / 1000000000000 : ℝ)
  frameLo := (309396177903 / 500000000000 : ℝ)
  frameHi := (58271649839 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13214]
  agentFrame_pos := by norm_num only [agent13214]
  worldRadius := (2368989599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13214]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (14787661 / 15625000000 : ℝ)
  lowerTail := (143983721 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (820471907 / 125000000000 : ℝ)
  ledger := by
    have h : (11510587 / 10000000000 : ℚ) +
        (4251989759 / 500000000000000000 : ℚ) / (2368989599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (14787661 / 15625000000 : ℚ) + (143983721 / 125000000000 : ℚ) ≤
        (820471907 / 125000000000 : ℚ) := by norm_num only
    have hc : (((11510587 / 10000000000 : ℚ) +
        (4251989759 / 500000000000000000 : ℚ) / (2368989599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (14787661 / 15625000000 : ℚ) + (143983721 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((820471907 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13214]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13214 :
    2 * 160 < 13214 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999833 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13214 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13215 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13215. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13215 : WorldParameters where
  hiddenCharge := (57551027 / 50000000000 : ℝ)
  frame := (309389792163 / 500000000000 : ℝ)
  moment := (1062787543 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13215 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728381855801 / 500000000000 : ℝ)
    root := (8169304841 / 1000000000000 : ℝ) }

noncomputable def scalar13215 : ScalarCertificate 13215 world13215 agent13215 where
  dimensionLo := 13215
  dimensionHi := 13215
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2369355899 / 1000000000000 : ℝ)
  frameLo := (309389792163 / 500000000000 : ℝ)
  frameHi := (728381855801 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13215]
  agentFrame_pos := by norm_num only [agent13215]
  worldRadius := (2369355899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13215]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (118206751 / 125000000000 : ℝ)
  lowerTail := (575507729 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (820169861 / 125000000000 : ℝ)
  ledger := by
    have h : (57551027 / 50000000000 : ℚ) +
        (1062787543 / 125000000000000000 : ℚ) / (2369355899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (118206751 / 125000000000 : ℚ) + (575507729 / 500000000000 : ℚ) ≤
        (820169861 / 125000000000 : ℚ) := by norm_num only
    have hc : (((57551027 / 50000000000 : ℚ) +
        (1062787543 / 125000000000000000 : ℚ) / (2369355899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (118206751 / 125000000000 : ℚ) + (575507729 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((820169861 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13215]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13215 :
    2 * 160 < 13215 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999763 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13215 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13216 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13216. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13216 : WorldParameters where
  hiddenCharge := (1150982389 / 1000000000000 : ℝ)
  frame := (618766814799 / 1000000000000 : ℝ)
  moment := (4250310817 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13216 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1456736193811 / 1000000000000 : ℝ)
    root := (4084357873 / 500000000000 : ℝ) }

noncomputable def scalar13216 : ScalarCertificate 13216 world13216 agent13216 where
  dimensionLo := 13216
  dimensionHi := 13216
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2369722199 / 1000000000000 : ℝ)
  frameLo := (618766814799 / 1000000000000 : ℝ)
  frameHi := (1456736193811 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13216]
  agentFrame_pos := by norm_num only [agent13216]
  worldRadius := (2369722199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13216]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (236224613 / 250000000000 : ℝ)
  lowerTail := (71885121 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (204967017 / 31250000000 : ℝ)
  ledger := by
    have h : (1150982389 / 1000000000000 : ℚ) +
        (4250310817 / 500000000000000000 : ℚ) / (2369722199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236224613 / 250000000000 : ℚ) + (71885121 / 62500000000 : ℚ) ≤
        (204967017 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1150982389 / 1000000000000 : ℚ) +
        (4250310817 / 500000000000000000 : ℚ) / (2369722199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236224613 / 250000000000 : ℚ) + (71885121 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((204967017 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13216]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13216 :
    2 * 160 < 13216 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994839 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13216 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13217 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13217. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13217 : WorldParameters where
  hiddenCharge := (1150944249 / 1000000000000 : ℝ)
  frame := (24750161889 / 40000000000 : ℝ)
  moment := (8498943387 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13217 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728354340487 / 500000000000 : ℝ)
    root := (4084063373 / 500000000000 : ℝ) }

noncomputable def scalar13217 : ScalarCertificate 13217 world13217 agent13217 where
  dimensionLo := 13217
  dimensionHi := 13217
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2370088599 / 1000000000000 : ℝ)
  frameLo := (24750161889 / 40000000000 : ℝ)
  frameHi := (728354340487 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13217]
  agentFrame_pos := by norm_num only [agent13217]
  worldRadius := (2370088599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13217]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (236035897 / 250000000000 : ℝ)
  lowerTail := (1149309151 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6556531993 / 1000000000000 : ℝ)
  ledger := by
    have h : (1150944249 / 1000000000000 : ℚ) +
        (8498943387 / 1000000000000000000 : ℚ) / (2370088599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236035897 / 250000000000 : ℚ) + (1149309151 / 1000000000000 : ℚ) ≤
        (6556531993 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1150944249 / 1000000000000 : ℚ) +
        (8498943387 / 1000000000000000000 : ℚ) / (2370088599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236035897 / 250000000000 : ℚ) + (1149309151 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6556531993 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13217]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13217 :
    2 * 160 < 13217 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999623 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13217 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13218 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13218. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13218 : WorldParameters where
  hiddenCharge := (575453059 / 500000000000 : ℝ)
  frame := (309370640801 / 500000000000 : ℝ)
  moment := (4248632801 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13218 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (145668118471 / 100000000000 : ℝ)
    root := (8167537961 / 1000000000000 : ℝ) }

noncomputable def scalar13218 : ScalarCertificate 13218 world13218 agent13218 where
  dimensionLo := 13218
  dimensionHi := 13218
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2370454899 / 1000000000000 : ℝ)
  frameLo := (309370640801 / 500000000000 : ℝ)
  frameHi := (145668118471 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13218]
  agentFrame_pos := by norm_num only [agent13218]
  worldRadius := (2370454899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13218]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (471694701 / 500000000000 : ℝ)
  lowerTail := (574228543 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6554121463 / 1000000000000 : ℝ)
  ledger := by
    have h : (575453059 / 500000000000 : ℚ) +
        (4248632801 / 500000000000000000 : ℚ) / (2370454899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (471694701 / 500000000000 : ℚ) + (574228543 / 500000000000 : ℚ) ≤
        (6554121463 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((575453059 / 500000000000 : ℚ) +
        (4248632801 / 500000000000000000 : ℚ) / (2370454899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (471694701 / 500000000000 : ℚ) + (574228543 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6554121463 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13218]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13218 :
    2 * 160 < 13218 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998509 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13218 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13219 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13219. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13219 : WorldParameters where
  hiddenCharge := (287716999 / 250000000000 : ℝ)
  frame := (618728517931 / 1000000000000 : ℝ)
  moment := (8495588281 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13219 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364163426253 / 250000000000 : ℝ)
    root := (8166949271 / 1000000000000 : ℝ) }

noncomputable def scalar13219 : ScalarCertificate 13219 world13219 agent13219 where
  dimensionLo := 13219
  dimensionHi := 13219
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2370821299 / 1000000000000 : ℝ)
  frameLo := (618728517931 / 1000000000000 : ℝ)
  frameHi := (364163426253 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13219]
  agentFrame_pos := by norm_num only [agent13219]
  worldRadius := (2370821299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13219]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (471317971 / 500000000000 : ℝ)
  lowerTail := (5738029 / 5000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1637928201 / 250000000000 : ℝ)
  ledger := by
    have h : (287716999 / 250000000000 : ℚ) +
        (8495588281 / 1000000000000000000 : ℚ) / (2370821299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (471317971 / 500000000000 : ℚ) + (5738029 / 5000000000 : ℚ) ≤
        (1637928201 / 250000000000 : ℚ) := by norm_num only
    have hc : (((287716999 / 250000000000 : ℚ) +
        (8495588281 / 1000000000000000000 : ℚ) / (2370821299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (471317971 / 500000000000 : ℚ) + (5738029 / 5000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1637928201 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13219]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13219 :
    2 * 160 < 13219 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999487 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13219 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13220 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13220. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13220 : WorldParameters where
  hiddenCharge := (287707471 / 250000000000 : ℝ)
  frame := (618715756211 / 1000000000000 : ℝ)
  moment := (4246955711 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13220 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1456549513401 / 1000000000000 : ℝ)
    root := (2041590199 / 250000000000 : ℝ) }

noncomputable def scalar13220 : ScalarCertificate 13220 world13220 agent13220 where
  dimensionLo := 13220
  dimensionHi := 13220
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2371308199 / 1000000000000 : ℝ)
  frameLo := (618715756211 / 1000000000000 : ℝ)
  frameHi := (1456549513401 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13220]
  agentFrame_pos := by norm_num only [agent13220]
  worldRadius := (2371308199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13220]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (941717377 / 1000000000000 : ℝ)
  lowerTail := (1146534589 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6548766077 / 1000000000000 : ℝ)
  ledger := by
    have h : (287707471 / 250000000000 : ℚ) +
        (4246955711 / 500000000000000000 : ℚ) / (2371308199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (941717377 / 1000000000000 : ℚ) + (1146534589 / 1000000000000 : ℚ) ≤
        (6548766077 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((287707471 / 250000000000 : ℚ) +
        (4246955711 / 500000000000000000 : ℚ) / (2371308199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (941717377 / 1000000000000 : ℚ) + (1146534589 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6548766077 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13220]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13220 :
    2 * 160 < 13220 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999881 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13220 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13221 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13221. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13221 : WorldParameters where
  hiddenCharge := (575395891 / 500000000000 : ℝ)
  frame := (618702996441 / 1000000000000 : ℝ)
  moment := (4246117513 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13221 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364130514007 / 250000000000 : ℝ)
    root := (1633154483 / 200000000000 : ℝ) }

noncomputable def scalar13221 : ScalarCertificate 13221 world13221 agent13221 where
  dimensionLo := 13221
  dimensionHi := 13221
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2371674499 / 1000000000000 : ℝ)
  frameLo := (618702996441 / 1000000000000 : ℝ)
  frameHi := (364130514007 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13221]
  agentFrame_pos := by norm_num only [agent13221]
  worldRadius := (2371674499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13221]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (470482667 / 500000000000 : ℝ)
  lowerTail := (143210603 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (654636157 / 100000000000 : ℝ)
  ledger := by
    have h : (575395891 / 500000000000 : ℚ) +
        (4246117513 / 500000000000000000 : ℚ) / (2371674499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (470482667 / 500000000000 : ℚ) + (143210603 / 125000000000 : ℚ) ≤
        (654636157 / 100000000000 : ℚ) := by norm_num only
    have hc : (((575395891 / 500000000000 : ℚ) +
        (4246117513 / 500000000000000000 : ℚ) / (2371674499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (470482667 / 500000000000 : ℚ) + (143210603 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((654636157 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13221]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13221 :
    2 * 160 < 13221 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999883 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13221 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13222 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13222. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13222 : WorldParameters where
  hiddenCharge := (115075369 / 100000000000 : ℝ)
  frame := (618690238621 / 1000000000000 : ℝ)
  moment := (2122639773 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13222 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364123653801 / 250000000000 : ℝ)
    root := (32660737 / 4000000000 : ℝ) }

noncomputable def scalar13222 : ScalarCertificate 13222 world13222 agent13222 where
  dimensionLo := 13222
  dimensionHi := 13222
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2372040899 / 1000000000000 : ℝ)
  frameLo := (618690238621 / 1000000000000 : ℝ)
  frameHi := (364123653801 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13222]
  agentFrame_pos := by norm_num only [agent13222]
  worldRadius := (2372040899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13222]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (940214087 / 1000000000000 : ℝ)
  lowerTail := (114483591 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (261758363 / 40000000000 : ℝ)
  ledger := by
    have h : (115075369 / 100000000000 : ℚ) +
        (2122639773 / 250000000000000000 : ℚ) / (2372040899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (940214087 / 1000000000000 : ℚ) + (114483591 / 100000000000 : ℚ) ≤
        (261758363 / 40000000000 : ℚ) := by norm_num only
    have hc : (((115075369 / 100000000000 : ℚ) +
        (2122639773 / 250000000000000000 : ℚ) / (2372040899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (940214087 / 1000000000000 : ℚ) + (114483591 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((261758363 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13222]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13222 :
    2 * 160 < 13222 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996301 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13222 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13223 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13223. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13223 : WorldParameters where
  hiddenCharge := (1150715607 / 1000000000000 : ℝ)
  frame := (618677482751 / 1000000000000 : ℝ)
  moment := (8488883621 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13223 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364116796279 / 250000000000 : ℝ)
    root := (4082298089 / 500000000000 : ℝ) }

noncomputable def scalar13223 : ScalarCertificate 13223 world13223 agent13223 where
  dimensionLo := 13223
  dimensionHi := 13223
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2372407399 / 1000000000000 : ℝ)
  frameLo := (618677482751 / 1000000000000 : ℝ)
  frameHi := (364116796279 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13223]
  agentFrame_pos := by norm_num only [agent13223]
  worldRadius := (2372407399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13223]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (117432943 / 125000000000 : ℝ)
  lowerTail := (1143987751 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3270779201 / 500000000000 : ℝ)
  ledger := by
    have h : (1150715607 / 1000000000000 : ℚ) +
        (8488883621 / 1000000000000000000 : ℚ) / (2372407399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (117432943 / 125000000000 : ℚ) + (1143987751 / 1000000000000 : ℚ) ≤
        (3270779201 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1150715607 / 1000000000000 : ℚ) +
        (8488883621 / 1000000000000000000 : ℚ) / (2372407399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (117432943 / 125000000000 : ℚ) + (1143987751 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3270779201 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13223]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13223 :
    2 * 160 < 13223 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995087 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13223 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13224 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13224. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13224 : WorldParameters where
  hiddenCharge := (575338767 / 500000000000 : ℝ)
  frame := (61866472883 / 100000000000 : ℝ)
  moment := (8487208611 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13224 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364109941439 / 250000000000 : ℝ)
    root := (4082004161 / 500000000000 : ℝ) }

noncomputable def scalar13224 : ScalarCertificate 13224 world13224 agent13224 where
  dimensionLo := 13224
  dimensionHi := 13224
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2372773699 / 1000000000000 : ℝ)
  frameLo := (61866472883 / 100000000000 : ℝ)
  frameHi := (364109941439 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13224]
  agentFrame_pos := by norm_num only [agent13224]
  worldRadius := (2372773699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13224]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (469356799 / 500000000000 : ℝ)
  lowerTail := (1143140217 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6539159699 / 1000000000000 : ℝ)
  ledger := by
    have h : (575338767 / 500000000000 : ℚ) +
        (8487208611 / 1000000000000000000 : ℚ) / (2372773699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (469356799 / 500000000000 : ℚ) + (1143140217 / 1000000000000 : ℚ) ≤
        (6539159699 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((575338767 / 500000000000 : ℚ) +
        (8487208611 / 1000000000000000000 : ℚ) / (2372773699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (469356799 / 500000000000 : ℚ) + (1143140217 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6539159699 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13224]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13224 :
    2 * 160 < 13224 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997937 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13224 {← IO.monoMsNow}" : IO Unit)
