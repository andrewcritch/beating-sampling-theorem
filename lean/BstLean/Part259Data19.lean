import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12320 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12320. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12320 : WorldParameters where
  hiddenCharge := (1189475693 / 1000000000000 : ℝ)
  frame := (157763226541 / 250000000000 : ℝ)
  moment := (1276527707 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12320 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1840725041 / 1000000000000 : ℝ)
    frame := (1456161189391 / 1000000000000 : ℝ)
    root := (4390039967 / 500000000000 : ℝ) }

noncomputable def scalar12320 : ScalarCertificate 12320 world12320 agent12320 where
  dimensionLo := 12320
  dimensionHi := 12320
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2082185999 / 1000000000000 : ℝ)
  frameLo := (157763226541 / 250000000000 : ℝ)
  frameHi := (1456161189391 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12320]
  agentFrame_pos := by norm_num only [agent12320]
  worldRadius := (2082185999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12320]
  retainedCharge := (1840725041 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1893762721 / 1000000000000 : ℝ)
  lowerTail := (434188221 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4725197571 / 500000000000 : ℝ)
  ledger := by
    have h : (1189475693 / 1000000000000 : ℚ) +
        (1276527707 / 125000000000000000 : ℚ) / (2082185999 / 1000000000000 : ℚ) ^ 2 +
        (1840725041 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1893762721 / 1000000000000 : ℚ) + (434188221 / 200000000000 : ℚ) ≤
        (4725197571 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1189475693 / 1000000000000 : ℚ) +
        (1276527707 / 125000000000000000 : ℚ) / (2082185999 / 1000000000000 : ℚ) ^ 2 +
        (1840725041 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1893762721 / 1000000000000 : ℚ) + (434188221 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4725197571 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12320]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12320 :
    2 * 160 < 12320 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999996079 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12320 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12321 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12321. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12321 : WorldParameters where
  hiddenCharge := (1189427401 / 1000000000000 : ℝ)
  frame := (78879772137 / 125000000000 : ℝ)
  moment := (10210053059 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12321 : AgentParameters :=
  { agentLedgerParameters with
    charge := (460006071 / 250000000000 : ℝ)
    frame := (1456120745747 / 1000000000000 : ℝ)
    root := (8779356581 / 1000000000000 : ℝ) }

noncomputable def scalar12321 : ScalarCertificate 12321 world12321 agent12321 where
  dimensionLo := 12321
  dimensionHi := 12321
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2082542299 / 1000000000000 : ℝ)
  frameLo := (78879772137 / 125000000000 : ℝ)
  frameHi := (1456120745747 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12321]
  agentFrame_pos := by norm_num only [agent12321]
  worldRadius := (2082542299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12321]
  retainedCharge := (460006071 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1892092939 / 1000000000000 : ℝ)
  lowerTail := (2169152427 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (118061021 / 12500000000 : ℝ)
  ledger := by
    have h : (1189427401 / 1000000000000 : ℚ) +
        (10210053059 / 1000000000000000000 : ℚ) / (2082542299 / 1000000000000 : ℚ) ^ 2 +
        (460006071 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1892092939 / 1000000000000 : ℚ) + (2169152427 / 1000000000000 : ℚ) ≤
        (118061021 / 12500000000 : ℚ) := by norm_num only
    have hc : (((1189427401 / 1000000000000 : ℚ) +
        (10210053059 / 1000000000000000000 : ℚ) / (2082542299 / 1000000000000 : ℚ) ^ 2 +
        (460006071 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1892092939 / 1000000000000 : ℚ) + (2169152427 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((118061021 / 12500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12321]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12321 :
    2 * 160 < 12321 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (687499847 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12321 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12322 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12322. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12322 : WorldParameters where
  hiddenCharge := (594689561 / 500000000000 : ℝ)
  frame := (631023450481 / 1000000000000 : ℝ)
  moment := (2041577021 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12322 : AgentParameters :=
  { agentLedgerParameters with
    charge := (919662077 / 500000000000 : ℝ)
    frame := (291216064473 / 200000000000 : ℝ)
    root := (8778633379 / 1000000000000 : ℝ) }

noncomputable def scalar12322 : ScalarCertificate 12322 world12322 agent12322 where
  dimensionLo := 12322
  dimensionHi := 12322
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2082898699 / 1000000000000 : ℝ)
  frameLo := (631023450481 / 1000000000000 : ℝ)
  frameHi := (291216064473 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12322]
  agentFrame_pos := by norm_num only [agent12322]
  worldRadius := (2082898699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12322]
  retainedCharge := (919662077 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1890424871 / 1000000000000 : ℝ)
  lowerTail := (433473099 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4719686499 / 500000000000 : ℝ)
  ledger := by
    have h : (594689561 / 500000000000 : ℚ) +
        (2041577021 / 200000000000000000 : ℚ) / (2082898699 / 1000000000000 : ℚ) ^ 2 +
        (919662077 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1890424871 / 1000000000000 : ℚ) + (433473099 / 200000000000 : ℚ) ≤
        (4719686499 / 500000000000 : ℚ) := by norm_num only
    have hc : (((594689561 / 500000000000 : ℚ) +
        (2041577021 / 200000000000000000 : ℚ) / (2082898699 / 1000000000000 : ℚ) ^ 2 +
        (919662077 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1890424871 / 1000000000000 : ℚ) + (433473099 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4719686499 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12322]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12322 :
    2 * 160 < 12322 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499998951 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12322 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12323 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12323. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12323 : WorldParameters where
  hiddenCharge := (148666357 / 125000000000 : ℝ)
  frame := (631008726317 / 1000000000000 : ℝ)
  moment := (2041143559 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12323 : AgentParameters :=
  { agentLedgerParameters with
    charge := (459656163 / 250000000000 : ℝ)
    frame := (364009979809 / 250000000000 : ℝ)
    root := (2743097 / 312500000 : ℝ) }

noncomputable def scalar12323 : ScalarCertificate 12323 world12323 agent12323 where
  dimensionLo := 12323
  dimensionHi := 12323
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2083255099 / 1000000000000 : ℝ)
  frameLo := (631008726317 / 1000000000000 : ℝ)
  frameHi := (364009979809 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12323]
  agentFrame_pos := by norm_num only [agent12323]
  worldRadius := (2083255099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12323]
  retainedCharge := (459656163 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (377751697 / 200000000000 : ℝ)
  lowerTail := (541395067 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4716934623 / 500000000000 : ℝ)
  ledger := by
    have h : (148666357 / 125000000000 : ℚ) +
        (2041143559 / 200000000000000000 : ℚ) / (2083255099 / 1000000000000 : ℚ) ^ 2 +
        (459656163 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377751697 / 200000000000 : ℚ) + (541395067 / 250000000000 : ℚ) ≤
        (4716934623 / 500000000000 : ℚ) := by norm_num only
    have hc : (((148666357 / 125000000000 : ℚ) +
        (2041143559 / 200000000000000000 : ℚ) / (2083255099 / 1000000000000 : ℚ) ^ 2 +
        (459656163 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377751697 / 200000000000 : ℚ) + (541395067 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4716934623 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12323]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12323 :
    2 * 160 < 12323 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997099 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12323 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12324 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12324. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12324 : WorldParameters where
  hiddenCharge := (1189282603 / 1000000000000 : ℝ)
  frame := (630994004603 / 1000000000000 : ℝ)
  moment := (10203551127 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12324 : AgentParameters :=
  { agentLedgerParameters with
    charge := (918962889 / 500000000000 : ℝ)
    frame := (1455999536351 / 1000000000000 : ℝ)
    root := (8777187717 / 1000000000000 : ℝ) }

noncomputable def scalar12324 : ScalarCertificate 12324 world12324 agent12324 where
  dimensionLo := 12324
  dimensionHi := 12324
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2083611499 / 1000000000000 : ℝ)
  frameLo := (630994004603 / 1000000000000 : ℝ)
  frameHi := (1455999536351 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12324]
  agentFrame_pos := by norm_num only [agent12324]
  worldRadius := (2083611499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12324]
  retainedCharge := (918962889 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1887093857 / 1000000000000 : ℝ)
  lowerTail := (1081898411 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9428370577 / 1000000000000 : ℝ)
  ledger := by
    have h : (1189282603 / 1000000000000 : ℚ) +
        (10203551127 / 1000000000000000000 : ℚ) / (2083611499 / 1000000000000 : ℚ) ^ 2 +
        (918962889 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1887093857 / 1000000000000 : ℚ) + (1081898411 / 500000000000 : ℚ) ≤
        (9428370577 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1189282603 / 1000000000000 : ℚ) +
        (10203551127 / 1000000000000000000 : ℚ) / (2083611499 / 1000000000000 : ℚ) ^ 2 +
        (918962889 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1887093857 / 1000000000000 : ℚ) + (1081898411 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9428370577 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12324]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12324 :
    2 * 160 < 12324 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995113 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12324 {← IO.monoMsNow}" : IO Unit)
