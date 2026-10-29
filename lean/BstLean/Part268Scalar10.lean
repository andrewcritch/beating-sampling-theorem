import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12600 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12600. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12600 : WorldParameters where
  hiddenCharge := (588226261 / 500000000000 : ℝ)
  frame := (627022238601 / 1000000000000 : ℝ)
  moment := (4814642843 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12600 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480162441299 / 1000000000000 : ℝ)
    root := (4282421201 / 500000000000 : ℝ) }

noncomputable def scalar12600 : ScalarCertificate 12600 world12600 agent12600 where
  dimensionLo := 12600
  dimensionHi := 12600
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2140430299 / 1000000000000 : ℝ)
  frameLo := (627022238601 / 1000000000000 : ℝ)
  frameHi := (1480162441299 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12600]
  agentFrame_pos := by norm_num only [agent12600]
  worldRadius := (2140430299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12600]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1590178491 / 1000000000000 : ℝ)
  lowerTail := (467030521 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (853570153 / 100000000000 : ℝ)
  ledger := by
    have h : (588226261 / 500000000000 : ℚ) +
        (4814642843 / 500000000000000000 : ℚ) / (2140430299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1590178491 / 1000000000000 : ℚ) + (467030521 / 250000000000 : ℚ) ≤
        (853570153 / 100000000000 : ℚ) := by norm_num only
    have hc : (((588226261 / 500000000000 : ℚ) +
        (4814642843 / 500000000000000000 : ℚ) / (2140430299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1590178491 / 1000000000000 : ℚ) + (467030521 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((853570153 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12600]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12600 :
    2 * 160 < 12600 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998977 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12600 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12601 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12601. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12601 : WorldParameters where
  hiddenCharge := (588203873 / 500000000000 : ℝ)
  frame := (627008171459 / 1000000000000 : ℝ)
  moment := (4813644031 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12601 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480129046413 / 1000000000000 : ℝ)
    root := (1070517257 / 125000000000 : ℝ) }

noncomputable def scalar12601 : ScalarCertificate 12601 world12601 agent12601 where
  dimensionLo := 12601
  dimensionHi := 12601
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2140786199 / 1000000000000 : ℝ)
  frameLo := (627008171459 / 1000000000000 : ℝ)
  frameHi := (1480129046413 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12601]
  agentFrame_pos := by norm_num only [agent12601]
  worldRadius := (2140786199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12601]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (397203719 / 250000000000 : ℝ)
  lowerTail := (1866634259 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1706334131 / 200000000000 : ℝ)
  ledger := by
    have h : (588203873 / 500000000000 : ℚ) +
        (4813644031 / 500000000000000000 : ℚ) / (2140786199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (397203719 / 250000000000 : ℚ) + (1866634259 / 1000000000000 : ℚ) ≤
        (1706334131 / 200000000000 : ℚ) := by norm_num only
    have hc : (((588203873 / 500000000000 : ℚ) +
        (4813644031 / 500000000000000000 : ℚ) / (2140786199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (397203719 / 250000000000 : ℚ) + (1866634259 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1706334131 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12601]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12601 :
    2 * 160 < 12601 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998957 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12601 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12602 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12602. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12602 : WorldParameters where
  hiddenCharge := (1176362983 / 1000000000000 : ℝ)
  frame := (125398821319 / 200000000000 : ℝ)
  moment := (4812645509 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12602 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480095666749 / 1000000000000 : ℝ)
    root := (8563433869 / 1000000000000 : ℝ) }

noncomputable def scalar12602 : ScalarCertificate 12602 world12602 agent12602 where
  dimensionLo := 12602
  dimensionHi := 12602
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2141141999 / 1000000000000 : ℝ)
  frameLo := (125398821319 / 200000000000 : ℝ)
  frameHi := (1480095666749 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12602]
  agentFrame_pos := by norm_num only [agent12602]
  worldRadius := (2141141999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12602]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (396863113 / 250000000000 : ℝ)
  lowerTail := (1865147653 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (213191079 / 25000000000 : ℝ)
  ledger := by
    have h : (1176362983 / 1000000000000 : ℚ) +
        (4812645509 / 500000000000000000 : ℚ) / (2141141999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (396863113 / 250000000000 : ℚ) + (1865147653 / 1000000000000 : ℚ) ≤
        (213191079 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1176362983 / 1000000000000 : ℚ) +
        (4812645509 / 500000000000000000 : ℚ) / (2141141999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (396863113 / 250000000000 : ℚ) + (1865147653 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((213191079 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12602]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12602 :
    2 * 160 < 12602 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999787 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12602 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12603 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12603. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12603 : WorldParameters where
  hiddenCharge := (1176318231 / 1000000000000 : ℝ)
  frame := (62698004401 / 100000000000 : ℝ)
  moment := (1202911819 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12603 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296012461647 / 200000000000 : ℝ)
    root := (8562729979 / 1000000000000 : ℝ) }

noncomputable def scalar12603 : ScalarCertificate 12603 world12603 agent12603 where
  dimensionLo := 12603
  dimensionHi := 12603
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2141497799 / 1000000000000 : ℝ)
  frameLo := (62698004401 / 100000000000 : ℝ)
  frameHi := (296012461647 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12603]
  agentFrame_pos := by norm_num only [agent12603]
  worldRadius := (2141497799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12603]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (317218293 / 200000000000 : ℝ)
  lowerTail := (931831263 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8523619359 / 1000000000000 : ℝ)
  ledger := by
    have h : (1176318231 / 1000000000000 : ℚ) +
        (1202911819 / 125000000000000000 : ℚ) / (2141497799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (317218293 / 200000000000 : ℚ) + (931831263 / 500000000000 : ℚ) ≤
        (8523619359 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1176318231 / 1000000000000 : ℚ) +
        (1202911819 / 125000000000000000 : ℚ) / (2141497799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (317218293 / 200000000000 : ℚ) + (931831263 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8523619359 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12603]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12603 :
    2 * 160 < 12603 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998987 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12603 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12604 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12604. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12604 : WorldParameters where
  hiddenCharge := (1176273491 / 1000000000000 : ℝ)
  frame := (626965983701 / 1000000000000 : ℝ)
  moment := (1202662333 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12604 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480028970861 / 1000000000000 : ℝ)
    root := (8562026247 / 1000000000000 : ℝ) }

noncomputable def scalar12604 : ScalarCertificate 12604 world12604 agent12604 where
  dimensionLo := 12604
  dimensionHi := 12604
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2141853699 / 1000000000000 : ℝ)
  frameLo := (626965983701 / 1000000000000 : ℝ)
  frameHi := (1480028970861 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12604]
  agentFrame_pos := by norm_num only [agent12604]
  worldRadius := (2141853699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12604]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (792365941 / 500000000000 : ℝ)
  lowerTail := (931089427 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2129899749 / 250000000000 : ℝ)
  ledger := by
    have h : (1176273491 / 1000000000000 : ℚ) +
        (1202662333 / 125000000000000000 : ℚ) / (2141853699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (792365941 / 500000000000 : ℚ) + (931089427 / 500000000000 : ℚ) ≤
        (2129899749 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1176273491 / 1000000000000 : ℚ) +
        (1202662333 / 125000000000000000 : ℚ) / (2141853699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (792365941 / 500000000000 : ℚ) + (931089427 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2129899749 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12604]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12604 :
    2 * 160 < 12604 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999611 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12604 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12605 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12605. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12605 : WorldParameters where
  hiddenCharge := (1176228763 / 1000000000000 : ℝ)
  frame := (626951925669 / 1000000000000 : ℝ)
  moment := (1923860671 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12605 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369998912169 / 250000000000 : ℝ)
    root := (8561322811 / 1000000000000 : ℝ) }

noncomputable def scalar12605 : ScalarCertificate 12605 world12605 agent12605 where
  dimensionLo := 12605
  dimensionHi := 12605
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2142209499 / 1000000000000 : ℝ)
  frameLo := (626951925669 / 1000000000000 : ℝ)
  frameHi := (369998912169 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12605]
  agentFrame_pos := by norm_num only [agent12605]
  worldRadius := (2142209499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12605]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (395843403 / 250000000000 : ℝ)
  lowerTail := (1860696521 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4257791127 / 500000000000 : ℝ)
  ledger := by
    have h : (1176228763 / 1000000000000 : ℚ) +
        (1923860671 / 200000000000000000 : ℚ) / (2142209499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (395843403 / 250000000000 : ℚ) + (1860696521 / 1000000000000 : ℚ) ≤
        (4257791127 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1176228763 / 1000000000000 : ℚ) +
        (1923860671 / 200000000000000000 : ℚ) / (2142209499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (395843403 / 250000000000 : ℚ) + (1860696521 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4257791127 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12605]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12605 :
    2 * 160 < 12605 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999917 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12605 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12606 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12606. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12606 : WorldParameters where
  hiddenCharge := (1176184047 / 1000000000000 : ℝ)
  frame := (313468934957 / 500000000000 : ℝ)
  moment := (76938469 / 8000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12606 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1479962347609 / 1000000000000 : ℝ)
    root := (4280309801 / 500000000000 : ℝ) }

noncomputable def scalar12606 : ScalarCertificate 12606 world12606 agent12606 where
  dimensionLo := 12606
  dimensionHi := 12606
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2142565399 / 1000000000000 : ℝ)
  frameLo := (313468934957 / 500000000000 : ℝ)
  frameHi := (1479962347609 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12606]
  agentFrame_pos := by norm_num only [agent12606]
  worldRadius := (2142565399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12606]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (791008403 / 500000000000 : ℝ)
  lowerTail := (1859215703 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (851156907 / 100000000000 : ℝ)
  ledger := by
    have h : (1176184047 / 1000000000000 : ℚ) +
        (76938469 / 8000000000000000 : ℚ) / (2142565399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (791008403 / 500000000000 : ℚ) + (1859215703 / 1000000000000 : ℚ) ≤
        (851156907 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1176184047 / 1000000000000 : ℚ) +
        (76938469 / 8000000000000000 : ℚ) / (2142565399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (791008403 / 500000000000 : ℚ) + (1859215703 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((851156907 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12606]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12606 :
    2 * 160 < 12606 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998551 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12606 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12607 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12607. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12607 : WorldParameters where
  hiddenCharge := (1176139343 / 1000000000000 : ℝ)
  frame := (313461908217 / 500000000000 : ℝ)
  moment := (1201914309 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12607 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (11561945841 / 7812500000 : ℝ)
    root := (1069989569 / 125000000000 : ℝ) }

noncomputable def scalar12607 : ScalarCertificate 12607 world12607 agent12607 where
  dimensionLo := 12607
  dimensionHi := 12607
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2142921199 / 1000000000000 : ℝ)
  frameLo := (313461908217 / 500000000000 : ℝ)
  frameHi := (11561945841 / 7812500000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12607]
  agentFrame_pos := by norm_num only [agent12607]
  worldRadius := (2142921199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12607]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (158066121 / 100000000000 : ℝ)
  lowerTail := (1857736131 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (850755931 / 100000000000 : ℝ)
  ledger := by
    have h : (1176139343 / 1000000000000 : ℚ) +
        (1201914309 / 125000000000000000 : ℚ) / (2142921199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (158066121 / 100000000000 : ℚ) + (1857736131 / 1000000000000 : ℚ) ≤
        (850755931 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1176139343 / 1000000000000 : ℚ) +
        (1201914309 / 125000000000000000 : ℚ) / (2142921199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (158066121 / 100000000000 : ℚ) + (1857736131 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((850755931 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12607]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12607 :
    2 * 160 < 12607 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999343 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12607 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12608 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12608. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12608 : WorldParameters where
  hiddenCharge := (1176094651 / 1000000000000 : ℝ)
  frame := (626909765229 / 1000000000000 : ℝ)
  moment := (9613320897 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12608 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369973950711 / 250000000000 : ℝ)
    root := (2139803449 / 250000000000 : ℝ) }

noncomputable def scalar12608 : ScalarCertificate 12608 world12608 agent12608 where
  dimensionLo := 12608
  dimensionHi := 12608
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2143277099 / 1000000000000 : ℝ)
  frameLo := (626909765229 / 1000000000000 : ℝ)
  frameHi := (369973950711 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12608]
  agentFrame_pos := by norm_num only [agent12608]
  worldRadius := (2143277099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12608]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (157930711 / 100000000000 : ℝ)
  lowerTail := (1856258097 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4251776581 / 500000000000 : ℝ)
  ledger := by
    have h : (1176094651 / 1000000000000 : ℚ) +
        (9613320897 / 1000000000000000000 : ℚ) / (2143277099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (157930711 / 100000000000 : ℚ) + (1856258097 / 1000000000000 : ℚ) ≤
        (4251776581 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1176094651 / 1000000000000 : ℚ) +
        (9613320897 / 1000000000000000000 : ℚ) / (2143277099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (157930711 / 100000000000 : ℚ) + (1856258097 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4251776581 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12608]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12608 :
    2 * 160 < 12608 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (109999989 / 10000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12608 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12609 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12609. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12609 : WorldParameters where
  hiddenCharge := (1176049971 / 1000000000000 : ℝ)
  frame := (313447858149 / 500000000000 : ℝ)
  moment := (9611327899 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12609 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (11838900473 / 8000000000 : ℝ)
    root := (8558511199 / 1000000000000 : ℝ) }

noncomputable def scalar12609 : ScalarCertificate 12609 world12609 agent12609 where
  dimensionLo := 12609
  dimensionHi := 12609
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2143632899 / 1000000000000 : ℝ)
  frameLo := (313447858149 / 500000000000 : ℝ)
  frameHi := (11838900473 / 8000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12609]
  agentFrame_pos := by norm_num only [agent12609]
  worldRadius := (2143632899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12609]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (788977109 / 500000000000 : ℝ)
  lowerTail := (927390653 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8499550433 / 1000000000000 : ℝ)
  ledger := by
    have h : (1176049971 / 1000000000000 : ℚ) +
        (9611327899 / 1000000000000000000 : ℚ) / (2143632899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (788977109 / 500000000000 : ℚ) + (927390653 / 500000000000 : ℚ) ≤
        (8499550433 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1176049971 / 1000000000000 : ℚ) +
        (9611327899 / 1000000000000000000 : ℚ) / (2143632899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (788977109 / 500000000000 : ℚ) + (927390653 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8499550433 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12609]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12609 :
    2 * 160 < 12609 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999493 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12609 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12610 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12610. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12610 : WorldParameters where
  hiddenCharge := (1176005303 / 1000000000000 : ℝ)
  frame := (626881669641 / 1000000000000 : ℝ)
  moment := (9609335479 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12610 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739873464083 / 500000000000 : ℝ)
    root := (8557808897 / 1000000000000 : ℝ) }

noncomputable def scalar12610 : ScalarCertificate 12610 world12610 agent12610 where
  dimensionLo := 12610
  dimensionHi := 12610
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2144099899 / 1000000000000 : ℝ)
  frameLo := (626881669641 / 1000000000000 : ℝ)
  frameHi := (739873464083 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12610]
  agentFrame_pos := by norm_num only [agent12610]
  worldRadius := (2144099899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12610]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (197039547 / 125000000000 : ℝ)
  lowerTail := (46323487 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4247340827 / 500000000000 : ℝ)
  ledger := by
    have h : (1176005303 / 1000000000000 : ℚ) +
        (9609335479 / 1000000000000000000 : ℚ) / (2144099899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (197039547 / 125000000000 : ℚ) + (46323487 / 25000000000 : ℚ) ≤
        (4247340827 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1176005303 / 1000000000000 : ℚ) +
        (9609335479 / 1000000000000000000 : ℚ) / (2144099899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (197039547 / 125000000000 : ℚ) + (46323487 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4247340827 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12610]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12610 :
    2 * 160 < 12610 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998473 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12610 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12611 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12611. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12611 : WorldParameters where
  hiddenCharge := (587980323 / 500000000000 : ℝ)
  frame := (626867625257 / 1000000000000 : ℝ)
  moment := (2401835909 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12611 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46241053801 / 31250000000 : ℝ)
    root := (8557106753 / 1000000000000 : ℝ) }

noncomputable def scalar12611 : ScalarCertificate 12611 world12611 agent12611 where
  dimensionLo := 12611
  dimensionHi := 12611
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2144455799 / 1000000000000 : ℝ)
  frameLo := (626867625257 / 1000000000000 : ℝ)
  frameHi := (46241053801 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12611]
  agentFrame_pos := by norm_num only [agent12611]
  worldRadius := (2144455799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12611]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1574966477 / 1000000000000 : ℝ)
  lowerTail := (370293161 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8490686533 / 1000000000000 : ℝ)
  ledger := by
    have h : (587980323 / 500000000000 : ℚ) +
        (2401835909 / 250000000000000000 : ℚ) / (2144455799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1574966477 / 1000000000000 : ℚ) + (370293161 / 200000000000 : ℚ) ≤
        (8490686533 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((587980323 / 500000000000 : ℚ) +
        (2401835909 / 250000000000000000 : ℚ) / (2144455799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1574966477 / 1000000000000 : ℚ) + (370293161 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8490686533 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12611]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12611 :
    2 * 160 < 12611 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999427 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12611 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12612 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12612. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12612 : WorldParameters where
  hiddenCharge := (587958001 / 500000000000 : ℝ)
  frame := (313426791573 / 500000000000 : ℝ)
  moment := (9605352369 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12612 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369920134037 / 250000000000 : ℝ)
    root := (8556404903 / 1000000000000 : ℝ) }

noncomputable def scalar12612 : ScalarCertificate 12612 world12612 agent12612 where
  dimensionLo := 12612
  dimensionHi := 12612
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2144811699 / 1000000000000 : ℝ)
  frameLo := (313426791573 / 500000000000 : ℝ)
  frameHi := (369920134037 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12612]
  agentFrame_pos := by norm_num only [agent12612]
  worldRadius := (2144811699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12612]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1573618001 / 1000000000000 : ℝ)
  lowerTail := (462498399 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8486695071 / 1000000000000 : ℝ)
  ledger := by
    have h : (587958001 / 500000000000 : ℚ) +
        (9605352369 / 1000000000000000000 : ℚ) / (2144811699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1573618001 / 1000000000000 : ℚ) + (462498399 / 250000000000 : ℚ) ≤
        (8486695071 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((587958001 / 500000000000 : ℚ) +
        (9605352369 / 1000000000000000000 : ℚ) / (2144811699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1573618001 / 1000000000000 : ℚ) + (462498399 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8486695071 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12612]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12612 :
    2 * 160 < 12612 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999717 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12612 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12613 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12613. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12613 : WorldParameters where
  hiddenCharge := (1175871369 / 1000000000000 : ℝ)
  frame := (313419771653 / 500000000000 : ℝ)
  moment := (9603361679 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12613 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295929474341 / 200000000000 : ℝ)
    root := (8555703279 / 1000000000000 : ℝ) }

noncomputable def scalar12613 : ScalarCertificate 12613 world12613 agent12613 where
  dimensionLo := 12613
  dimensionHi := 12613
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2145167599 / 1000000000000 : ℝ)
  frameLo := (313419771653 / 500000000000 : ℝ)
  frameHi := (295929474341 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12613]
  agentFrame_pos := by norm_num only [agent12613]
  worldRadius := (2145167599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12613]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1572270883 / 1000000000000 : ℝ)
  lowerTail := (462130697 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (132542299 / 15625000000 : ℝ)
  ledger := by
    have h : (1175871369 / 1000000000000 : ℚ) +
        (9603361679 / 1000000000000000000 : ℚ) / (2145167599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1572270883 / 1000000000000 : ℚ) + (462130697 / 250000000000 : ℚ) ≤
        (132542299 / 15625000000 : ℚ) := by norm_num only
    have hc : (((1175871369 / 1000000000000 : ℚ) +
        (9603361679 / 1000000000000000000 : ℚ) / (2145167599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1572270883 / 1000000000000 : ℚ) + (462130697 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((132542299 / 15625000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12613]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12613 :
    2 * 160 < 12613 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996111 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12613 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12614 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12614. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12614 : WorldParameters where
  hiddenCharge := (1175826749 / 1000000000000 : ℝ)
  frame := (626825505739 / 1000000000000 : ℝ)
  moment := (4800685783 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12614 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739807111177 / 500000000000 : ℝ)
    root := (8555001813 / 1000000000000 : ℝ) }

noncomputable def scalar12614 : ScalarCertificate 12614 world12614 agent12614 where
  dimensionLo := 12614
  dimensionHi := 12614
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2145523499 / 1000000000000 : ℝ)
  frameLo := (626825505739 / 1000000000000 : ℝ)
  frameHi := (739807111177 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12614]
  agentFrame_pos := by norm_num only [agent12614]
  worldRadius := (2145523499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12614]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1570925031 / 1000000000000 : ℝ)
  lowerTail := (1847053281 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4239361269 / 500000000000 : ℝ)
  ledger := by
    have h : (1175826749 / 1000000000000 : ℚ) +
        (4800685783 / 500000000000000000 : ℚ) / (2145523499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1570925031 / 1000000000000 : ℚ) + (1847053281 / 1000000000000 : ℚ) ≤
        (4239361269 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1175826749 / 1000000000000 : ℚ) +
        (4800685783 / 500000000000000000 : ℚ) / (2145523499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1570925031 / 1000000000000 : ℚ) + (1847053281 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4239361269 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12614]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12614 :
    2 * 160 < 12614 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999689 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12614 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12615 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12615. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12615 : WorldParameters where
  hiddenCharge := (58789107 / 50000000000 : ℝ)
  frame := (313405735221 / 500000000000 : ℝ)
  moment := (9599382029 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12615 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739790547011 / 500000000000 : ℝ)
    root := (8554300641 / 1000000000000 : ℝ) }

noncomputable def scalar12615 : ScalarCertificate 12615 world12615 agent12615 where
  dimensionLo := 12615
  dimensionHi := 12615
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2145879399 / 1000000000000 : ℝ)
  frameLo := (313405735221 / 500000000000 : ℝ)
  frameHi := (739790547011 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12615]
  agentFrame_pos := by norm_num only [agent12615]
  worldRadius := (2145879399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12615]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1569580597 / 1000000000000 : ℝ)
  lowerTail := (369117047 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2118685397 / 250000000000 : ℝ)
  ledger := by
    have h : (58789107 / 50000000000 : ℚ) +
        (9599382029 / 1000000000000000000 : ℚ) / (2145879399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1569580597 / 1000000000000 : ℚ) + (369117047 / 200000000000 : ℚ) ≤
        (2118685397 / 250000000000 : ℚ) := by norm_num only
    have hc : (((58789107 / 50000000000 : ℚ) +
        (9599382029 / 1000000000000000000 : ℚ) / (2145879399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1569580597 / 1000000000000 : ℚ) + (369117047 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2118685397 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12615]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12615 :
    2 * 160 < 12615 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998329 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12615 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12616 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12616. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12616 : WorldParameters where
  hiddenCharge := (1175737543 / 1000000000000 : ℝ)
  frame := (125359487483 / 200000000000 : ℝ)
  moment := (2399348267 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12616 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1479547980761 / 1000000000000 : ℝ)
    root := (4276799813 / 500000000000 : ℝ) }

noncomputable def scalar12616 : ScalarCertificate 12616 world12616 agent12616 where
  dimensionLo := 12616
  dimensionHi := 12616
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2146235299 / 1000000000000 : ℝ)
  frameLo := (125359487483 / 200000000000 : ℝ)
  frameHi := (1479547980761 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12616]
  agentFrame_pos := by norm_num only [agent12616]
  worldRadius := (2146235299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12616]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (784118713 / 500000000000 : ℝ)
  lowerTail := (1844118489 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (132355687 / 15625000000 : ℝ)
  ledger := by
    have h : (1175737543 / 1000000000000 : ℚ) +
        (2399348267 / 250000000000000000 : ℚ) / (2146235299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (784118713 / 500000000000 : ℚ) + (1844118489 / 1000000000000 : ℚ) ≤
        (132355687 / 15625000000 : ℚ) := by norm_num only
    have hc : (((1175737543 / 1000000000000 : ℚ) +
        (2399348267 / 250000000000000000 : ℚ) / (2146235299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (784118713 / 500000000000 : ℚ) + (1844118489 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((132355687 / 15625000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12616]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12616 :
    2 * 160 < 12616 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999633 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12616 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12617 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12617. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12617 : WorldParameters where
  hiddenCharge := (587846479 / 500000000000 : ℝ)
  frame := (313391703329 / 500000000000 : ℝ)
  moment := (9595404683 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12617 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46234840451 / 31250000000 : ℝ)
    root := (1069112363 / 125000000000 : ℝ) }

noncomputable def scalar12617 : ScalarCertificate 12617 world12617 agent12617 where
  dimensionLo := 12617
  dimensionHi := 12617
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2146591099 / 1000000000000 : ℝ)
  frameLo := (313391703329 / 500000000000 : ℝ)
  frameHi := (46234840451 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12617]
  agentFrame_pos := by norm_num only [agent12617]
  worldRadius := (2146591099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12617]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (313379121 / 200000000000 : ℝ)
  lowerTail := (1842653133 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (264587189 / 31250000000 : ℝ)
  ledger := by
    have h : (587846479 / 500000000000 : ℚ) +
        (9595404683 / 1000000000000000000 : ℚ) / (2146591099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (313379121 / 200000000000 : ℚ) + (1842653133 / 1000000000000 : ℚ) ≤
        (264587189 / 31250000000 : ℚ) := by norm_num only
    have hc : (((587846479 / 500000000000 : ℚ) +
        (9595404683 / 1000000000000000000 : ℚ) / (2146591099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (313379121 / 200000000000 : ℚ) + (1842653133 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((264587189 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12617]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12617 :
    2 * 160 < 12617 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998547 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12617 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12618 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12618. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12618 : WorldParameters where
  hiddenCharge := (235129677 / 200000000000 : ℝ)
  frame := (62676937817 / 100000000000 : ℝ)
  moment := (9593416873 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12618 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739740908609 / 500000000000 : ℝ)
    root := (427609917 / 50000000000 : ℝ) }

noncomputable def scalar12618 : ScalarCertificate 12618 world12618 agent12618 where
  dimensionLo := 12618
  dimensionHi := 12618
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2146947199 / 1000000000000 : ℝ)
  frameLo := (62676937817 / 100000000000 : ℝ)
  frameHi := (739740908609 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12618]
  agentFrame_pos := by norm_num only [agent12618]
  worldRadius := (2146947199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12618]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (782777647 / 500000000000 : ℝ)
  lowerTail := (920594671 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8462819389 / 1000000000000 : ℝ)
  ledger := by
    have h : (235129677 / 200000000000 : ℚ) +
        (9593416873 / 1000000000000000000 : ℚ) / (2146947199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (782777647 / 500000000000 : ℚ) + (920594671 / 500000000000 : ℚ) ≤
        (8462819389 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((235129677 / 200000000000 : ℚ) +
        (9593416873 / 1000000000000000000 : ℚ) / (2146947199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (782777647 / 500000000000 : ℚ) + (920594671 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8462819389 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12618]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12618 :
    2 * 160 < 12618 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998637 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12618 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12619 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12619. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12619 : WorldParameters where
  hiddenCharge := (73475239 / 62500000000 : ℝ)
  frame := (12535107039 / 20000000000 : ℝ)
  moment := (9591429639 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12619 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739724383457 / 500000000000 : ℝ)
    root := (8551498069 / 1000000000000 : ℝ) }

noncomputable def scalar12619 : ScalarCertificate 12619 world12619 agent12619 where
  dimensionLo := 12619
  dimensionHi := 12619
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2147302999 / 1000000000000 : ℝ)
  frameLo := (12535107039 / 20000000000 : ℝ)
  frameHi := (739724383457 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12619]
  agentFrame_pos := by norm_num only [agent12619]
  worldRadius := (2147302999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12619]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (312843229 / 200000000000 : ℝ)
  lowerTail := (114982921 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4229426213 / 500000000000 : ℝ)
  ledger := by
    have h : (73475239 / 62500000000 : ℚ) +
        (9591429639 / 1000000000000000000 : ℚ) / (2147302999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (312843229 / 200000000000 : ℚ) + (114982921 / 62500000000 : ℚ) ≤
        (4229426213 / 500000000000 : ℚ) := by norm_num only
    have hc : (((73475239 / 62500000000 : ℚ) +
        (9591429639 / 1000000000000000000 : ℚ) / (2147302999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (312843229 / 200000000000 : ℚ) + (114982921 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((4229426213 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12619]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12619 :
    2 * 160 < 12619 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998653 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12619 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12620 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12620. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12620 : WorldParameters where
  hiddenCharge := (587779637 / 500000000000 : ℝ)
  frame := (626741327999 / 1000000000000 : ℝ)
  moment := (479472149 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12620 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369833360843 / 250000000000 : ℝ)
    root := (4275398977 / 500000000000 : ℝ) }

noncomputable def scalar12620 : ScalarCertificate 12620 world12620 agent12620 where
  dimensionLo := 12620
  dimensionHi := 12620
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2147770099 / 1000000000000 : ℝ)
  frameLo := (626741327999 / 1000000000000 : ℝ)
  frameHi := (369833360843 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12620]
  agentFrame_pos := by norm_num only [agent12620]
  worldRadius := (2147770099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12620]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (390648631 / 250000000000 : ℝ)
  lowerTail := (1837902079 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8454026231 / 1000000000000 : ℝ)
  ledger := by
    have h : (587779637 / 500000000000 : ℚ) +
        (479472149 / 50000000000000000 : ℚ) / (2147770099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (390648631 / 250000000000 : ℚ) + (1837902079 / 1000000000000 : ℚ) ≤
        (8454026231 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((587779637 / 500000000000 : ℚ) +
        (479472149 / 50000000000000000 : ℚ) / (2147770099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (390648631 / 250000000000 : ℚ) + (1837902079 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8454026231 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12620]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12620 :
    2 * 160 < 12620 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994319 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12620 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12621 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12621. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12621 : WorldParameters where
  hiddenCharge := (1175514737 / 1000000000000 : ℝ)
  frame := (313363653157 / 500000000000 : ℝ)
  moment := (1917491379 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12621 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295860084819 / 200000000000 : ℝ)
    root := (8550098133 / 1000000000000 : ℝ) }

noncomputable def scalar12621 : ScalarCertificate 12621 world12621 agent12621 where
  dimensionLo := 12621
  dimensionHi := 12621
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2148125999 / 1000000000000 : ℝ)
  frameLo := (313363653157 / 500000000000 : ℝ)
  frameHi := (295860084819 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12621]
  agentFrame_pos := by norm_num only [agent12621]
  worldRadius := (2148125999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12621]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (312251661 / 200000000000 : ℝ)
  lowerTail := (1836442521 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8450066731 / 1000000000000 : ℝ)
  ledger := by
    have h : (1175514737 / 1000000000000 : ℚ) +
        (1917491379 / 200000000000000000 : ℚ) / (2148125999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (312251661 / 200000000000 : ℚ) + (1836442521 / 1000000000000 : ℚ) ≤
        (8450066731 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1175514737 / 1000000000000 : ℚ) +
        (1917491379 / 200000000000000000 : ℚ) / (2148125999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (312251661 / 200000000000 : ℚ) + (1836442521 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8450066731 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12621]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12621 :
    2 * 160 < 12621 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998869 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12621 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12622 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12622. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12622 : WorldParameters where
  hiddenCharge := (1175470211 / 1000000000000 : ℝ)
  frame := (626713286897 / 1000000000000 : ℝ)
  moment := (4792735693 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12622 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (9245421411 / 6250000000 : ℝ)
    root := (2137349617 / 250000000000 : ℝ) }

noncomputable def scalar12622 : ScalarCertificate 12622 world12622 agent12622 where
  dimensionLo := 12622
  dimensionHi := 12622
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2148481999 / 1000000000000 : ℝ)
  frameLo := (626713286897 / 1000000000000 : ℝ)
  frameHi := (9245421411 / 6250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12622]
  agentFrame_pos := by norm_num only [agent12622]
  worldRadius := (2148481999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12622]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (77996173 / 50000000000 : ℝ)
  lowerTail := (458746097 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8446110601 / 1000000000000 : ℝ)
  ledger := by
    have h : (1175470211 / 1000000000000 : ℚ) +
        (4792735693 / 500000000000000000 : ℚ) / (2148481999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77996173 / 50000000000 : ℚ) + (458746097 / 250000000000 : ℚ) ≤
        (8446110601 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1175470211 / 1000000000000 : ℚ) +
        (4792735693 / 500000000000000000 : ℚ) / (2148481999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77996173 / 50000000000 : ℚ) + (458746097 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8446110601 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12622]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12622 :
    2 * 160 < 12622 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998723 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12622 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12623 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12623. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12623 : WorldParameters where
  hiddenCharge := (1175425697 / 1000000000000 : ℝ)
  frame := (125339853949 / 200000000000 : ℝ)
  moment := (9583486451 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12623 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369808612089 / 250000000000 : ℝ)
    root := (1709739819 / 200000000000 : ℝ) }

noncomputable def scalar12623 : ScalarCertificate 12623 world12623 agent12623 where
  dimensionLo := 12623
  dimensionHi := 12623
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2148837999 / 1000000000000 : ℝ)
  frameLo := (125339853949 / 200000000000 : ℝ)
  frameHi := (369808612089 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12623]
  agentFrame_pos := by norm_num only [agent12623]
  worldRadius := (2148837999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12623]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1558590019 / 1000000000000 : ℝ)
  lowerTail := (916763851 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4221079043 / 500000000000 : ℝ)
  ledger := by
    have h : (1175425697 / 1000000000000 : ℚ) +
        (9583486451 / 1000000000000000000 : ℚ) / (2148837999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1558590019 / 1000000000000 : ℚ) + (916763851 / 500000000000 : ℚ) ≤
        (4221079043 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1175425697 / 1000000000000 : ℚ) +
        (9583486451 / 1000000000000000000 : ℚ) / (2148837999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1558590019 / 1000000000000 : ℚ) + (916763851 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4221079043 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12623]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12623 :
    2 * 160 < 12623 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (171874957 / 15625000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12623 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12624 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12624. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12624 : WorldParameters where
  hiddenCharge := (293845299 / 250000000000 : ℝ)
  frame := (626685254859 / 1000000000000 : ℝ)
  moment := (958150209 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12624 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1479201485939 / 1000000000000 : ℝ)
    root := (4273999939 / 500000000000 : ℝ) }

noncomputable def scalar12624 : ScalarCertificate 12624 world12624 agent12624 where
  dimensionLo := 12624
  dimensionHi := 12624
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2149193899 / 1000000000000 : ℝ)
  frameLo := (626685254859 / 1000000000000 : ℝ)
  frameHi := (1479201485939 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12624]
  agentFrame_pos := by norm_num only [agent12624]
  worldRadius := (2149193899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12624]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1557257737 / 1000000000000 : ℝ)
  lowerTail := (458018051 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8438208873 / 1000000000000 : ℝ)
  ledger := by
    have h : (293845299 / 250000000000 : ℚ) +
        (958150209 / 100000000000000000 : ℚ) / (2149193899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1557257737 / 1000000000000 : ℚ) + (458018051 / 250000000000 : ℚ) ≤
        (8438208873 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((293845299 / 250000000000 : ℚ) +
        (958150209 / 100000000000000000 : ℚ) / (2149193899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1557257737 / 1000000000000 : ℚ) + (458018051 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8438208873 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12624]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12624 :
    2 * 160 < 12624 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999413 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12624 {← IO.monoMsNow}" : IO Unit)
