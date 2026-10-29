import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12750 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12750. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12750 : WorldParameters where
  hiddenCharge := (1169867439 / 1000000000000 : ℝ)
  frame := (124987461753 / 200000000000 : ℝ)
  moment := (4667997919 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12750 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294815202547 / 200000000000 : ℝ)
    root := (4230821097 / 500000000000 : ℝ) }

noncomputable def scalar12750 : ScalarCertificate 12750 world12750 agent12750 where
  dimensionLo := 12750
  dimensionHi := 12750
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2195629499 / 1000000000000 : ℝ)
  frameLo := (124987461753 / 200000000000 : ℝ)
  frameHi := (294815202547 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12750]
  agentFrame_pos := by norm_num only [agent12750]
  worldRadius := (2195629499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12750]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (698035961 / 500000000000 : ℝ)
  lowerTail := (1654679677 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7956376661 / 1000000000000 : ℝ)
  ledger := by
    have h : (1169867439 / 1000000000000 : ℚ) +
        (4667997919 / 500000000000000000 : ℚ) / (2195629499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (698035961 / 500000000000 : ℚ) + (1654679677 / 1000000000000 : ℚ) ≤
        (7956376661 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1169867439 / 1000000000000 : ℚ) +
        (4667997919 / 500000000000000000 : ℚ) / (2195629499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (698035961 / 500000000000 : ℚ) + (1654679677 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7956376661 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12750]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12750 :
    2 * 160 < 12750 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999801 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12750 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12751 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12751. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12751 : WorldParameters where
  hiddenCharge := (116982441 / 100000000000 : ℝ)
  frame := (624923576927 / 1000000000000 : ℝ)
  moment := (9334082713 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12751 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474044355937 / 1000000000000 : ℝ)
    root := (2115242547 / 250000000000 : ℝ) }

noncomputable def scalar12751 : ScalarCertificate 12751 world12751 agent12751 where
  dimensionLo := 12751
  dimensionHi := 12751
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2195987599 / 1000000000000 : ℝ)
  frameLo := (624923576927 / 1000000000000 : ℝ)
  frameHi := (1474044355937 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12751]
  agentFrame_pos := by norm_num only [agent12751]
  worldRadius := (2195987599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12751]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1394896653 / 1000000000000 : ℝ)
  lowerTail := (826693071 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7952836553 / 1000000000000 : ℝ)
  ledger := by
    have h : (116982441 / 100000000000 : ℚ) +
        (9334082713 / 1000000000000000000 : ℚ) / (2195987599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1394896653 / 1000000000000 : ℚ) + (826693071 / 500000000000 : ℚ) ≤
        (7952836553 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((116982441 / 100000000000 : ℚ) +
        (9334082713 / 1000000000000000000 : ℚ) / (2195987599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1394896653 / 1000000000000 : ℚ) + (826693071 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7952836553 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12751]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12751 :
    2 * 160 < 12751 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999711 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12751 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12752 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12752. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12752 : WorldParameters where
  hiddenCharge := (73111337 / 62500000000 : ℝ)
  frame := (624909847281 / 1000000000000 : ℝ)
  moment := (1866434027 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12752 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294802541407 / 200000000000 : ℝ)
    root := (8460298453 / 1000000000000 : ℝ) }

noncomputable def scalar12752 : ScalarCertificate 12752 world12752 agent12752 where
  dimensionLo := 12752
  dimensionHi := 12752
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2196345799 / 1000000000000 : ℝ)
  frameLo := (624909847281 / 1000000000000 : ℝ)
  frameHi := (294802541407 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12752]
  agentFrame_pos := by norm_num only [agent12752]
  worldRadius := (2196345799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12752]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (174215329 / 125000000000 : ℝ)
  lowerTail := (1652093897 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7949299499 / 1000000000000 : ℝ)
  ledger := by
    have h : (73111337 / 62500000000 : ℚ) +
        (1866434027 / 200000000000000000 : ℚ) / (2196345799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (174215329 / 125000000000 : ℚ) + (1652093897 / 1000000000000 : ℚ) ≤
        (7949299499 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((73111337 / 62500000000 : ℚ) +
        (1866434027 / 200000000000000000 : ℚ) / (2196345799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (174215329 / 125000000000 : ℚ) + (1652093897 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7949299499 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12752]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12752 :
    2 * 160 < 12752 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999817 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12752 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12753 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12753. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12753 : WorldParameters where
  hiddenCharge := (584869193 / 500000000000 : ℝ)
  frame := (624896119827 / 1000000000000 : ℝ)
  moment := (1866051621 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12753 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473981083733 / 1000000000000 : ℝ)
    root := (2114906731 / 250000000000 : ℝ) }

noncomputable def scalar12753 : ScalarCertificate 12753 world12753 agent12753 where
  dimensionLo := 12753
  dimensionHi := 12753
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2196703799 / 1000000000000 : ℝ)
  frameLo := (624896119827 / 1000000000000 : ℝ)
  frameHi := (1473981083733 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12753]
  agentFrame_pos := by norm_num only [agent12753]
  worldRadius := (2196703799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12753]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (696274813 / 500000000000 : ℝ)
  lowerTail := (103175169 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7945765557 / 1000000000000 : ℝ)
  ledger := by
    have h : (584869193 / 500000000000 : ℚ) +
        (1866051621 / 200000000000000000 : ℚ) / (2196703799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (696274813 / 500000000000 : ℚ) + (103175169 / 62500000000 : ℚ) ≤
        (7945765557 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((584869193 / 500000000000 : ℚ) +
        (1866051621 / 200000000000000000 : ℚ) / (2196703799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (696274813 / 500000000000 : ℚ) + (103175169 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7945765557 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12753]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12753 :
    2 * 160 < 12753 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995341 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12753 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12754 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12754. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12754 : WorldParameters where
  hiddenCharge := (1169695391 / 1000000000000 : ℝ)
  frame := (124976478913 / 200000000000 : ℝ)
  moment := (4664173311 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12754 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736974737107 / 500000000000 : ℝ)
    root := (4229477767 / 500000000000 : ℝ) }

noncomputable def scalar12754 : ScalarCertificate 12754 world12754 agent12754 where
  dimensionLo := 12754
  dimensionHi := 12754
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2197061899 / 1000000000000 : ℝ)
  frameLo := (124976478913 / 200000000000 : ℝ)
  frameHi := (736974737107 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12754]
  agentFrame_pos := by norm_num only [agent12754]
  worldRadius := (2197061899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12754]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (695688891 / 500000000000 : ℝ)
  lowerTail := (20618909 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7942234499 / 1000000000000 : ℝ)
  ledger := by
    have h : (1169695391 / 1000000000000 : ℚ) +
        (4664173311 / 500000000000000000 : ℚ) / (2197061899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (695688891 / 500000000000 : ℚ) + (20618909 / 12500000000 : ℚ) ≤
        (7942234499 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1169695391 / 1000000000000 : ℚ) +
        (4664173311 / 500000000000000000 : ℚ) / (2197061899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (695688891 / 500000000000 : ℚ) + (20618909 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7942234499 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12754]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12754 :
    2 * 160 < 12754 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995253 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12754 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12755 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12755. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12755 : WorldParameters where
  hiddenCharge := (1169652407 / 1000000000000 : ℝ)
  frame := (624868671493 / 1000000000000 : ℝ)
  moment := (9326435687 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12755 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473917878469 / 1000000000000 : ℝ)
    root := (66080347 / 7812500000 : ℝ) }

noncomputable def scalar12755 : ScalarCertificate 12755 world12755 agent12755 where
  dimensionLo := 12755
  dimensionHi := 12755
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2197419999 / 1000000000000 : ℝ)
  frameLo := (624868671493 / 1000000000000 : ℝ)
  frameHi := (1473917878469 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12755]
  agentFrame_pos := by norm_num only [agent12755]
  worldRadius := (2197419999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12755]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1390207123 / 1000000000000 : ℝ)
  lowerTail := (1648223961 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1587741309 / 200000000000 : ℝ)
  ledger := by
    have h : (1169652407 / 1000000000000 : ℚ) +
        (9326435687 / 1000000000000000000 : ℚ) / (2197419999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1390207123 / 1000000000000 : ℚ) + (1648223961 / 1000000000000 : ℚ) ≤
        (1587741309 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1169652407 / 1000000000000 : ℚ) +
        (9326435687 / 1000000000000000000 : ℚ) / (2197419999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1390207123 / 1000000000000 : ℚ) + (1648223961 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1587741309 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12755]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12755 :
    2 * 160 < 12755 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999401 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12755 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12756 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12756. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12756 : WorldParameters where
  hiddenCharge := (233921887 / 200000000000 : ℝ)
  frame := (156213737653 / 250000000000 : ℝ)
  moment := (4662262649 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12756 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184235787799 / 125000000000 : ℝ)
    root := (2114403359 / 250000000000 : ℝ) }

noncomputable def scalar12756 : ScalarCertificate 12756 world12756 agent12756 where
  dimensionLo := 12756
  dimensionHi := 12756
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2197778099 / 1000000000000 : ℝ)
  frameLo := (156213737653 / 250000000000 : ℝ)
  frameHi := (184235787799 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12756]
  agentFrame_pos := by norm_num only [agent12756]
  worldRadius := (2197778099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12756]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (347259391 / 250000000000 : ℝ)
  lowerTail := (1646936349 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (317407261 / 40000000000 : ℝ)
  ledger := by
    have h : (233921887 / 200000000000 : ℚ) +
        (4662262649 / 500000000000000000 : ℚ) / (2197778099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (347259391 / 250000000000 : ℚ) + (1646936349 / 1000000000000 : ℚ) ≤
        (317407261 / 40000000000 : ℚ) := by norm_num only
    have hc : (((233921887 / 200000000000 : ℚ) +
        (4662262649 / 500000000000000000 : ℚ) / (2197778099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (347259391 / 250000000000 : ℚ) + (1646936349 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((317407261 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12756]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12756 :
    2 * 160 < 12756 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999953 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12756 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12757 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12757. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12757 : WorldParameters where
  hiddenCharge := (584783237 / 500000000000 : ℝ)
  frame := (7810515399 / 12500000000 : ℝ)
  moment := (291331733 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12757 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58954189839 / 40000000000 : ℝ)
    root := (1057117841 / 125000000000 : ℝ) }

noncomputable def scalar12757 : ScalarCertificate 12757 world12757 agent12757 where
  dimensionLo := 12757
  dimensionHi := 12757
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2198136299 / 1000000000000 : ℝ)
  frameLo := (7810515399 / 12500000000 : ℝ)
  frameHi := (58954189839 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12757]
  agentFrame_pos := by norm_num only [agent12757]
  worldRadius := (2198136299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12757]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1387869297 / 1000000000000 : ℝ)
  lowerTail := (1645650083 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (396582983 / 50000000000 : ℝ)
  ledger := by
    have h : (584783237 / 500000000000 : ℚ) +
        (291331733 / 31250000000000000 : ℚ) / (2198136299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1387869297 / 1000000000000 : ℚ) + (1645650083 / 1000000000000 : ℚ) ≤
        (396582983 / 50000000000 : ℚ) := by norm_num only
    have hc : (((584783237 / 500000000000 : ℚ) +
        (291331733 / 31250000000000000 : ℚ) / (2198136299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1387869297 / 1000000000000 : ℚ) + (1645650083 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((396582983 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12757]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12757 :
    2 * 160 < 12757 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998257 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12757 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12758 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12758. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12758 : WorldParameters where
  hiddenCharge := (292380881 / 250000000000 : ℝ)
  frame := (624827515417 / 1000000000000 : ℝ)
  moment := (9320706161 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12758 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473823209207 / 1000000000000 : ℝ)
    root := (338250889 / 40000000000 : ℝ) }

noncomputable def scalar12758 : ScalarCertificate 12758 world12758 agent12758 where
  dimensionLo := 12758
  dimensionHi := 12758
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2198494299 / 1000000000000 : ℝ)
  frameLo := (624827515417 / 1000000000000 : ℝ)
  frameHi := (1473823209207 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12758]
  agentFrame_pos := by norm_num only [agent12758]
  worldRadius := (2198494299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12758]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (693351007 / 500000000000 : ℝ)
  lowerTail := (1644364831 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3964070417 / 500000000000 : ℝ)
  ledger := by
    have h : (292380881 / 250000000000 : ℚ) +
        (9320706161 / 1000000000000000000 : ℚ) / (2198494299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (693351007 / 500000000000 : ℚ) + (1644364831 / 1000000000000 : ℚ) ≤
        (3964070417 / 500000000000 : ℚ) := by norm_num only
    have hc : (((292380881 / 250000000000 : ℚ) +
        (9320706161 / 1000000000000000000 : ℚ) / (2198494299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (693351007 / 500000000000 : ℚ) + (1644364831 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3964070417 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12758]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12758 :
    2 * 160 < 12758 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994109 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12758 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12759 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12759. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12759 : WorldParameters where
  hiddenCharge := (584740293 / 500000000000 : ℝ)
  frame := (624813801103 / 1000000000000 : ℝ)
  moment := (2329699353 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12759 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58951667211 / 40000000000 : ℝ)
    root := (422780093 / 50000000000 : ℝ) }

noncomputable def scalar12759 : ScalarCertificate 12759 world12759 agent12759 where
  dimensionLo := 12759
  dimensionHi := 12759
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2198852399 / 1000000000000 : ℝ)
  frameLo := (624813801103 / 1000000000000 : ℝ)
  frameHi := (58951667211 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12759]
  agentFrame_pos := by norm_num only [agent12759]
  worldRadius := (2198852399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12759]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1385535861 / 1000000000000 : ℝ)
  lowerTail := (1643080751 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (396231241 / 50000000000 : ℝ)
  ledger := by
    have h : (584740293 / 500000000000 : ℚ) +
        (2329699353 / 250000000000000000 : ℚ) / (2198852399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1385535861 / 1000000000000 : ℚ) + (1643080751 / 1000000000000 : ℚ) ≤
        (396231241 / 50000000000 : ℚ) := by norm_num only
    have hc : (((584740293 / 500000000000 : ℚ) +
        (2329699353 / 250000000000000000 : ℚ) / (2198852399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1385535861 / 1000000000000 : ℚ) + (1643080751 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((396231241 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12759]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12759 :
    2 * 160 < 12759 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999831 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12759 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12760 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12760. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12760 : WorldParameters where
  hiddenCharge := (1169437659 / 1000000000000 : ℝ)
  frame := (624800088977 / 1000000000000 : ℝ)
  moment := (931688921 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12760 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147367953979 / 100000000000 : ℝ)
    root := (4227465883 / 500000000000 : ℝ) }

noncomputable def scalar12760 : ScalarCertificate 12760 world12760 agent12760 where
  dimensionLo := 12760
  dimensionHi := 12760
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2199323699 / 1000000000000 : ℝ)
  frameLo := (624800088977 / 1000000000000 : ℝ)
  frameHi := (147367953979 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12760]
  agentFrame_pos := by norm_num only [agent12760]
  worldRadius := (2199323699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12760]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (692061039 / 500000000000 : ℝ)
  lowerTail := (820738167 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7920343233 / 1000000000000 : ℝ)
  ledger := by
    have h : (1169437659 / 1000000000000 : ℚ) +
        (931688921 / 100000000000000000 : ℚ) / (2199323699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (692061039 / 500000000000 : ℚ) + (820738167 / 500000000000 : ℚ) ≤
        (7920343233 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1169437659 / 1000000000000 : ℚ) +
        (931688921 / 100000000000000000 : ℚ) / (2199323699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (692061039 / 500000000000 : ℚ) + (820738167 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7920343233 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12760]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12760 :
    2 * 160 < 12760 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999283 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12760 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12761 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12761. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12761 : WorldParameters where
  hiddenCharge := (1169394743 / 1000000000000 : ℝ)
  frame := (312393189519 / 500000000000 : ℝ)
  moment := (9314981553 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12761 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368412012763 / 250000000000 : ℝ)
    root := (845426181 / 100000000000 : ℝ) }

noncomputable def scalar12761 : ScalarCertificate 12761 world12761 agent12761 where
  dimensionLo := 12761
  dimensionHi := 12761
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2199681899 / 1000000000000 : ℝ)
  frameLo := (312393189519 / 500000000000 : ℝ)
  frameHi := (368412012763 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12761]
  agentFrame_pos := by norm_num only [agent12761]
  worldRadius := (2199681899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12761]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (691479239 / 500000000000 : ℝ)
  lowerTail := (820097471 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (39584169 / 5000000000 : ℝ)
  ledger := by
    have h : (1169394743 / 1000000000000 : ℚ) +
        (9314981553 / 1000000000000000000 : ℚ) / (2199681899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (691479239 / 500000000000 : ℚ) + (820097471 / 500000000000 : ℚ) ≤
        (39584169 / 5000000000 : ℚ) := by norm_num only
    have hc : (((1169394743 / 1000000000000 : ℚ) +
        (9314981553 / 1000000000000000000 : ℚ) / (2199681899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (691479239 / 500000000000 : ℚ) + (820097471 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((39584169 / 5000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12761]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12761 :
    2 * 160 < 12761 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999583 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12761 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12762 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12762. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12762 : WorldParameters where
  hiddenCharge := (1169351839 / 1000000000000 : ℝ)
  frame := (312386335643 / 500000000000 : ℝ)
  moment := (4656537221 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12762 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736808290963 / 500000000000 : ℝ)
    root := (67628737 / 8000000000 : ℝ) }

noncomputable def scalar12762 : ScalarCertificate 12762 world12762 agent12762 where
  dimensionLo := 12762
  dimensionHi := 12762
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2200039999 / 1000000000000 : ℝ)
  frameLo := (312386335643 / 500000000000 : ℝ)
  frameHi := (736808290963 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12762]
  agentFrame_pos := by norm_num only [agent12762]
  worldRadius := (2200039999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12762]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1381795997 / 1000000000000 : ℝ)
  lowerTail := (819457353 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7913327503 / 1000000000000 : ℝ)
  ledger := by
    have h : (1169351839 / 1000000000000 : ℚ) +
        (4656537221 / 500000000000000000 : ℚ) / (2200039999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1381795997 / 1000000000000 : ℚ) + (819457353 / 500000000000 : ℚ) ≤
        (7913327503 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1169351839 / 1000000000000 : ℚ) +
        (4656537221 / 500000000000000000 : ℚ) / (2200039999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1381795997 / 1000000000000 : ℚ) + (819457353 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7913327503 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12762]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12762 :
    2 * 160 < 12762 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997111 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12762 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12763 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12763. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12763 : WorldParameters where
  hiddenCharge := (584654473 / 500000000000 : ℝ)
  frame := (15618974143 / 25000000000 : ℝ)
  moment := (2327791969 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12763 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473585126503 / 1000000000000 : ℝ)
    root := (4226461289 / 500000000000 : ℝ) }

noncomputable def scalar12763 : ScalarCertificate 12763 world12763 agent12763 where
  dimensionLo := 12763
  dimensionHi := 12763
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2200398299 / 1000000000000 : ℝ)
  frameLo := (15618974143 / 25000000000 : ℝ)
  frameHi := (1473585126503 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12763]
  agentFrame_pos := by norm_num only [agent12763]
  worldRadius := (2200398299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12763]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (345158687 / 250000000000 : ℝ)
  lowerTail := (818817879 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (123591001 / 15625000000 : ℝ)
  ledger := by
    have h : (584654473 / 500000000000 : ℚ) +
        (2327791969 / 250000000000000000 : ℚ) / (2200398299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (345158687 / 250000000000 : ℚ) + (818817879 / 500000000000 : ℚ) ≤
        (123591001 / 15625000000 : ℚ) := by norm_num only
    have hc : (((584654473 / 500000000000 : ℚ) +
        (2327791969 / 250000000000000000 : ℚ) / (2200398299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (345158687 / 250000000000 : ℚ) + (818817879 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((123591001 / 15625000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12763]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12763 :
    2 * 160 < 12763 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999523 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12763 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12764 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12764. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12764 : WorldParameters where
  hiddenCharge := (73079129 / 62500000000 : ℝ)
  frame := (31237263117 / 50000000000 : ℝ)
  moment := (290914433 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12764 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368388421193 / 250000000000 : ℝ)
    root := (8452253301 / 1000000000000 : ℝ) }

noncomputable def scalar12764 : ScalarCertificate 12764 world12764 agent12764 where
  dimensionLo := 12764
  dimensionHi := 12764
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2200756399 / 1000000000000 : ℝ)
  frameLo := (31237263117 / 50000000000 : ℝ)
  frameHi := (368388421193 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12764]
  agentFrame_pos := by norm_num only [agent12764]
  worldRadius := (2200756399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12764]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (275894901 / 200000000000 : ℝ)
  lowerTail := (818178921 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3953161849 / 500000000000 : ℝ)
  ledger := by
    have h : (73079129 / 62500000000 : ℚ) +
        (290914433 / 31250000000000000 : ℚ) / (2200756399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (275894901 / 200000000000 : ℚ) + (818178921 / 500000000000 : ℚ) ≤
        (3953161849 / 500000000000 : ℚ) := by norm_num only
    have hc : (((73079129 / 62500000000 : ℚ) +
        (290914433 / 31250000000000000 : ℚ) / (2200756399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (275894901 / 200000000000 : ℚ) + (818178921 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3953161849 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12764]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12764 :
    2 * 160 < 12764 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999917 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12764 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12765 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12765. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12765 : WorldParameters where
  hiddenCharge := (584611597 / 500000000000 : ℝ)
  frame := (312365780573 / 500000000000 : ℝ)
  moment := (9307356381 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12765 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473522268529 / 1000000000000 : ℝ)
    root := (4225792081 / 500000000000 : ℝ) }

noncomputable def scalar12765 : ScalarCertificate 12765 world12765 agent12765 where
  dimensionLo := 12765
  dimensionHi := 12765
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2201114599 / 1000000000000 : ℝ)
  frameLo := (312365780573 / 500000000000 : ℝ)
  frameHi := (1473522268529 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12765]
  agentFrame_pos := by norm_num only [agent12765]
  worldRadius := (2201114599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12765]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (68915773 / 50000000000 : ℝ)
  lowerTail := (817540591 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7902826297 / 1000000000000 : ℝ)
  ledger := by
    have h : (584611597 / 500000000000 : ℚ) +
        (9307356381 / 1000000000000000000 : ℚ) / (2201114599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (68915773 / 50000000000 : ℚ) + (817540591 / 500000000000 : ℚ) ≤
        (7902826297 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((584611597 / 500000000000 : ℚ) +
        (9307356381 / 1000000000000000000 : ℚ) / (2201114599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (68915773 / 50000000000 : ℚ) + (817540591 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7902826297 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12765]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12765 :
    2 * 160 < 12765 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995173 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12765 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12766 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12766. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12766 : WorldParameters where
  hiddenCharge := (584590167 / 500000000000 : ℝ)
  frame := (124943572427 / 200000000000 : ℝ)
  moment := (9305451451 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12766 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473490865961 / 1000000000000 : ℝ)
    root := (8450915293 / 1000000000000 : ℝ) }

noncomputable def scalar12766 : ScalarCertificate 12766 world12766 agent12766 where
  dimensionLo := 12766
  dimensionHi := 12766
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2201472699 / 1000000000000 : ℝ)
  frameLo := (124943572427 / 200000000000 : ℝ)
  frameHi := (1473490865961 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12766]
  agentFrame_pos := by norm_num only [agent12766]
  worldRadius := (2201472699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12766]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (688578751 / 500000000000 : ℝ)
  lowerTail := (1633805643 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3949665981 / 500000000000 : ℝ)
  ledger := by
    have h : (584590167 / 500000000000 : ℚ) +
        (9305451451 / 1000000000000000000 : ℚ) / (2201472699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (688578751 / 500000000000 : ℚ) + (1633805643 / 1000000000000 : ℚ) ≤
        (3949665981 / 500000000000 : ℚ) := by norm_num only
    have hc : (((584590167 / 500000000000 : ℚ) +
        (9305451451 / 1000000000000000000 : ℚ) / (2201472699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (688578751 / 500000000000 : ℚ) + (1633805643 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3949665981 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12766]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12766 :
    2 * 160 < 12766 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997029 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12766 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12767 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12767. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12767 : WorldParameters where
  hiddenCharge := (584568743 / 500000000000 : ℝ)
  frame := (624704165309 / 1000000000000 : ℝ)
  moment := (4651773533 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12767 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (73672973853 / 50000000000 : ℝ)
    root := (8450246561 / 1000000000000 : ℝ) }

noncomputable def scalar12767 : ScalarCertificate 12767 world12767 agent12767 where
  dimensionLo := 12767
  dimensionHi := 12767
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2201830899 / 1000000000000 : ℝ)
  frameLo := (624704165309 / 1000000000000 : ℝ)
  frameHi := (73672973853 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12767]
  agentFrame_pos := by norm_num only [agent12767]
  worldRadius := (2201830899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12767]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (86000043 / 62500000000 : ℝ)
  lowerTail := (326506259 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3947920237 / 500000000000 : ℝ)
  ledger := by
    have h : (584568743 / 500000000000 : ℚ) +
        (4651773533 / 500000000000000000 : ℚ) / (2201830899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (86000043 / 62500000000 : ℚ) + (326506259 / 200000000000 : ℚ) ≤
        (3947920237 / 500000000000 : ℚ) := by norm_num only
    have hc : (((584568743 / 500000000000 : ℚ) +
        (4651773533 / 500000000000000000 : ℚ) / (2201830899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (86000043 / 62500000000 : ℚ) + (326506259 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3947920237 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12767]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12767 :
    2 * 160 < 12767 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999261 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12767 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12768 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12768. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12768 : WorldParameters where
  hiddenCharge := (23381893 / 20000000000 : ℝ)
  frame := (624690470667 / 1000000000000 : ℝ)
  moment := (4650821613 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12768 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473428107717 / 1000000000000 : ℝ)
    root := (8449578099 / 1000000000000 : ℝ) }

noncomputable def scalar12768 : ScalarCertificate 12768 world12768 agent12768 where
  dimensionLo := 12768
  dimensionHi := 12768
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2202189099 / 1000000000000 : ℝ)
  frameLo := (624690470667 / 1000000000000 : ℝ)
  frameHi := (1473428107717 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12768]
  agentFrame_pos := by norm_num only [agent12768]
  worldRadius := (2202189099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12768]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1374845067 / 1000000000000 : ℝ)
  lowerTail := (407814547 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3946176051 / 500000000000 : ℝ)
  ledger := by
    have h : (23381893 / 20000000000 : ℚ) +
        (4650821613 / 500000000000000000 : ℚ) / (2202189099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1374845067 / 1000000000000 : ℚ) + (407814547 / 250000000000 : ℚ) ≤
        (3946176051 / 500000000000 : ℚ) := by norm_num only
    have hc : (((23381893 / 20000000000 : ℚ) +
        (4650821613 / 500000000000000000 : ℚ) / (2202189099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1374845067 / 1000000000000 : ℚ) + (407814547 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3946176051 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12768]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12768 :
    2 * 160 < 12768 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997857 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12768 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12769 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12769. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12769 : WorldParameters where
  hiddenCharge := (73065739 / 62500000000 : ℝ)
  frame := (624676778207 / 1000000000000 : ℝ)
  moment := (9299739929 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12769 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473396752023 / 1000000000000 : ℝ)
    root := (8448909841 / 1000000000000 : ℝ) }

noncomputable def scalar12769 : ScalarCertificate 12769 world12769 agent12769 where
  dimensionLo := 12769
  dimensionHi := 12769
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2202547299 / 1000000000000 : ℝ)
  frameLo := (624676778207 / 1000000000000 : ℝ)
  frameHi := (1473396752023 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12769]
  agentFrame_pos := by norm_num only [agent12769]
  worldRadius := (2202547299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12769]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (686845279 / 500000000000 : ℝ)
  lowerTail := (1629986233 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (197221667 / 25000000000 : ℝ)
  ledger := by
    have h : (73065739 / 62500000000 : ℚ) +
        (9299739929 / 1000000000000000000 : ℚ) / (2202547299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (686845279 / 500000000000 : ℚ) + (1629986233 / 1000000000000 : ℚ) ≤
        (197221667 / 25000000000 : ℚ) := by norm_num only
    have hc : (((73065739 / 62500000000 : ℚ) +
        (9299739929 / 1000000000000000000 : ℚ) / (2202547299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (686845279 / 500000000000 : ℚ) + (1629986233 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((197221667 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12769]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12769 :
    2 * 160 < 12769 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (274999961 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12769 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12770 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12770. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12770 : WorldParameters where
  hiddenCharge := (116900901 / 100000000000 : ℝ)
  frame := (62466308793 / 100000000000 : ℝ)
  moment := (9297837177 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12770 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473284894659 / 1000000000000 : ℝ)
    root := (8448241719 / 1000000000000 : ℝ) }

noncomputable def scalar12770 : ScalarCertificate 12770 world12770 agent12770 where
  dimensionLo := 12770
  dimensionHi := 12770
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2203018699 / 1000000000000 : ℝ)
  frameLo := (62466308793 / 100000000000 : ℝ)
  frameHi := (1473284894659 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12770]
  agentFrame_pos := by norm_num only [agent12770]
  worldRadius := (2203018699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12770]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (137229047 / 100000000000 : ℝ)
  lowerTail := (814198221 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7884621627 / 1000000000000 : ℝ)
  ledger := by
    have h : (116900901 / 100000000000 : ℚ) +
        (9297837177 / 1000000000000000000 : ℚ) / (2203018699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (137229047 / 100000000000 : ℚ) + (814198221 / 500000000000 : ℚ) ≤
        (7884621627 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((116900901 / 100000000000 : ℚ) +
        (9297837177 / 1000000000000000000 : ℚ) / (2203018699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (137229047 / 100000000000 : ℚ) + (814198221 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7884621627 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12770]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12770 :
    2 * 160 < 12770 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (274999957 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12770 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12771 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12771. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12771 : WorldParameters where
  hiddenCharge := (1168966207 / 1000000000000 : ℝ)
  frame := (124929879967 / 200000000000 : ℝ)
  moment := (9295934969 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12771 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147325357897 / 100000000000 : ℝ)
    root := (8447573801 / 1000000000000 : ℝ) }

noncomputable def scalar12771 : ScalarCertificate 12771 world12771 agent12771 where
  dimensionLo := 12771
  dimensionHi := 12771
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2203376999 / 1000000000000 : ℝ)
  frameLo := (124929879967 / 200000000000 : ℝ)
  frameHi := (147325357897 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12771]
  agentFrame_pos := by norm_num only [agent12771]
  worldRadius := (2203376999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12771]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (10712019 / 7812500000 : ℝ)
  lowerTail := (406781773 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (492571413 / 62500000000 : ℝ)
  ledger := by
    have h : (1168966207 / 1000000000000 : ℚ) +
        (9295934969 / 1000000000000000000 : ℚ) / (2203376999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (10712019 / 7812500000 : ℚ) + (406781773 / 250000000000 : ℚ) ≤
        (492571413 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1168966207 / 1000000000000 : ℚ) +
        (9295934969 / 1000000000000000000 : ℚ) / (2203376999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (10712019 / 7812500000 : ℚ) + (406781773 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((492571413 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12771]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12771 :
    2 * 160 < 12771 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995209 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12771 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12772 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12772. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12772 : WorldParameters where
  hiddenCharge := (146115427 / 125000000000 : ℝ)
  frame := (624635713921 / 1000000000000 : ℝ)
  moment := (1858806661 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12772 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184152784613 / 125000000000 : ℝ)
    root := (1055863269 / 125000000000 : ℝ) }

noncomputable def scalar12772 : ScalarCertificate 12772 world12772 agent12772 where
  dimensionLo := 12772
  dimensionHi := 12772
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2203735199 / 1000000000000 : ℝ)
  frameLo := (624635713921 / 1000000000000 : ℝ)
  frameHi := (184152784613 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12772]
  agentFrame_pos := by norm_num only [agent12772]
  worldRadius := (2203735199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12772]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (54799499 / 40000000000 : ℝ)
  lowerTail := (325171771 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3938833319 / 500000000000 : ℝ)
  ledger := by
    have h : (146115427 / 125000000000 : ℚ) +
        (1858806661 / 200000000000000000 : ℚ) / (2203735199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (54799499 / 40000000000 : ℚ) + (325171771 / 200000000000 : ℚ) ≤
        (3938833319 / 500000000000 : ℚ) := by norm_num only
    have hc : (((146115427 / 125000000000 : ℚ) +
        (1858806661 / 200000000000000000 : ℚ) / (2203735199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (54799499 / 40000000000 : ℚ) + (325171771 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3938833319 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12772]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12772 :
    2 * 160 < 12772 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997693 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12772 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12773 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12773. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12773 : WorldParameters where
  hiddenCharge := (233776127 / 200000000000 : ℝ)
  frame := (156155507547 / 250000000000 : ℝ)
  moment := (1161516523 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12773 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473190988451 / 1000000000000 : ℝ)
    root := (105577983 / 12500000000 : ℝ) }

noncomputable def scalar12773 : ScalarCertificate 12773 world12773 agent12773 where
  dimensionLo := 12773
  dimensionHi := 12773
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2204093499 / 1000000000000 : ℝ)
  frameLo := (156155507547 / 250000000000 : ℝ)
  frameHi := (1473190988451 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12773]
  agentFrame_pos := by norm_num only [agent12773]
  worldRadius := (2204093499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12773]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (684418827 / 500000000000 : ℝ)
  lowerTail := (1624591801 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3937096747 / 500000000000 : ℝ)
  ledger := by
    have h : (233776127 / 200000000000 : ℚ) +
        (1161516523 / 125000000000000000 : ℚ) / (2204093499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (684418827 / 500000000000 : ℚ) + (1624591801 / 1000000000000 : ℚ) ≤
        (3937096747 / 500000000000 : ℚ) := by norm_num only
    have hc : (((233776127 / 200000000000 : ℚ) +
        (1161516523 / 125000000000000000 : ℚ) / (2204093499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (684418827 / 500000000000 : ℚ) + (1624591801 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3937096747 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12773]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12773 :
    2 * 160 < 12773 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998791 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12773 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12774 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12774. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12774 : WorldParameters where
  hiddenCharge := (584418933 / 500000000000 : ℝ)
  frame := (124921669727 / 200000000000 : ℝ)
  moment := (9290231607 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12774 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736579859751 / 500000000000 : ℝ)
    root := (2111392849 / 250000000000 : ℝ) }

noncomputable def scalar12774 : ScalarCertificate 12774 world12774 agent12774 where
  dimensionLo := 12774
  dimensionHi := 12774
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2204451799 / 1000000000000 : ℝ)
  frameLo := (124921669727 / 200000000000 : ℝ)
  frameHi := (736579859751 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12774]
  agentFrame_pos := by norm_num only [agent12774]
  worldRadius := (2204451799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12774]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (683844509 / 500000000000 : ℝ)
  lowerTail := (81166299 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (983840431 / 125000000000 : ℝ)
  ledger := by
    have h : (584418933 / 500000000000 : ℚ) +
        (9290231607 / 1000000000000000000 : ℚ) / (2204451799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (683844509 / 500000000000 : ℚ) + (81166299 / 50000000000 : ℚ) ≤
        (983840431 / 125000000000 : ℚ) := by norm_num only
    have hc : (((584418933 / 500000000000 : ℚ) +
        (9290231607 / 1000000000000000000 : ℚ) / (2204451799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (683844509 / 500000000000 : ℚ) + (81166299 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((983840431 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12774]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12774 :
    2 * 160 < 12774 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999843 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12774 {← IO.monoMsNow}" : IO Unit)
