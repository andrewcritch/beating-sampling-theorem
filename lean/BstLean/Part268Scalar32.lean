import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13150 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13150. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13150 : WorldParameters where
  hiddenCharge := (576760631 / 500000000000 : ℝ)
  frame := (123922762873 / 200000000000 : ℝ)
  moment := (8612417931 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13150 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1459028855589 / 1000000000000 : ℝ)
    root := (4103966941 / 500000000000 : ℝ) }

noncomputable def scalar13150 : ScalarCertificate 13150 world13150 agent13150 where
  dimensionLo := 13150
  dimensionHi := 13150
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2344867899 / 1000000000000 : ℝ)
  frameLo := (123922762873 / 200000000000 : ℝ)
  frameHi := (1459028855589 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13150]
  agentFrame_pos := by norm_num only [agent13150]
  worldRadius := (2344867899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13150]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (498658431 / 500000000000 : ℝ)
  lowerTail := (604737723 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6725807843 / 1000000000000 : ℝ)
  ledger := by
    have h : (576760631 / 500000000000 : ℚ) +
        (8612417931 / 1000000000000000000 : ℚ) / (2344867899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (498658431 / 500000000000 : ℚ) + (604737723 / 500000000000 : ℚ) ≤
        (6725807843 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576760631 / 500000000000 : ℚ) +
        (8612417931 / 1000000000000000000 : ℚ) / (2344867899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (498658431 / 500000000000 : ℚ) + (604737723 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6725807843 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13150]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13150 :
    2 * 160 < 13150 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997217 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13150 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13151 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13151. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13151 : WorldParameters where
  hiddenCharge := (46139299 / 40000000000 : ℝ)
  frame := (77450114613 / 125000000000 : ℝ)
  moment := (8610708759 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13151 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291800153519 / 200000000000 : ℝ)
    root := (1641466903 / 200000000000 : ℝ) }

noncomputable def scalar13151 : ScalarCertificate 13151 world13151 agent13151 where
  dimensionLo := 13151
  dimensionHi := 13151
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2345233199 / 1000000000000 : ℝ)
  frameLo := (77450114613 / 125000000000 : ℝ)
  frameHi := (291800153519 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13151]
  agentFrame_pos := by norm_num only [agent13151]
  worldRadius := (2345233199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13151]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (124564293 / 125000000000 : ℝ)
  lowerTail := (60428603 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6723264479 / 1000000000000 : ℝ)
  ledger := by
    have h : (46139299 / 40000000000 : ℚ) +
        (8610708759 / 1000000000000000000 : ℚ) / (2345233199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124564293 / 125000000000 : ℚ) + (60428603 / 50000000000 : ℚ) ≤
        (6723264479 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((46139299 / 40000000000 : ℚ) +
        (8610708759 / 1000000000000000000 : ℚ) / (2345233199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124564293 / 125000000000 : ℚ) + (60428603 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6723264479 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13151]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13151 :
    2 * 160 < 13151 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998959 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13151 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13152 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13152. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13152 : WorldParameters where
  hiddenCharge := (1153443697 / 1000000000000 : ℝ)
  frame := (619588021427 / 1000000000000 : ℝ)
  moment := (8609000061 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13152 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729486348263 / 500000000000 : ℝ)
    root := (2051683827 / 250000000000 : ℝ) }

noncomputable def scalar13152 : ScalarCertificate 13152 world13152 agent13152 where
  dimensionLo := 13152
  dimensionHi := 13152
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2345598399 / 1000000000000 : ℝ)
  frameLo := (619588021427 / 1000000000000 : ℝ)
  frameHi := (729486348263 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13152]
  agentFrame_pos := by norm_num only [agent13152]
  worldRadius := (2345598399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13152]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (248928129 / 250000000000 : ℝ)
  lowerTail := (241533881 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1680180797 / 250000000000 : ℝ)
  ledger := by
    have h : (1153443697 / 1000000000000 : ℚ) +
        (8609000061 / 1000000000000000000 : ℚ) / (2345598399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (248928129 / 250000000000 : ℚ) + (241533881 / 200000000000 : ℚ) ≤
        (1680180797 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1153443697 / 1000000000000 : ℚ) +
        (8609000061 / 1000000000000000000 : ℚ) / (2345598399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (248928129 / 250000000000 : ℚ) + (241533881 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1680180797 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13152]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13152 :
    2 * 160 < 13152 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (499999873 / 50000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13152 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13153 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13153. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13153 : WorldParameters where
  hiddenCharge := (115340493 / 100000000000 : ℝ)
  frame := (619575127933 / 1000000000000 : ℝ)
  moment := (4303645919 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13153 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29178892731 / 20000000000 : ℝ)
    root := (4103068131 / 500000000000 : ℝ) }

noncomputable def scalar13153 : ScalarCertificate 13153 world13153 agent13153 where
  dimensionLo := 13153
  dimensionHi := 13153
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2345963599 / 1000000000000 : ℝ)
  frameLo := (619575127933 / 1000000000000 : ℝ)
  frameHi := (29178892731 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13153]
  agentFrame_pos := by norm_num only [agent13153]
  worldRadius := (2345963599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13153]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (994911421 / 1000000000000 : ℝ)
  lowerTail := (48270701 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1679545981 / 250000000000 : ℝ)
  ledger := by
    have h : (115340493 / 100000000000 : ℚ) +
        (4303645919 / 500000000000000000 : ℚ) / (2345963599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (994911421 / 1000000000000 : ℚ) + (48270701 / 40000000000 : ℚ) ≤
        (1679545981 / 250000000000 : ℚ) := by norm_num only
    have hc : (((115340493 / 100000000000 : ℚ) +
        (4303645919 / 500000000000000000 : ℚ) / (2345963599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (994911421 / 1000000000000 : ℚ) + (48270701 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1679545981 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13153]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13153 :
    2 * 160 < 13153 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998401 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13153 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13154 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13154. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13154 : WorldParameters where
  hiddenCharge := (288341543 / 250000000000 : ℝ)
  frame := (309781118211 / 500000000000 : ℝ)
  moment := (1075698011 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13154 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458916593487 / 1000000000000 : ℝ)
    root := (8205537377 / 1000000000000 : ℝ) }

noncomputable def scalar13154 : ScalarCertificate 13154 world13154 agent13154 where
  dimensionLo := 13154
  dimensionHi := 13154
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2346328799 / 1000000000000 : ℝ)
  frameLo := (309781118211 / 500000000000 : ℝ)
  frameHi := (1458916593487 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13154]
  agentFrame_pos := by norm_num only [agent13154]
  worldRadius := (2346328799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13154]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (994111077 / 1000000000000 : ℝ)
  lowerTail := (241173289 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3357823363 / 500000000000 : ℝ)
  ledger := by
    have h : (288341543 / 250000000000 : ℚ) +
        (1075698011 / 125000000000000000 : ℚ) / (2346328799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (994111077 / 1000000000000 : ℚ) + (241173289 / 200000000000 : ℚ) ≤
        (3357823363 / 500000000000 : ℚ) := by norm_num only
    have hc : (((288341543 / 250000000000 : ℚ) +
        (1075698011 / 125000000000000000 : ℚ) / (2346328799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (994111077 / 1000000000000 : ℚ) + (241173289 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3357823363 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13154]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13154 :
    2 * 160 < 13154 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996059 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13154 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13155 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13155. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13155 : WorldParameters where
  hiddenCharge := (46133097 / 40000000000 : ℝ)
  frame := (619549346893 / 1000000000000 : ℝ)
  moment := (8603876811 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13155 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729444280753 / 500000000000 : ℝ)
    root := (2051234663 / 250000000000 : ℝ) }

noncomputable def scalar13155 : ScalarCertificate 13155 world13155 agent13155 where
  dimensionLo := 13155
  dimensionHi := 13155
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2346694199 / 1000000000000 : ℝ)
  frameLo := (619549346893 / 1000000000000 : ℝ)
  frameHi := (729444280753 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13155]
  agentFrame_pos := by norm_num only [agent13155]
  worldRadius := (2346694199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13155]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (99331159 / 100000000000 : ℝ)
  lowerTail := (30124157 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (134262231 / 20000000000 : ℝ)
  ledger := by
    have h : (46133097 / 40000000000 : ℚ) +
        (8603876811 / 1000000000000000000 : ℚ) / (2346694199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (99331159 / 100000000000 : ℚ) + (30124157 / 25000000000 : ℚ) ≤
        (134262231 / 20000000000 : ℚ) := by norm_num only
    have hc : (((46133097 / 40000000000 : ℚ) +
        (8603876811 / 1000000000000000000 : ℚ) / (2346694199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (99331159 / 100000000000 : ℚ) + (30124157 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((134262231 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13155]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13155 :
    2 * 160 < 13155 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (249999903 / 25000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13155 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13156 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13156. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13156 : WorldParameters where
  hiddenCharge := (1153288687 / 1000000000000 : ℝ)
  frame := (309768229673 / 500000000000 : ℝ)
  moment := (1075271251 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13156 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729430270301 / 500000000000 : ℝ)
    root := (8204340027 / 1000000000000 : ℝ) }

noncomputable def scalar13156 : ScalarCertificate 13156 world13156 agent13156 where
  dimensionLo := 13156
  dimensionHi := 13156
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2347059399 / 1000000000000 : ℝ)
  frameLo := (309768229673 / 500000000000 : ℝ)
  frameHi := (729430270301 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13156]
  agentFrame_pos := by norm_num only [agent13156]
  worldRadius := (2347059399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13156]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (99251267 / 100000000000 : ℝ)
  lowerTail := (120406671 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3355289159 / 500000000000 : ℝ)
  ledger := by
    have h : (1153288687 / 1000000000000 : ℚ) +
        (1075271251 / 125000000000000000 : ℚ) / (2347059399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (99251267 / 100000000000 : ℚ) + (120406671 / 100000000000 : ℚ) ≤
        (3355289159 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1153288687 / 1000000000000 : ℚ) +
        (1075271251 / 125000000000000000 : ℚ) / (2347059399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (99251267 / 100000000000 : ℚ) + (120406671 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3355289159 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13156]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13156 :
    2 * 160 < 13156 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998567 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13156 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13157 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13157. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13157 : WorldParameters where
  hiddenCharge := (1153249959 / 1000000000000 : ℝ)
  frame := (30976178689 / 50000000000 : ℝ)
  moment := (8600463677 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13157 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729416268297 / 500000000000 : ℝ)
    root := (1025467703 / 125000000000 : ℝ) }

noncomputable def scalar13157 : ScalarCertificate 13157 world13157 agent13157 where
  dimensionLo := 13157
  dimensionHi := 13157
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2347424699 / 1000000000000 : ℝ)
  frameLo := (30976178689 / 50000000000 : ℝ)
  frameHi := (729416268297 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13157]
  agentFrame_pos := by norm_num only [agent13157]
  worldRadius := (2347424699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13157]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (4958573 / 5000000000 : ℝ)
  lowerTail := (240633609 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (268321889 / 40000000000 : ℝ)
  ledger := by
    have h : (1153249959 / 1000000000000 : ℚ) +
        (8600463677 / 1000000000000000000 : ℚ) / (2347424699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (4958573 / 5000000000 : ℚ) + (240633609 / 200000000000 : ℚ) ≤
        (268321889 / 40000000000 : ℚ) := by norm_num only
    have hc : (((1153249959 / 1000000000000 : ℚ) +
        (8600463677 / 1000000000000000000 : ℚ) / (2347424699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (4958573 / 5000000000 : ℚ) + (240633609 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((268321889 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13157]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13157 :
    2 * 160 < 13157 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999767 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13157 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13158 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13158. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13158 : WorldParameters where
  hiddenCharge := (1153211241 / 1000000000000 : ℝ)
  frame := (309755345097 / 500000000000 : ℝ)
  moment := (429937891 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13158 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364701135913 / 250000000000 : ℝ)
    root := (410157169 / 50000000000 : ℝ) }

noncomputable def scalar13158 : ScalarCertificate 13158 world13158 agent13158 where
  dimensionLo := 13158
  dimensionHi := 13158
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2347789999 / 1000000000000 : ℝ)
  frameLo := (309755345097 / 500000000000 : ℝ)
  frameHi := (364701135913 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13158]
  agentFrame_pos := by norm_num only [agent13158]
  worldRadius := (2347789999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13158]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (990917259 / 1000000000000 : ℝ)
  lowerTail := (1202270153 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1676379537 / 250000000000 : ℝ)
  ledger := by
    have h : (1153211241 / 1000000000000 : ℚ) +
        (429937891 / 50000000000000000 : ℚ) / (2347789999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (990917259 / 1000000000000 : ℚ) + (1202270153 / 1000000000000 : ℚ) ≤
        (1676379537 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1153211241 / 1000000000000 : ℚ) +
        (429937891 / 50000000000000000 : ℚ) / (2347789999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (990917259 / 1000000000000 : ℚ) + (1202270153 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1676379537 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13158]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13158 :
    2 * 160 < 13158 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999121 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13158 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13159 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13159. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13159 : WorldParameters where
  hiddenCharge := (1153172533 / 1000000000000 : ℝ)
  frame := (619497808589 / 1000000000000 : ℝ)
  moment := (2149263109 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13159 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458776567593 / 1000000000000 : ℝ)
    root := (4101272649 / 500000000000 : ℝ) }

noncomputable def scalar13159 : ScalarCertificate 13159 world13159 agent13159 where
  dimensionLo := 13159
  dimensionHi := 13159
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2348155199 / 1000000000000 : ℝ)
  frameLo := (619497808589 / 1000000000000 : ℝ)
  frameHi := (1458776567593 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13159]
  agentFrame_pos := by norm_num only [agent13159]
  worldRadius := (2348155199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13159]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (990120603 / 1000000000000 : ℝ)
  lowerTail := (600686493 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (837873891 / 125000000000 : ℝ)
  ledger := by
    have h : (1153172533 / 1000000000000 : ℚ) +
        (2149263109 / 250000000000000000 : ℚ) / (2348155199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (990120603 / 1000000000000 : ℚ) + (600686493 / 500000000000 : ℚ) ≤
        (837873891 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1153172533 / 1000000000000 : ℚ) +
        (2149263109 / 250000000000000000 : ℚ) / (2348155199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (990120603 / 1000000000000 : ℚ) + (600686493 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((837873891 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13159]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13159 :
    2 * 160 < 13159 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997187 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13159 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13160 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13160. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13160 : WorldParameters where
  hiddenCharge := (576566917 / 500000000000 : ℝ)
  frame := (154871232241 / 250000000000 : ℝ)
  moment := (2148836881 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13160 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58346893919 / 40000000000 : ℝ)
    root := (65615579 / 8000000000 : ℝ) }

noncomputable def scalar13160 : ScalarCertificate 13160 world13160 agent13160 where
  dimensionLo := 13160
  dimensionHi := 13160
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2348638699 / 1000000000000 : ℝ)
  frameLo := (154871232241 / 250000000000 : ℝ)
  frameHi := (58346893919 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13160]
  agentFrame_pos := by norm_num only [agent13160]
  worldRadius := (2348638699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13160]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (247288063 / 250000000000 : ℝ)
  lowerTail := (1200247961 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6699908083 / 1000000000000 : ℝ)
  ledger := by
    have h : (576566917 / 500000000000 : ℚ) +
        (2148836881 / 250000000000000000 : ℚ) / (2348638699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247288063 / 250000000000 : ℚ) + (1200247961 / 1000000000000 : ℚ) ≤
        (6699908083 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576566917 / 500000000000 : ℚ) +
        (2148836881 / 250000000000000000 : ℚ) / (2348638699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247288063 / 250000000000 : ℚ) + (1200247961 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6699908083 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13160]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13160 :
    2 * 160 < 13160 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997563 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13160 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13161 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13161. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13161 : WorldParameters where
  hiddenCharge := (576547573 / 500000000000 : ℝ)
  frame := (309736025659 / 500000000000 : ℝ)
  moment := (1718728617 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13161 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729322200339 / 500000000000 : ℝ)
    root := (2050337403 / 250000000000 : ℝ) }

noncomputable def scalar13161 : ScalarCertificate 13161 world13161 agent13161 where
  dimensionLo := 13161
  dimensionHi := 13161
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2349003999 / 1000000000000 : ℝ)
  frameLo := (309736025659 / 500000000000 : ℝ)
  frameHi := (729322200339 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13161]
  agentFrame_pos := by norm_num only [agent13161]
  worldRadius := (2349003999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13161]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (7721541 / 7812500000 : ℝ)
  lowerTail := (1199352571 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1674346373 / 250000000000 : ℝ)
  ledger := by
    have h : (576547573 / 500000000000 : ℚ) +
        (1718728617 / 200000000000000000 : ℚ) / (2349003999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7721541 / 7812500000 : ℚ) + (1199352571 / 1000000000000 : ℚ) ≤
        (1674346373 / 250000000000 : ℚ) := by norm_num only
    have hc : (((576547573 / 500000000000 : ℚ) +
        (1718728617 / 200000000000000000 : ℚ) / (2349003999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7721541 / 7812500000 : ℚ) + (1199352571 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1674346373 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13161]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13161 :
    2 * 160 < 13161 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997257 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13161 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13162 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13162. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13162 : WorldParameters where
  hiddenCharge := (1153056467 / 1000000000000 : ℝ)
  frame := (619459175651 / 1000000000000 : ℝ)
  moment := (4295969559 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13162 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458616458601 / 1000000000000 : ℝ)
    root := (820075201 / 100000000000 : ℝ) }

noncomputable def scalar13162 : ScalarCertificate 13162 world13162 agent13162 where
  dimensionLo := 13162
  dimensionHi := 13162
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2349369299 / 1000000000000 : ℝ)
  frameLo := (619459175651 / 1000000000000 : ℝ)
  frameHi := (1458616458601 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13162]
  agentFrame_pos := by norm_num only [agent13162]
  worldRadius := (2349369299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13162]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (987562951 / 1000000000000 : ℝ)
  lowerTail := (599228963 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3347432433 / 500000000000 : ℝ)
  ledger := by
    have h : (1153056467 / 1000000000000 : ℚ) +
        (4295969559 / 500000000000000000 : ℚ) / (2349369299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (987562951 / 1000000000000 : ℚ) + (599228963 / 500000000000 : ℚ) ≤
        (3347432433 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1153056467 / 1000000000000 : ℚ) +
        (4295969559 / 500000000000000000 : ℚ) / (2349369299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (987562951 / 1000000000000 : ℚ) + (599228963 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3347432433 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13162]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13162 :
    2 * 160 < 13162 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999459 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13162 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13163 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13163. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13163 : WorldParameters where
  hiddenCharge := (1153017799 / 1000000000000 : ℝ)
  frame := (619446301963 / 1000000000000 : ℝ)
  moment := (8590235623 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13163 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182323567401 / 125000000000 : ℝ)
    root := (8200154567 / 1000000000000 : ℝ) }

noncomputable def scalar13163 : ScalarCertificate 13163 world13163 agent13163 where
  dimensionLo := 13163
  dimensionHi := 13163
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2349734599 / 1000000000000 : ℝ)
  frameLo := (619446301963 / 1000000000000 : ℝ)
  frameHi := (182323567401 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13163]
  agentFrame_pos := by norm_num only [agent13163]
  worldRadius := (2349734599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13163]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (123346177 / 125000000000 : ℝ)
  lowerTail := (18711939 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1673086583 / 250000000000 : ℝ)
  ledger := by
    have h : (1153017799 / 1000000000000 : ℚ) +
        (8590235623 / 1000000000000000000 : ℚ) / (2349734599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (123346177 / 125000000000 : ℚ) + (18711939 / 15625000000 : ℚ) ≤
        (1673086583 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1153017799 / 1000000000000 : ℚ) +
        (8590235623 / 1000000000000000000 : ℚ) / (2349734599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (123346177 / 125000000000 : ℚ) + (18711939 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((1673086583 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13163]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13163 :
    2 * 160 < 13163 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997609 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13163 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13164 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13164. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13164 : WorldParameters where
  hiddenCharge := (57648957 / 50000000000 : ℝ)
  frame := (154858357563 / 250000000000 : ℝ)
  moment := (42942663 / 5000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13164 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58342425001 / 40000000000 : ℝ)
    root := (1639911457 / 200000000000 : ℝ) }

noncomputable def scalar13164 : ScalarCertificate 13164 world13164 agent13164 where
  dimensionLo := 13164
  dimensionHi := 13164
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2350099999 / 1000000000000 : ℝ)
  frameLo := (154858357563 / 250000000000 : ℝ)
  frameHi := (58342425001 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13164]
  agentFrame_pos := by norm_num only [agent13164]
  worldRadius := (2350099999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13164]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (985976649 / 1000000000000 : ℝ)
  lowerTail := (1196671081 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6689829761 / 1000000000000 : ℝ)
  ledger := by
    have h : (57648957 / 50000000000 : ℚ) +
        (42942663 / 5000000000000000 : ℚ) / (2350099999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (985976649 / 1000000000000 : ℚ) + (1196671081 / 1000000000000 : ℚ) ≤
        (6689829761 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((57648957 / 50000000000 : ℚ) +
        (42942663 / 5000000000000000 : ℚ) / (2350099999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (985976649 / 1000000000000 : ℚ) + (1196671081 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6689829761 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13164]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13164 :
    2 * 160 < 13164 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998937 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13164 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13165 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13165. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13165 : WorldParameters where
  hiddenCharge := (1152940491 / 1000000000000 : ℝ)
  frame := (309710280259 / 500000000000 : ℝ)
  moment := (8586830049 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13165 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (145853272769 / 100000000000 : ℝ)
    root := (4099480081 / 500000000000 : ℝ) }

noncomputable def scalar13165 : ScalarCertificate 13165 world13165 agent13165 where
  dimensionLo := 13165
  dimensionHi := 13165
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2350465399 / 1000000000000 : ℝ)
  frameLo := (309710280259 / 500000000000 : ℝ)
  frameHi := (145853272769 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13165]
  agentFrame_pos := by norm_num only [agent13165]
  worldRadius := (2350465399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13165]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (7881477 / 8000000000 : ℝ)
  lowerTail := (149472357 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1337463047 / 200000000000 : ℝ)
  ledger := by
    have h : (1152940491 / 1000000000000 : ℚ) +
        (8586830049 / 1000000000000000000 : ℚ) / (2350465399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7881477 / 8000000000 : ℚ) + (149472357 / 125000000000 : ℚ) ≤
        (1337463047 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1152940491 / 1000000000000 : ℚ) +
        (8586830049 / 1000000000000000000 : ℚ) / (2350465399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7881477 / 8000000000 : ℚ) + (149472357 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1337463047 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13165]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13165 :
    2 * 160 < 13165 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999153 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13165 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13166 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13166. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13166 : WorldParameters where
  hiddenCharge := (288225463 / 250000000000 : ℝ)
  frame := (309703846381 / 500000000000 : ℝ)
  moment := (8585127969 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13166 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1823131059 / 1250000000 : ℝ)
    root := (4099181599 / 500000000000 : ℝ) }

noncomputable def scalar13166 : ScalarCertificate 13166 world13166 agent13166 where
  dimensionLo := 13166
  dimensionHi := 13166
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2350830699 / 1000000000000 : ℝ)
  frameLo := (309703846381 / 500000000000 : ℝ)
  frameHi := (1823131059 / 1250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13166]
  agentFrame_pos := by norm_num only [agent13166]
  worldRadius := (2350830699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13166]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (984393281 / 1000000000000 : ℝ)
  lowerTail := (23897747 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6684802753 / 1000000000000 : ℝ)
  ledger := by
    have h : (288225463 / 250000000000 : ℚ) +
        (8585127969 / 1000000000000000000 : ℚ) / (2350830699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (984393281 / 1000000000000 : ℚ) + (23897747 / 20000000000 : ℚ) ≤
        (6684802753 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((288225463 / 250000000000 : ℚ) +
        (8585127969 / 1000000000000000000 : ℚ) / (2350830699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (984393281 / 1000000000000 : ℚ) + (23897747 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6684802753 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13166]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13166 :
    2 * 160 < 13166 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995843 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13166 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13167 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13167. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13167 : WorldParameters where
  hiddenCharge := (576431611 / 500000000000 : ℝ)
  frame := (309697413491 / 500000000000 : ℝ)
  moment := (8583426361 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13167 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58339079109 / 40000000000 : ℝ)
    root := (4098883197 / 500000000000 : ℝ) }

noncomputable def scalar13167 : ScalarCertificate 13167 world13167 agent13167 where
  dimensionLo := 13167
  dimensionHi := 13167
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2351196099 / 1000000000000 : ℝ)
  frameLo := (309697413491 / 500000000000 : ℝ)
  frameHi := (58339079109 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13167]
  agentFrame_pos := by norm_num only [agent13167]
  worldRadius := (2351196099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13167]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (6147517 / 6250000000 : ℝ)
  lowerTail := (29849917 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6682292269 / 1000000000000 : ℝ)
  ledger := by
    have h : (576431611 / 500000000000 : ℚ) +
        (8583426361 / 1000000000000000000 : ℚ) / (2351196099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (6147517 / 6250000000 : ℚ) + (29849917 / 25000000000 : ℚ) ≤
        (6682292269 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576431611 / 500000000000 : ℚ) +
        (8583426361 / 1000000000000000000 : ℚ) / (2351196099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (6147517 / 6250000000 : ℚ) + (29849917 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6682292269 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13167]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13167 :
    2 * 160 < 13167 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999998943 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13167 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13168 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13168. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13168 : WorldParameters where
  hiddenCharge := (1152824603 / 1000000000000 : ℝ)
  frame := (309690981589 / 500000000000 : ℝ)
  moment := (343269009 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13168 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (72922455963 / 50000000000 : ℝ)
    root := (8197169689 / 1000000000000 : ℝ) }

noncomputable def scalar13168 : ScalarCertificate 13168 world13168 agent13168 where
  dimensionLo := 13168
  dimensionHi := 13168
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2351561499 / 1000000000000 : ℝ)
  frameLo := (309690981589 / 500000000000 : ℝ)
  frameHi := (72922455963 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13168]
  agentFrame_pos := by norm_num only [agent13168]
  worldRadius := (2351561499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13168]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (245703211 / 250000000000 : ℝ)
  lowerTail := (238621347 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6679783707 / 1000000000000 : ℝ)
  ledger := by
    have h : (1152824603 / 1000000000000 : ℚ) +
        (343269009 / 40000000000000000 : ℚ) / (2351561499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (245703211 / 250000000000 : ℚ) + (238621347 / 200000000000 : ℚ) ≤
        (6679783707 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1152824603 / 1000000000000 : ℚ) +
        (343269009 / 40000000000000000 : ℚ) / (2351561499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (245703211 / 250000000000 : ℚ) + (238621347 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6679783707 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13168]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13168 :
    2 * 160 < 13168 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999469 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13168 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13169 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13169. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13169 : WorldParameters where
  hiddenCharge := (1152785993 / 1000000000000 : ℝ)
  frame := (619369101349 / 1000000000000 : ℝ)
  moment := (8580024559 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13169 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (7292106359 / 5000000000 : ℝ)
    root := (2049143301 / 250000000000 : ℝ) }

noncomputable def scalar13169 : ScalarCertificate 13169 world13169 agent13169 where
  dimensionLo := 13169
  dimensionHi := 13169
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2351926899 / 1000000000000 : ℝ)
  frameLo := (619369101349 / 1000000000000 : ℝ)
  frameHi := (7292106359 / 5000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13169]
  agentFrame_pos := by norm_num only [agent13169]
  worldRadius := (2351926899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13169]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (39280949 / 40000000000 : ℝ)
  lowerTail := (1192217593 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1335455443 / 200000000000 : ℝ)
  ledger := by
    have h : (1152785993 / 1000000000000 : ℚ) +
        (8580024559 / 1000000000000000000 : ℚ) / (2351926899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (39280949 / 40000000000 : ℚ) + (1192217593 / 1000000000000 : ℚ) ≤
        (1335455443 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1152785993 / 1000000000000 : ℚ) +
        (8580024559 / 1000000000000000000 : ℚ) / (2351926899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (39280949 / 40000000000 : ℚ) + (1192217593 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1335455443 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13169]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13169 :
    2 * 160 < 13169 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999469 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13169 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13170 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13170. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13170 : WorldParameters where
  hiddenCharge := (576373697 / 500000000000 : ℝ)
  frame := (123871248299 / 200000000000 : ℝ)
  moment := (2144581091 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13170 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (36457932309 / 25000000000 : ℝ)
    root := (4097988439 / 500000000000 : ℝ) }

noncomputable def scalar13170 : ScalarCertificate 13170 world13170 agent13170 where
  dimensionLo := 13170
  dimensionHi := 13170
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2352410499 / 1000000000000 : ℝ)
  frameLo := (123871248299 / 200000000000 : ℝ)
  frameHi := (36457932309 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13170]
  agentFrame_pos := by norm_num only [agent13170]
  worldRadius := (2352410499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13170]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (122633043 / 125000000000 : ℝ)
  lowerTail := (9528819 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1334843821 / 200000000000 : ℝ)
  ledger := by
    have h : (576373697 / 500000000000 : ℚ) +
        (2144581091 / 250000000000000000 : ℚ) / (2352410499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (122633043 / 125000000000 : ℚ) + (9528819 / 8000000000 : ℚ) ≤
        (1334843821 / 200000000000 : ℚ) := by norm_num only
    have hc : (((576373697 / 500000000000 : ℚ) +
        (2144581091 / 250000000000000000 : ℚ) / (2352410499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (122633043 / 125000000000 : ℚ) + (9528819 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1334843821 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13170]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13170 :
    2 * 160 < 13170 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998521 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13170 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13171 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13171. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13171 : WorldParameters where
  hiddenCharge := (288177201 / 250000000000 : ℝ)
  frame := (9677240369 / 15625000000 : ℝ)
  moment := (837561 / 97656250000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13171 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291657895873 / 200000000000 : ℝ)
    root := (1024422589 / 125000000000 : ℝ) }

noncomputable def scalar13171 : ScalarCertificate 13171 world13171 agent13171 where
  dimensionLo := 13171
  dimensionHi := 13171
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2352775799 / 1000000000000 : ℝ)
  frameLo := (9677240369 / 15625000000 : ℝ)
  frameHi := (291657895873 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13171]
  agentFrame_pos := by norm_num only [agent13171]
  worldRadius := (2352775799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13171]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (490138377 / 500000000000 : ℝ)
  lowerTail := (9521719 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3335858521 / 500000000000 : ℝ)
  ledger := by
    have h : (288177201 / 250000000000 : ℚ) +
        (837561 / 97656250000000 : ℚ) / (2352775799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (490138377 / 500000000000 : ℚ) + (9521719 / 8000000000 : ℚ) ≤
        (3335858521 / 500000000000 : ℚ) := by norm_num only
    have hc : (((288177201 / 250000000000 : ℚ) +
        (837561 / 97656250000000 : ℚ) / (2352775799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (490138377 / 500000000000 : ℚ) + (9521719 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3335858521 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13171]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13171 :
    2 * 160 < 13171 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994479 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13171 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13172 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13172. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13172 : WorldParameters where
  hiddenCharge := (72041889 / 62500000000 : ℝ)
  frame := (61933052771 / 100000000000 : ℝ)
  moment := (8574925387 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13172 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458261671537 / 1000000000000 : ℝ)
    root := (128043511 / 15625000000 : ℝ) }

noncomputable def scalar13172 : ScalarCertificate 13172 world13172 agent13172 where
  dimensionLo := 13172
  dimensionHi := 13172
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2353141299 / 1000000000000 : ℝ)
  frameLo := (61933052771 / 100000000000 : ℝ)
  frameHi := (1458261671537 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13172]
  agentFrame_pos := by norm_num only [agent13172]
  worldRadius := (2353141299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13172]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (244872497 / 250000000000 : ℝ)
  lowerTail := (1189328253 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3334608463 / 500000000000 : ℝ)
  ledger := by
    have h : (72041889 / 62500000000 : ℚ) +
        (8574925387 / 1000000000000000000 : ℚ) / (2353141299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (244872497 / 250000000000 : ℚ) + (1189328253 / 1000000000000 : ℚ) ≤
        (3334608463 / 500000000000 : ℚ) := by norm_num only
    have hc : (((72041889 / 62500000000 : ℚ) +
        (8574925387 / 1000000000000000000 : ℚ) / (2353141299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (244872497 / 250000000000 : ℚ) + (1189328253 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3334608463 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13172]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13172 :
    2 * 160 < 13172 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999567 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13172 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13173 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13173. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13173 : WorldParameters where
  hiddenCharge := (1152631653 / 1000000000000 : ℝ)
  frame := (309658836889 / 500000000000 : ℝ)
  moment := (2143306651 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13173 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458233880513 / 1000000000000 : ℝ)
    root := (1024273607 / 125000000000 : ℝ) }

noncomputable def scalar13173 : ScalarCertificate 13173 world13173 agent13173 where
  dimensionLo := 13173
  dimensionHi := 13173
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2353506799 / 1000000000000 : ℝ)
  frameLo := (309658836889 / 500000000000 : ℝ)
  frameHi := (1458233880513 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13173]
  agentFrame_pos := by norm_num only [agent13173]
  worldRadius := (2353506799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13173]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (489351979 / 500000000000 : ℝ)
  lowerTail := (237688483 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (166667971 / 25000000000 : ℝ)
  ledger := by
    have h : (1152631653 / 1000000000000 : ℚ) +
        (2143306651 / 250000000000000000 : ℚ) / (2353506799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (489351979 / 500000000000 : ℚ) + (237688483 / 200000000000 : ℚ) ≤
        (166667971 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1152631653 / 1000000000000 : ℚ) +
        (2143306651 / 250000000000000000 : ℚ) / (2353506799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (489351979 / 500000000000 : ℚ) + (237688483 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((166667971 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13173]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13173 :
    2 * 160 < 13173 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999599 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13173 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13174 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13174. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13174 : WorldParameters where
  hiddenCharge := (1152593093 / 1000000000000 : ℝ)
  frame := (30965241091 / 50000000000 : ℝ)
  moment := (2142882073 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13174 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458206106287 / 1000000000000 : ℝ)
    root := (4096796583 / 500000000000 : ℝ) }

noncomputable def scalar13174 : ScalarCertificate 13174 world13174 agent13174 where
  dimensionLo := 13174
  dimensionHi := 13174
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2353872299 / 1000000000000 : ℝ)
  frameLo := (30965241091 / 50000000000 : ℝ)
  frameHi := (1458206106287 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13174]
  agentFrame_pos := by norm_num only [agent13174]
  worldRadius := (2353872299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13174]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (122239833 / 125000000000 : ℝ)
  lowerTail := (14844467 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6664222781 / 1000000000000 : ℝ)
  ledger := by
    have h : (1152593093 / 1000000000000 : ℚ) +
        (2142882073 / 250000000000000000 : ℚ) / (2353872299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (122239833 / 125000000000 : ℚ) + (14844467 / 12500000000 : ℚ) ≤
        (6664222781 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1152593093 / 1000000000000 : ℚ) +
        (2142882073 / 250000000000000000 : ℚ) / (2353872299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (122239833 / 125000000000 : ℚ) + (14844467 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((6664222781 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13174]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13174 :
    2 * 160 < 13174 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994841 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13174 {← IO.monoMsNow}" : IO Unit)
