import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13175 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13175. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13175 : WorldParameters where
  hiddenCharge := (576277271 / 500000000000 : ℝ)
  frame := (619291971833 / 1000000000000 : ℝ)
  moment := (8569830449 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13175 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458178337213 / 1000000000000 : ℝ)
    root := (327719903 / 40000000000 : ℝ) }

noncomputable def scalar13175 : ScalarCertificate 13175 world13175 agent13175 where
  dimensionLo := 13175
  dimensionHi := 13175
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2354237699 / 1000000000000 : ℝ)
  frameLo := (619291971833 / 1000000000000 : ℝ)
  frameHi := (1458178337213 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13175]
  agentFrame_pos := by norm_num only [agent13175]
  worldRadius := (2354237699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13175]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (61070873 / 62500000000 : ℝ)
  lowerTail := (296668233 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6661728587 / 1000000000000 : ℝ)
  ledger := by
    have h : (576277271 / 500000000000 : ℚ) +
        (8569830449 / 1000000000000000000 : ℚ) / (2354237699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61070873 / 62500000000 : ℚ) + (296668233 / 250000000000 : ℚ) ≤
        (6661728587 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576277271 / 500000000000 : ℚ) +
        (8569830449 / 1000000000000000000 : ℚ) / (2354237699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61070873 / 62500000000 : ℚ) + (296668233 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6661728587 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13175]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13175 :
    2 * 160 < 13175 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999767 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13175 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13176 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13176. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13176 : WorldParameters where
  hiddenCharge := (576258001 / 500000000000 : ℝ)
  frame := (619279123819 / 1000000000000 : ℝ)
  moment := (8568133077 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13176 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58326023397 / 40000000000 : ℝ)
    root := (8192402203 / 1000000000000 : ℝ) }

noncomputable def scalar13176 : ScalarCertificate 13176 world13176 agent13176 where
  dimensionLo := 13176
  dimensionHi := 13176
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2354603099 / 1000000000000 : ℝ)
  frameLo := (619279123819 / 1000000000000 : ℝ)
  frameHi := (58326023397 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13176]
  agentFrame_pos := by norm_num only [agent13176]
  worldRadius := (2354603099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13176]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (976350043 / 1000000000000 : ℝ)
  lowerTail := (47431573 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1331847299 / 200000000000 : ℝ)
  ledger := by
    have h : (576258001 / 500000000000 : ℚ) +
        (8568133077 / 1000000000000000000 : ℚ) / (2354603099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (976350043 / 1000000000000 : ℚ) + (47431573 / 40000000000 : ℚ) ≤
        (1331847299 / 200000000000 : ℚ) := by norm_num only
    have hc : (((576258001 / 500000000000 : ℚ) +
        (8568133077 / 1000000000000000000 : ℚ) / (2354603099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (976350043 / 1000000000000 : ℚ) + (47431573 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1331847299 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13176]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13176 :
    2 * 160 < 13176 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999577 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13176 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13177 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13177. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13177 : WorldParameters where
  hiddenCharge := (1152477471 / 1000000000000 : ℝ)
  frame := (38704142361 / 62500000000 : ℝ)
  moment := (4283218087 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13177 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (729061424709 / 500000000000 : ℝ)
    root := (819180699 / 100000000000 : ℝ) }

noncomputable def scalar13177 : ScalarCertificate 13177 world13177 agent13177 where
  dimensionLo := 13177
  dimensionHi := 13177
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2354968599 / 1000000000000 : ℝ)
  frameLo := (38704142361 / 62500000000 : ℝ)
  frameHi := (729061424709 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13177]
  agentFrame_pos := by norm_num only [agent13177]
  worldRadius := (2354968599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13177]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (15243233 / 15625000000 : ℝ)
  lowerTail := (148113321 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6656746423 / 1000000000000 : ℝ)
  ledger := by
    have h : (1152477471 / 1000000000000 : ℚ) +
        (4283218087 / 500000000000000000 : ℚ) / (2354968599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (15243233 / 15625000000 : ℚ) + (148113321 / 125000000000 : ℚ) ≤
        (6656746423 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1152477471 / 1000000000000 : ℚ) +
        (4283218087 / 500000000000000000 : ℚ) / (2354968599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (15243233 / 15625000000 : ℚ) + (148113321 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6656746423 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13177]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13177 :
    2 * 160 < 13177 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998173 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13177 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13178 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13178. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13178 : WorldParameters where
  hiddenCharge := (23048779 / 20000000000 : ℝ)
  frame := (123850686741 / 200000000000 : ℝ)
  moment := (8564739741 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13178 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458094932813 / 1000000000000 : ℝ)
    root := (1638242387 / 200000000000 : ℝ) }

noncomputable def scalar13178 : ScalarCertificate 13178 world13178 agent13178 where
  dimensionLo := 13178
  dimensionHi := 13178
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2355334399 / 1000000000000 : ℝ)
  frameLo := (123850686741 / 200000000000 : ℝ)
  frameHi := (1458094932813 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13178]
  agentFrame_pos := by norm_num only [agent13178]
  worldRadius := (2355334399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13178]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (243696017 / 250000000000 : ℝ)
  lowerTail := (1184023999 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6654256941 / 1000000000000 : ℝ)
  ledger := by
    have h : (23048779 / 20000000000 : ℚ) +
        (8564739741 / 1000000000000000000 : ℚ) / (2355334399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (243696017 / 250000000000 : ℚ) + (1184023999 / 1000000000000 : ℚ) ≤
        (6654256941 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((23048779 / 20000000000 : ℚ) +
        (8564739741 / 1000000000000000000 : ℚ) / (2355334399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (243696017 / 250000000000 : ℚ) + (1184023999 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6654256941 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13178]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13178 :
    2 * 160 < 13178 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999577 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13178 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13179 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13179. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13179 : WorldParameters where
  hiddenCharge := (576200219 / 500000000000 : ℝ)
  frame := (154810147901 / 250000000000 : ℝ)
  moment := (4281521889 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13179 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1458066910777 / 1000000000000 : ℝ)
    root := (8190617039 / 1000000000000 : ℝ) }

noncomputable def scalar13179 : ScalarCertificate 13179 world13179 agent13179 where
  dimensionLo := 13179
  dimensionHi := 13179
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2355700399 / 1000000000000 : ℝ)
  frameLo := (154810147901 / 250000000000 : ℝ)
  frameHi := (1458066910777 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13179]
  agentFrame_pos := by norm_num only [agent13179]
  worldRadius := (2355700399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13179]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (974001689 / 1000000000000 : ℝ)
  lowerTail := (36973183 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1330353719 / 200000000000 : ℝ)
  ledger := by
    have h : (576200219 / 500000000000 : ℚ) +
        (4281521889 / 500000000000000000 : ℚ) / (2355700399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (974001689 / 1000000000000 : ℚ) + (36973183 / 31250000000 : ℚ) ≤
        (1330353719 / 200000000000 : ℚ) := by norm_num only
    have hc : (((576200219 / 500000000000 : ℚ) +
        (4281521889 / 500000000000000000 : ℚ) / (2355700399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (974001689 / 1000000000000 : ℚ) + (36973183 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((1330353719 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13179]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13179 :
    2 * 160 < 13179 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999037 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13179 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13180 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13180. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13180 : WorldParameters where
  hiddenCharge := (1152361937 / 1000000000000 : ℝ)
  frame := (619227751473 / 1000000000000 : ℝ)
  moment := (2140337071 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13180 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457962862309 / 1000000000000 : ℝ)
    root := (51187639 / 6250000000 : ℝ) }

noncomputable def scalar13180 : ScalarCertificate 13180 world13180 agent13180 where
  dimensionLo := 13180
  dimensionHi := 13180
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2356184699 / 1000000000000 : ℝ)
  frameLo := (619227751473 / 1000000000000 : ℝ)
  frameHi := (1457962862309 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13180]
  agentFrame_pos := by norm_num only [agent13180]
  worldRadius := (2356184699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13180]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (973050533 / 1000000000000 : ℝ)
  lowerTail := (1182035481 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6648732881 / 1000000000000 : ℝ)
  ledger := by
    have h : (1152361937 / 1000000000000 : ℚ) +
        (2140337071 / 250000000000000000 : ℚ) / (2356184699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (973050533 / 1000000000000 : ℚ) + (1182035481 / 1000000000000 : ℚ) ≤
        (6648732881 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1152361937 / 1000000000000 : ℚ) +
        (2140337071 / 250000000000000000 : ℚ) / (2356184699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (973050533 / 1000000000000 : ℚ) + (1182035481 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6648732881 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13180]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13180 :
    2 * 160 < 13180 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999667 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13180 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13181 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13181. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13181 : WorldParameters where
  hiddenCharge := (230464689 / 200000000000 : ℝ)
  frame := (619214913311 / 1000000000000 : ℝ)
  moment := (4279826629 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13181 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728967434427 / 500000000000 : ℝ)
    root := (8189427661 / 1000000000000 : ℝ) }

noncomputable def scalar13181 : ScalarCertificate 13181 world13181 agent13181 where
  dimensionLo := 13181
  dimensionHi := 13181
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2356550699 / 1000000000000 : ℝ)
  frameLo := (619214913311 / 1000000000000 : ℝ)
  frameHi := (728967434427 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13181]
  agentFrame_pos := by norm_num only [agent13181]
  worldRadius := (2356550699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13181]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (60766857 / 62500000000 : ℝ)
  lowerTail := (1181155013 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1661562221 / 250000000000 : ℝ)
  ledger := by
    have h : (230464689 / 200000000000 : ℚ) +
        (4279826629 / 500000000000000000 : ℚ) / (2356550699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (60766857 / 62500000000 : ℚ) + (1181155013 / 1000000000000 : ℚ) ≤
        (1661562221 / 250000000000 : ℚ) := by norm_num only
    have hc : (((230464689 / 200000000000 : ℚ) +
        (4279826629 / 500000000000000000 : ℚ) / (2356550699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (60766857 / 62500000000 : ℚ) + (1181155013 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1661562221 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13181]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13181 :
    2 * 160 < 13181 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (249999961 / 25000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13181 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13182 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13182. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13182 : WorldParameters where
  hiddenCharge := (1152284963 / 1000000000000 : ℝ)
  frame := (619202077119 / 1000000000000 : ℝ)
  moment := (4278979351 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13182 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (145790689217 / 100000000000 : ℝ)
    root := (8188833239 / 1000000000000 : ℝ) }

noncomputable def scalar13182 : ScalarCertificate 13182 world13182 agent13182 where
  dimensionLo := 13182
  dimensionHi := 13182
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2356916699 / 1000000000000 : ℝ)
  frameLo := (619202077119 / 1000000000000 : ℝ)
  frameHi := (145790689217 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13182]
  agentFrame_pos := by norm_num only [agent13182]
  worldRadius := (2356916699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13182]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (48574481 / 50000000000 : ℝ)
  lowerTail := (590137661 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (830470863 / 125000000000 : ℝ)
  ledger := by
    have h : (1152284963 / 1000000000000 : ℚ) +
        (4278979351 / 500000000000000000 : ℚ) / (2356916699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (48574481 / 50000000000 : ℚ) + (590137661 / 500000000000 : ℚ) ≤
        (830470863 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1152284963 / 1000000000000 : ℚ) +
        (4278979351 / 500000000000000000 : ℚ) / (2356916699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (48574481 / 50000000000 : ℚ) + (590137661 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((830470863 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13182]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13182 :
    2 * 160 < 13182 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999581 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13182 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13183 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13183. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13183 : WorldParameters where
  hiddenCharge := (1152246491 / 1000000000000 : ℝ)
  frame := (38699327681 / 62500000000 : ℝ)
  moment := (1711252923 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13183 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457878926433 / 1000000000000 : ℝ)
    root := (63970617 / 7812500000 : ℝ) }

noncomputable def scalar13183 : ScalarCertificate 13183 world13183 agent13183 where
  dimensionLo := 13183
  dimensionHi := 13183
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2357282799 / 1000000000000 : ℝ)
  frameLo := (38699327681 / 62500000000 : ℝ)
  frameHi := (1457878926433 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13183]
  agentFrame_pos := by norm_num only [agent13183]
  worldRadius := (2357282799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13183]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (970710301 / 1000000000000 : ℝ)
  lowerTail := (235879291 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1328257379 / 200000000000 : ℝ)
  ledger := by
    have h : (1152246491 / 1000000000000 : ℚ) +
        (1711252923 / 200000000000000000 : ℚ) / (2357282799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (970710301 / 1000000000000 : ℚ) + (235879291 / 200000000000 : ℚ) ≤
        (1328257379 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1152246491 / 1000000000000 : ℚ) +
        (1711252923 / 200000000000000000 : ℚ) / (2357282799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (970710301 / 1000000000000 : ℚ) + (235879291 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1328257379 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13183]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13183 :
    2 * 160 < 13183 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (499999881 / 50000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13183 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13184 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13184. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13184 : WorldParameters where
  hiddenCharge := (1152208029 / 1000000000000 : ℝ)
  frame := (7739705133 / 12500000000 : ℝ)
  moment := (2138642749 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13184 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291570195491 / 200000000000 : ℝ)
    root := (8187644871 / 1000000000000 : ℝ) }

noncomputable def scalar13184 : ScalarCertificate 13184 world13184 agent13184 where
  dimensionLo := 13184
  dimensionHi := 13184
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2357648799 / 1000000000000 : ℝ)
  frameLo := (7739705133 / 12500000000 : ℝ)
  frameHi := (291570195491 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13184]
  agentFrame_pos := by norm_num only [agent13184]
  worldRadius := (2357648799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13184]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (969931649 / 1000000000000 : ℝ)
  lowerTail := (589259147 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (103731389 / 15625000000 : ℝ)
  ledger := by
    have h : (1152208029 / 1000000000000 : ℚ) +
        (2138642749 / 250000000000000000 : ℚ) / (2357648799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (969931649 / 1000000000000 : ℚ) + (589259147 / 500000000000 : ℚ) ≤
        (103731389 / 15625000000 : ℚ) := by norm_num only
    have hc : (((1152208029 / 1000000000000 : ℚ) +
        (2138642749 / 250000000000000000 : ℚ) / (2357648799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (969931649 / 1000000000000 : ℚ) + (589259147 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((103731389 / 15625000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13184]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13184 :
    2 * 160 < 13184 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997827 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13184 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13185 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13185. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13185 : WorldParameters where
  hiddenCharge := (1152169577 / 1000000000000 : ℝ)
  frame := (619163580353 / 1000000000000 : ℝ)
  moment := (4276438923 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13185 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457823039413 / 1000000000000 : ℝ)
    root := (8187050863 / 1000000000000 : ℝ) }

noncomputable def scalar13185 : ScalarCertificate 13185 world13185 agent13185 where
  dimensionLo := 13185
  dimensionHi := 13185
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2358014799 / 1000000000000 : ℝ)
  frameLo := (619163580353 / 1000000000000 : ℝ)
  frameHi := (1457823039413 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13185]
  agentFrame_pos := by norm_num only [agent13185]
  worldRadius := (2358014799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13185]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (96915367 / 100000000000 : ℝ)
  lowerTail := (73602553 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6636332791 / 1000000000000 : ℝ)
  ledger := by
    have h : (1152169577 / 1000000000000 : ℚ) +
        (4276438923 / 500000000000000000 : ℚ) / (2358014799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (96915367 / 100000000000 : ℚ) + (73602553 / 62500000000 : ℚ) ≤
        (6636332791 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1152169577 / 1000000000000 : ℚ) +
        (4276438923 / 500000000000000000 : ℚ) / (2358014799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (96915367 / 100000000000 : ℚ) + (73602553 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((6636332791 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13185]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13185 :
    2 * 160 < 13185 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999103 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13185 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13186 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13186. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13186 : WorldParameters where
  hiddenCharge := (576065567 / 500000000000 : ℝ)
  frame := (619150752033 / 1000000000000 : ℝ)
  moment := (2137796291 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13186 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728897556151 / 500000000000 : ℝ)
    root := (8186457073 / 1000000000000 : ℝ) }

noncomputable def scalar13186 : ScalarCertificate 13186 world13186 agent13186 where
  dimensionLo := 13186
  dimensionHi := 13186
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2358380899 / 1000000000000 : ℝ)
  frameLo := (619150752033 / 1000000000000 : ℝ)
  frameHi := (728897556151 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13186]
  agentFrame_pos := by norm_num only [agent13186]
  worldRadius := (2358380899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13186]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (968376497 / 1000000000000 : ℝ)
  lowerTail := (1176764261 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (265354349 / 40000000000 : ℝ)
  ledger := by
    have h : (576065567 / 500000000000 : ℚ) +
        (2137796291 / 250000000000000000 : ℚ) / (2358380899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (968376497 / 1000000000000 : ℚ) + (1176764261 / 1000000000000 : ℚ) ≤
        (265354349 / 40000000000 : ℚ) := by norm_num only
    have hc : (((576065567 / 500000000000 : ℚ) +
        (2137796291 / 250000000000000000 : ℚ) / (2358380899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (968376497 / 1000000000000 : ℚ) + (1176764261 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((265354349 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13186]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13186 :
    2 * 160 < 13186 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999969 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13186 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13187 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13187. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13187 : WorldParameters where
  hiddenCharge := (1152092701 / 1000000000000 : ℝ)
  frame := (619137925679 / 1000000000000 : ℝ)
  moment := (170989859 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13187 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457767207753 / 1000000000000 : ℝ)
    root := (4092931721 / 500000000000 : ℝ) }

noncomputable def scalar13187 : ScalarCertificate 13187 world13187 agent13187 where
  dimensionLo := 13187
  dimensionHi := 13187
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2358746899 / 1000000000000 : ℝ)
  frameLo := (619137925679 / 1000000000000 : ℝ)
  frameHi := (1457767207753 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13187]
  agentFrame_pos := by norm_num only [agent13187]
  worldRadius := (2358746899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13187]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (967600007 / 1000000000000 : ℝ)
  lowerTail := (587944201 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6631386707 / 1000000000000 : ℝ)
  ledger := by
    have h : (1152092701 / 1000000000000 : ℚ) +
        (170989859 / 20000000000000000 : ℚ) / (2358746899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (967600007 / 1000000000000 : ℚ) + (587944201 / 500000000000 : ℚ) ≤
        (6631386707 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1152092701 / 1000000000000 : ℚ) +
        (170989859 / 20000000000000000 : ℚ) / (2358746899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (967600007 / 1000000000000 : ℚ) + (587944201 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6631386707 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13187]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13187 :
    2 * 160 < 13187 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994649 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13187 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13188 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13188. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13188 : WorldParameters where
  hiddenCharge := (576027139 / 500000000000 : ℝ)
  frame := (154781275323 / 250000000000 : ℝ)
  moment := (2136950301 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13188 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91108706769 / 62500000000 : ℝ)
    root := (511579373 / 62500000000 : ℝ) }

noncomputable def scalar13188 : ScalarCertificate 13188 world13188 agent13188 where
  dimensionLo := 13188
  dimensionHi := 13188
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2359112999 / 1000000000000 : ℝ)
  frameLo := (154781275323 / 250000000000 : ℝ)
  frameHi := (91108706769 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13188]
  agentFrame_pos := by norm_num only [agent13188]
  worldRadius := (2359112999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13188]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (241706067 / 250000000000 : ℝ)
  lowerTail := (1175013339 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6628916609 / 1000000000000 : ℝ)
  ledger := by
    have h : (576027139 / 500000000000 : ℚ) +
        (2136950301 / 250000000000000000 : ℚ) / (2359112999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (241706067 / 250000000000 : ℚ) + (1175013339 / 1000000000000 : ℚ) ≤
        (6628916609 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((576027139 / 500000000000 : ℚ) +
        (2136950301 / 250000000000000000 : ℚ) / (2359112999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (241706067 / 250000000000 : ℚ) + (1175013339 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6628916609 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13188]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13188 :
    2 * 160 < 13188 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998889 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13188 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13189 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13189. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13189 : WorldParameters where
  hiddenCharge := (144001983 / 125000000000 : ℝ)
  frame := (61911227887 / 100000000000 : ℝ)
  moment := (4273054963 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13189 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (364427856397 / 250000000000 : ℝ)
    root := (8184676591 / 1000000000000 : ℝ) }

noncomputable def scalar13189 : ScalarCertificate 13189 world13189 agent13189 where
  dimensionLo := 13189
  dimensionHi := 13189
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2359478999 / 1000000000000 : ℝ)
  frameLo := (61911227887 / 100000000000 : ℝ)
  frameHi := (364427856397 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13189]
  agentFrame_pos := by norm_num only [agent13189]
  worldRadius := (2359478999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13189]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (193209831 / 200000000000 : ℝ)
  lowerTail := (587069471 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3313224219 / 500000000000 : ℝ)
  ledger := by
    have h : (144001983 / 125000000000 : ℚ) +
        (4273054963 / 500000000000000000 : ℚ) / (2359478999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (193209831 / 200000000000 : ℚ) + (587069471 / 500000000000 : ℚ) ≤
        (3313224219 / 500000000000 : ℚ) := by norm_num only
    have hc : (((144001983 / 125000000000 : ℚ) +
        (4273054963 / 500000000000000000 : ℚ) / (2359478999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (193209831 / 200000000000 : ℚ) + (587069471 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3313224219 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13189]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13189 :
    2 * 160 < 13189 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997863 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13189 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13190 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13190. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13190 : WorldParameters where
  hiddenCharge := (1151977461 / 1000000000000 : ℝ)
  frame := (309549729207 / 500000000000 : ℝ)
  moment := (1708883823 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13190 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (728803810911 / 500000000000 : ℝ)
    root := (1023010429 / 125000000000 : ℝ) }

noncomputable def scalar13190 : ScalarCertificate 13190 world13190 agent13190 where
  dimensionLo := 13190
  dimensionHi := 13190
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2359963399 / 1000000000000 : ℝ)
  frameLo := (309549729207 / 500000000000 : ℝ)
  frameHi := (728803810911 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13190]
  agentFrame_pos := by norm_num only [agent13190]
  worldRadius := (2359963399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13190]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (30159589 / 31250000000 : ℝ)
  lowerTail := (1173042257 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6623437339 / 1000000000000 : ℝ)
  ledger := by
    have h : (1151977461 / 1000000000000 : ℚ) +
        (1708883823 / 200000000000000000 : ℚ) / (2359963399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (30159589 / 31250000000 : ℚ) + (1173042257 / 1000000000000 : ℚ) ≤
        (6623437339 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1151977461 / 1000000000000 : ℚ) +
        (1708883823 / 200000000000000000 : ℚ) / (2359963399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (30159589 / 31250000000 : ℚ) + (1173042257 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6623437339 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13190]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13190 :
    2 * 160 < 13190 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (488281 / 48828125 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13190 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13191 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13191. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13191 : WorldParameters where
  hiddenCharge := (1151939067 / 1000000000000 : ℝ)
  frame := (309543319961 / 500000000000 : ℝ)
  moment := (2135682193 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13191 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (145757976757 / 100000000000 : ℝ)
    root := (818349043 / 100000000000 : ℝ) }

noncomputable def scalar13191 : ScalarCertificate 13191 world13191 agent13191 where
  dimensionLo := 13191
  dimensionHi := 13191
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2360329699 / 1000000000000 : ℝ)
  frameLo := (309543319961 / 500000000000 : ℝ)
  frameHi := (145757976757 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13191]
  agentFrame_pos := by norm_num only [agent13191]
  worldRadius := (2360329699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13191]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (120541687 / 125000000000 : ℝ)
  lowerTail := (586084881 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (413810847 / 62500000000 : ℝ)
  ledger := by
    have h : (1151939067 / 1000000000000 : ℚ) +
        (2135682193 / 250000000000000000 : ℚ) / (2360329699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (120541687 / 125000000000 : ℚ) + (586084881 / 500000000000 : ℚ) ≤
        (413810847 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1151939067 / 1000000000000 : ℚ) +
        (2135682193 / 250000000000000000 : ℚ) / (2360329699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (120541687 / 125000000000 : ℚ) + (586084881 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((413810847 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13191]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13191 :
    2 * 160 < 13191 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999313 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13191 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13192 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13192. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13192 : WorldParameters where
  hiddenCharge := (1151900683 / 1000000000000 : ℝ)
  frame := (123814764679 / 200000000000 : ℝ)
  moment := (533814931 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13192 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291510384843 / 200000000000 : ℝ)
    root := (327315901 / 40000000000 : ℝ) }

noncomputable def scalar13192 : ScalarCertificate 13192 world13192 agent13192 where
  dimensionLo := 13192
  dimensionHi := 13192
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2360695699 / 1000000000000 : ℝ)
  frameLo := (123814764679 / 200000000000 : ℝ)
  frameHi := (291510384843 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13192]
  agentFrame_pos := by norm_num only [agent13192]
  worldRadius := (2360695699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13192]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (963560629 / 1000000000000 : ℝ)
  lowerTail := (117129777 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6618511643 / 1000000000000 : ℝ)
  ledger := by
    have h : (1151900683 / 1000000000000 : ℚ) +
        (533814931 / 62500000000000000 : ℚ) / (2360695699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (963560629 / 1000000000000 : ℚ) + (117129777 / 100000000000 : ℚ) ≤
        (6618511643 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1151900683 / 1000000000000 : ℚ) +
        (533814931 / 62500000000000000 : ℚ) / (2360695699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (963560629 / 1000000000000 : ℚ) + (117129777 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6618511643 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13192]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13192 :
    2 * 160 < 13192 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996717 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13192 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13193 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13193. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13193 : WorldParameters where
  hiddenCharge := (1151862309 / 1000000000000 : ℝ)
  frame := (9672828263 / 15625000000 : ℝ)
  moment := (8539349487 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13193 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457524097571 / 1000000000000 : ℝ)
    root := (4091152419 / 500000000000 : ℝ) }

noncomputable def scalar13193 : ScalarCertificate 13193 world13193 agent13193 where
  dimensionLo := 13193
  dimensionHi := 13193
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2361061799 / 1000000000000 : ℝ)
  frameLo := (9672828263 / 15625000000 : ℝ)
  frameHi := (1457524097571 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13193]
  agentFrame_pos := by norm_num only [agent13193]
  worldRadius := (2361061799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13193]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (48139429 / 50000000000 : ℝ)
  lowerTail := (585213327 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6616051803 / 1000000000000 : ℝ)
  ledger := by
    have h : (1151862309 / 1000000000000 : ℚ) +
        (8539349487 / 1000000000000000000 : ℚ) / (2361061799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (48139429 / 50000000000 : ℚ) + (585213327 / 500000000000 : ℚ) ≤
        (6616051803 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1151862309 / 1000000000000 : ℚ) +
        (8539349487 / 1000000000000000000 : ℚ) / (2361061799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (48139429 / 50000000000 : ℚ) + (585213327 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6616051803 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13193]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13193 :
    2 * 160 < 13193 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995801 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13193 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13194 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13194. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13194 : WorldParameters where
  hiddenCharge := (143977993 / 125000000000 : ℝ)
  frame := (77381024529 / 125000000000 : ℝ)
  moment := (4268830273 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13194 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457496281813 / 1000000000000 : ℝ)
    root := (8181712309 / 1000000000000 : ℝ) }

noncomputable def scalar13194 : ScalarCertificate 13194 world13194 agent13194 where
  dimensionLo := 13194
  dimensionHi := 13194
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2361427899 / 1000000000000 : ℝ)
  frameLo := (77381024529 / 125000000000 : ℝ)
  frameHi := (1457496281813 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13194]
  agentFrame_pos := by norm_num only [agent13194]
  worldRadius := (2361427899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13194]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (481008617 / 500000000000 : ℝ)
  lowerTail := (292389071 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3306796957 / 500000000000 : ℝ)
  ledger := by
    have h : (143977993 / 125000000000 : ℚ) +
        (4268830273 / 500000000000000000 : ℚ) / (2361427899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (481008617 / 500000000000 : ℚ) + (292389071 / 250000000000 : ℚ) ≤
        (3306796957 / 500000000000 : ℚ) := by norm_num only
    have hc : (((143977993 / 125000000000 : ℚ) +
        (4268830273 / 500000000000000000 : ℚ) / (2361427899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (481008617 / 500000000000 : ℚ) + (292389071 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3306796957 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13194]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13194 :
    2 * 160 < 13194 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999359 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13194 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13195 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13195. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13195 : WorldParameters where
  hiddenCharge := (115178559 / 100000000000 : ℝ)
  frame := (123807077119 / 200000000000 : ℝ)
  moment := (8535972071 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13195 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1457468482753 / 1000000000000 : ℝ)
    root := (127829999 / 15625000000 : ℝ) }

noncomputable def scalar13195 : ScalarCertificate 13195 world13195 agent13195 where
  dimensionLo := 13195
  dimensionHi := 13195
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2361793999 / 1000000000000 : ℝ)
  frameLo := (123807077119 / 200000000000 : ℝ)
  frameHi := (1457468482753 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13195]
  agentFrame_pos := by norm_num only [agent13195]
  worldRadius := (2361793999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13195]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (961246609 / 1000000000000 : ℝ)
  lowerTail := (1168686681 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1322227603 / 200000000000 : ℝ)
  ledger := by
    have h : (115178559 / 100000000000 : ℚ) +
        (8535972071 / 1000000000000000000 : ℚ) / (2361793999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (961246609 / 1000000000000 : ℚ) + (1168686681 / 1000000000000 : ℚ) ≤
        (1322227603 / 200000000000 : ℚ) := by norm_num only
    have hc : (((115178559 / 100000000000 : ℚ) +
        (8535972071 / 1000000000000000000 : ℚ) / (2361793999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (961246609 / 1000000000000 : ℚ) + (1168686681 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1322227603 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13195]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13195 :
    2 * 160 < 13195 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995899 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13195 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13196 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13196. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13196 : WorldParameters where
  hiddenCharge := (230349449 / 200000000000 : ℝ)
  frame := (619022576921 / 1000000000000 : ℝ)
  moment := (4267142031 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13196 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (145744069457 / 100000000000 : ℝ)
    root := (8180527659 / 1000000000000 : ℝ) }

noncomputable def scalar13196 : ScalarCertificate 13196 world13196 agent13196 where
  dimensionLo := 13196
  dimensionHi := 13196
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2362160199 / 1000000000000 : ℝ)
  frameLo := (619022576921 / 1000000000000 : ℝ)
  frameHi := (145744069457 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13196]
  agentFrame_pos := by norm_num only [agent13196]
  worldRadius := (2362160199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13196]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (240119177 / 250000000000 : ℝ)
  lowerTail := (1167817853 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6608683989 / 1000000000000 : ℝ)
  ledger := by
    have h : (230349449 / 200000000000 : ℚ) +
        (4267142031 / 500000000000000000 : ℚ) / (2362160199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240119177 / 250000000000 : ℚ) + (1167817853 / 1000000000000 : ℚ) ≤
        (6608683989 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((230349449 / 200000000000 : ℚ) +
        (4267142031 / 500000000000000000 : ℚ) / (2362160199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240119177 / 250000000000 : ℚ) + (1167817853 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((6608683989 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13196]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13196 :
    2 * 160 < 13196 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998437 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13196 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13197 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13197. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13197 : WorldParameters where
  hiddenCharge := (1151708909 / 1000000000000 : ℝ)
  frame := (19344055319 / 31250000000 : ℝ)
  moment := (8532596521 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13197 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58296516923 / 40000000000 : ℝ)
    root := (20449839 / 2500000000 : ℝ) }

noncomputable def scalar13197 : ScalarCertificate 13197 world13197 agent13197 where
  dimensionLo := 13197
  dimensionHi := 13197
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2362526399 / 1000000000000 : ℝ)
  frameLo := (19344055319 / 31250000000 : ℝ)
  frameHi := (58296516923 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13197]
  agentFrame_pos := by norm_num only [agent13197]
  worldRadius := (2362526399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13197]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (479853781 / 500000000000 : ℝ)
  lowerTail := (1166949829 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3303116011 / 500000000000 : ℝ)
  ledger := by
    have h : (1151708909 / 1000000000000 : ℚ) +
        (8532596521 / 1000000000000000000 : ℚ) / (2362526399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (479853781 / 500000000000 : ℚ) + (1166949829 / 1000000000000 : ℚ) ≤
        (3303116011 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1151708909 / 1000000000000 : ℚ) +
        (8532596521 / 1000000000000000000 : ℚ) / (2362526399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (479853781 / 500000000000 : ℚ) + (1166949829 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3303116011 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13197]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13197 :
    2 * 160 < 13197 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499998659 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13197 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13198 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13198. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13198 : WorldParameters where
  hiddenCharge := (143958823 / 125000000000 : ℝ)
  frame := (618996965457 / 1000000000000 : ℝ)
  moment := (1706181889 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13198 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (291477032489 / 200000000000 : ℝ)
    root := (4089671849 / 500000000000 : ℝ) }

noncomputable def scalar13198 : ScalarCertificate 13198 world13198 agent13198 where
  dimensionLo := 13198
  dimensionHi := 13198
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2362892499 / 1000000000000 : ℝ)
  frameLo := (618996965457 / 1000000000000 : ℝ)
  frameHi := (291477032489 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13198]
  agentFrame_pos := by norm_num only [agent13198]
  worldRadius := (2362892499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13198]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (191787811 / 200000000000 : ℝ)
  lowerTail := (14576031 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (6603781999 / 1000000000000 : ℝ)
  ledger := by
    have h : (143958823 / 125000000000 : ℚ) +
        (1706181889 / 200000000000000000 : ℚ) / (2362892499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (191787811 / 200000000000 : ℚ) + (14576031 / 12500000000 : ℚ) ≤
        (6603781999 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((143958823 / 125000000000 : ℚ) +
        (1706181889 / 200000000000000000 : ℚ) / (2362892499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (191787811 / 200000000000 : ℚ) + (14576031 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((6603781999 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13198]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13198 :
    2 * 160 < 13198 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994871 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13198 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13199 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13199. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13199 : WorldParameters where
  hiddenCharge := (287908067 / 250000000000 : ℝ)
  frame := (618984162667 / 1000000000000 : ℝ)
  moment := (2132305709 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13199 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58294296507 / 40000000000 : ℝ)
    root := (2044687973 / 250000000000 : ℝ) }

noncomputable def scalar13199 : ScalarCertificate 13199 world13199 agent13199 where
  dimensionLo := 13199
  dimensionHi := 13199
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2363258699 / 1000000000000 : ℝ)
  frameLo := (618984162667 / 1000000000000 : ℝ)
  frameHi := (58294296507 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13199]
  agentFrame_pos := by norm_num only [agent13199]
  worldRadius := (2363258699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13199]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (119771409 / 125000000000 : ℝ)
  lowerTail := (582607951 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3300666921 / 500000000000 : ℝ)
  ledger := by
    have h : (287908067 / 250000000000 : ℚ) +
        (2132305709 / 250000000000000000 : ℚ) / (2363258699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119771409 / 125000000000 : ℚ) + (582607951 / 500000000000 : ℚ) ≤
        (3300666921 / 500000000000 : ℚ) := by norm_num only
    have hc : (((287908067 / 250000000000 : ℚ) +
        (2132305709 / 250000000000000000 : ℚ) / (2363258699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (119771409 / 125000000000 : ℚ) + (582607951 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3300666921 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13199]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13199 :
    2 * 160 < 13199 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997563 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13199 {← IO.monoMsNow}" : IO Unit)
