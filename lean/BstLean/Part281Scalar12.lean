import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12159 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12159. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12159 : WorldParameters where
  hiddenCharge := (1197426209 / 1000000000000 : ℝ)
  frame := (633456728613 / 1000000000000 : ℝ)
  moment := (10569932887 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12159 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499940034873 / 1000000000000 : ℝ)
    root := (7491988589 / 1000000000000 : ℝ) }

noncomputable def scalar12159 : ScalarCertificate 12159 world12159 agent12159 where
  dimensionLo := 12159
  dimensionHi := 12159
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2333120299 / 1000000000000 : ℝ)
  frameLo := (633456728613 / 1000000000000 : ℝ)
  frameHi := (1499940034873 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12159]
  agentFrame_pos := by norm_num only [agent12159]
  worldRadius := (2333120299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12159]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1304594183 / 1000000000000 : ℝ)
  lowerTail := (413933743 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3949336077 / 500000000000 : ℝ)
  ledger := by
    have h : (1197426209 / 1000000000000 : ℚ) +
        (10569932887 / 1000000000000000000 : ℚ) / (2333120299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1304594183 / 1000000000000 : ℚ) + (413933743 / 250000000000 : ℚ) ≤
        (3949336077 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1197426209 / 1000000000000 : ℚ) +
        (10569932887 / 1000000000000000000 : ℚ) / (2333120299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1304594183 / 1000000000000 : ℚ) + (413933743 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3949336077 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12159]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12159 :
    2 * 160 < 12159 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996239 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12159 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12160 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12160. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12160 : WorldParameters where
  hiddenCharge := (119737573 / 100000000000 : ℝ)
  frame := (633441596141 / 1000000000000 : ℝ)
  moment := (1056765743 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12160 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (374972841443 / 250000000000 : ℝ)
    root := (1872829713 / 250000000000 : ℝ) }

noncomputable def scalar12160 : ScalarCertificate 12160 world12160 agent12160 where
  dimensionLo := 12160
  dimensionHi := 12160
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2333523699 / 1000000000000 : ℝ)
  frameLo := (633441596141 / 1000000000000 : ℝ)
  frameHi := (374972841443 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12160]
  agentFrame_pos := by norm_num only [agent12160]
  worldRadius := (2333523699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12160]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1303426063 / 1000000000000 : ℝ)
  lowerTail := (1654360729 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1578998029 / 200000000000 : ℝ)
  ledger := by
    have h : (119737573 / 100000000000 : ℚ) +
        (1056765743 / 100000000000000000 : ℚ) / (2333523699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1303426063 / 1000000000000 : ℚ) + (1654360729 / 1000000000000 : ℚ) ≤
        (1578998029 / 200000000000 : ℚ) := by norm_num only
    have hc : (((119737573 / 100000000000 : ℚ) +
        (1056765743 / 100000000000000000 : ℚ) / (2333523699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1303426063 / 1000000000000 : ℚ) + (1654360729 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1578998029 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12160]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12160 :
    2 * 160 < 12160 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999719 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12160 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12161 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12161. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12161 : WorldParameters where
  hiddenCharge := (74832829 / 62500000000 : ℝ)
  frame := (633426466229 / 1000000000000 : ℝ)
  moment := (5282691329 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12161 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749921365781 / 500000000000 : ℝ)
    root := (7490649403 / 1000000000000 : ℝ) }

noncomputable def scalar12161 : ScalarCertificate 12161 world12161 agent12161 where
  dimensionLo := 12161
  dimensionHi := 12161
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2333927199 / 1000000000000 : ℝ)
  frameLo := (633426466229 / 1000000000000 : ℝ)
  frameHi := (749921365781 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12161]
  agentFrame_pos := by norm_num only [agent12161]
  worldRadius := (2333927199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12161]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (130225933 / 100000000000 : ℝ)
  lowerTail := (12913969 / 7812500000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1972827919 / 250000000000 : ℝ)
  ledger := by
    have h : (74832829 / 62500000000 : ℚ) +
        (5282691329 / 500000000000000000 : ℚ) / (2333927199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (130225933 / 100000000000 : ℚ) + (12913969 / 7812500000 : ℚ) ≤
        (1972827919 / 250000000000 : ℚ) := by norm_num only
    have hc : (((74832829 / 62500000000 : ℚ) +
        (5282691329 / 500000000000000000 : ℚ) / (2333927199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (130225933 / 100000000000 : ℚ) + (12913969 / 7812500000 : ℚ) : ℚ) : ℝ) ≤
        ((1972827919 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12161]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12161 :
    2 * 160 < 12161 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999301 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12161 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12162 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12162. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12162 : WorldParameters where
  hiddenCharge := (1197274813 / 1000000000000 : ℝ)
  frame := (158352834719 / 250000000000 : ℝ)
  moment := (1056310857 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12162 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499794120119 / 1000000000000 : ℝ)
    root := (748998009 / 100000000000 : ℝ) }

noncomputable def scalar12162 : ScalarCertificate 12162 world12162 agent12162 where
  dimensionLo := 12162
  dimensionHi := 12162
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2334330599 / 1000000000000 : ℝ)
  frameLo := (158352834719 / 250000000000 : ℝ)
  frameHi := (1499794120119 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12162]
  agentFrame_pos := by norm_num only [agent12162]
  worldRadius := (2334330599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12162]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (260218733 / 200000000000 : ℝ)
  lowerTail := (1651616513 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3943818199 / 500000000000 : ℝ)
  ledger := by
    have h : (1197274813 / 1000000000000 : ℚ) +
        (1056310857 / 100000000000000000 : ℚ) / (2334330599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260218733 / 200000000000 : ℚ) + (1651616513 / 1000000000000 : ℚ) ≤
        (3943818199 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1197274813 / 1000000000000 : ℚ) +
        (1056310857 / 100000000000000000 : ℚ) / (2334330599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260218733 / 200000000000 : ℚ) + (1651616513 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3943818199 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12162]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12162 :
    2 * 160 < 12162 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994721 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12162 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12163 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12163. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12163 : WorldParameters where
  hiddenCharge := (149653047 / 125000000000 : ℝ)
  frame := (633396214081 / 1000000000000 : ℝ)
  moment := (5280417583 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12163 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499745531423 / 1000000000000 : ℝ)
    root := (936163883 / 125000000000 : ℝ) }

noncomputable def scalar12163 : ScalarCertificate 12163 world12163 agent12163 where
  dimensionLo := 12163
  dimensionHi := 12163
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2334734099 / 1000000000000 : ℝ)
  frameLo := (633396214081 / 1000000000000 : ℝ)
  frameHi := (1499745531423 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12163]
  agentFrame_pos := by norm_num only [agent12163]
  worldRadius := (2334734099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12163]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (649964667 / 500000000000 : ℝ)
  lowerTail := (825123237 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7883964541 / 1000000000000 : ℝ)
  ledger := by
    have h : (149653047 / 125000000000 : ℚ) +
        (5280417583 / 500000000000000000 : ℚ) / (2334734099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (649964667 / 500000000000 : ℚ) + (825123237 / 500000000000 : ℚ) ≤
        (7883964541 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((149653047 / 125000000000 : ℚ) +
        (5280417583 / 500000000000000000 : ℚ) / (2334734099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (649964667 / 500000000000 : ℚ) + (825123237 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7883964541 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12163]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12163 :
    2 * 160 < 12163 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999791 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12163 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12164 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12164. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12164 : WorldParameters where
  hiddenCharge := (18705843 / 15625000000 : ℝ)
  frame := (158345272961 / 250000000000 : ℝ)
  moment := (2111712489 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12164 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37492424439 / 25000000000 : ℝ)
    root := (29954569 / 4000000000 : ℝ) }

noncomputable def scalar12164 : ScalarCertificate 12164 world12164 agent12164 where
  dimensionLo := 12164
  dimensionHi := 12164
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2335137499 / 1000000000000 : ℝ)
  frameLo := (158345272961 / 250000000000 : ℝ)
  frameHi := (37492424439 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12164]
  agentFrame_pos := by norm_num only [agent12164]
  worldRadius := (2335137499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12164]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (649383087 / 500000000000 : ℝ)
  lowerTail := (206109717 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (246259253 / 31250000000 : ℝ)
  ledger := by
    have h : (18705843 / 15625000000 : ℚ) +
        (2111712489 / 200000000000000000 : ℚ) / (2335137499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (649383087 / 500000000000 : ℚ) + (206109717 / 125000000000 : ℚ) ≤
        (246259253 / 31250000000 : ℚ) := by norm_num only
    have hc : (((18705843 / 15625000000 : ℚ) +
        (2111712489 / 200000000000000000 : ℚ) / (2335137499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (649383087 / 500000000000 : ℚ) + (206109717 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((246259253 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12164]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12164 :
    2 * 160 < 12164 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997667 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12164 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12165 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12165. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12165 : WorldParameters where
  hiddenCharge := (1197123543 / 1000000000000 : ℝ)
  frame := (158341493041 / 250000000000 : ℝ)
  moment := (1319536301 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12165 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187456056557 / 125000000000 : ℝ)
    root := (7487973571 / 1000000000000 : ℝ) }

noncomputable def scalar12165 : ScalarCertificate 12165 world12165 agent12165 where
  dimensionLo := 12165
  dimensionHi := 12165
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2335540999 / 1000000000000 : ℝ)
  frameLo := (158341493041 / 250000000000 : ℝ)
  frameHi := (187456056557 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12165]
  agentFrame_pos := by norm_num only [agent12165]
  worldRadius := (2335540999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12165]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (648802127 / 500000000000 : ℝ)
  lowerTail := (1647510381 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1575326177 / 200000000000 : ℝ)
  ledger := by
    have h : (1197123543 / 1000000000000 : ℚ) +
        (1319536301 / 125000000000000000 : ℚ) / (2335540999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (648802127 / 500000000000 : ℚ) + (1647510381 / 1000000000000 : ℚ) ≤
        (1575326177 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1197123543 / 1000000000000 : ℚ) +
        (1319536301 / 125000000000000000 : ℚ) / (2335540999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (648802127 / 500000000000 : ℚ) + (1647510381 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1575326177 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12165]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12165 :
    2 * 160 < 12165 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (274999857 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12165 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12166 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12166. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12166 : WorldParameters where
  hiddenCharge := (1197073147 / 1000000000000 : ℝ)
  frame := (989610711 / 1562500000 : ℝ)
  moment := (5277009527 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12166 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499599950043 / 1000000000000 : ℝ)
    root := (374365259 / 50000000000 : ℝ) }

noncomputable def scalar12166 : ScalarCertificate 12166 world12166 agent12166 where
  dimensionLo := 12166
  dimensionHi := 12166
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2335944499 / 1000000000000 : ℝ)
  frameLo := (989610711 / 1562500000 : ℝ)
  frameHi := (1499599950043 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12166]
  agentFrame_pos := by norm_num only [agent12166]
  worldRadius := (2335944499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12166]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (324110897 / 250000000000 : ℝ)
  lowerTail := (411536103 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3936484543 / 500000000000 : ℝ)
  ledger := by
    have h : (1197073147 / 1000000000000 : ℚ) +
        (5277009527 / 500000000000000000 : ℚ) / (2335944499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (324110897 / 250000000000 : ℚ) + (411536103 / 250000000000 : ℚ) ≤
        (3936484543 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1197073147 / 1000000000000 : ℚ) +
        (5277009527 / 500000000000000000 : ℚ) / (2335944499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (324110897 / 250000000000 : ℚ) + (411536103 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3936484543 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12166]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12166 :
    2 * 160 < 12166 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995569 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12166 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12167 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12167. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12167 : WorldParameters where
  hiddenCharge := (598511383 / 500000000000 : ℝ)
  frame := (79166967559 / 125000000000 : ℝ)
  moment := (5275874191 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12167 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499551476351 / 1000000000000 : ℝ)
    root := (7486636923 / 1000000000000 : ℝ) }

noncomputable def scalar12167 : ScalarCertificate 12167 world12167 agent12167 where
  dimensionLo := 12167
  dimensionHi := 12167
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2336347999 / 1000000000000 : ℝ)
  frameLo := (79166967559 / 125000000000 : ℝ)
  frameHi := (1499551476351 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12167]
  agentFrame_pos := by norm_num only [agent12167]
  worldRadius := (2336347999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12167]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1295284083 / 1000000000000 : ℝ)
  lowerTail := (328955947 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (491831907 / 62500000000 : ℝ)
  ledger := by
    have h : (598511383 / 500000000000 : ℚ) +
        (5275874191 / 500000000000000000 : ℚ) / (2336347999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1295284083 / 1000000000000 : ℚ) + (328955947 / 200000000000 : ℚ) ≤
        (491831907 / 62500000000 : ℚ) := by norm_num only
    have hc : (((598511383 / 500000000000 : ℚ) +
        (5275874191 / 500000000000000000 : ℚ) / (2336347999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1295284083 / 1000000000000 : ℚ) + (328955947 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((491831907 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12167]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12167 :
    2 * 160 < 12167 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997771 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12167 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12168 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12168. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12168 : WorldParameters where
  hiddenCharge := (598486199 / 500000000000 : ℝ)
  frame := (633320628459 / 1000000000000 : ℝ)
  moment := (10549478393 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12168 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749751515681 / 500000000000 : ℝ)
    root := (7485968953 / 1000000000000 : ℝ) }

noncomputable def scalar12168 : ScalarCertificate 12168 world12168 agent12168 where
  dimensionLo := 12168
  dimensionHi := 12168
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2336751399 / 1000000000000 : ℝ)
  frameLo := (633320628459 / 1000000000000 : ℝ)
  frameHi := (749751515681 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12168]
  agentFrame_pos := by norm_num only [agent12168]
  worldRadius := (2336751399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12168]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (80882861 / 62500000000 : ℝ)
  lowerTail := (821708191 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7865655399 / 1000000000000 : ℝ)
  ledger := by
    have h : (598486199 / 500000000000 : ℚ) +
        (10549478393 / 1000000000000000000 : ℚ) / (2336751399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (80882861 / 62500000000 : ℚ) + (821708191 / 500000000000 : ℚ) ≤
        (7865655399 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((598486199 / 500000000000 : ℚ) +
        (10549478393 / 1000000000000000000 : ℚ) / (2336751399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (80882861 / 62500000000 : ℚ) + (821708191 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7865655399 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12168]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12168 :
    2 * 160 < 12168 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999271 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12168 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12169 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12169. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12169 : WorldParameters where
  hiddenCharge := (239384409 / 200000000000 : ℝ)
  frame := (633305519 / 1000000000 : ℝ)
  moment := (5273604543 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12169 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499454609007 / 1000000000000 : ℝ)
    root := (7485301119 / 1000000000000 : ℝ) }

noncomputable def scalar12169 : ScalarCertificate 12169 world12169 agent12169 where
  dimensionLo := 12169
  dimensionHi := 12169
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2337154999 / 1000000000000 : ℝ)
  frameLo := (633305519 / 1000000000 : ℝ)
  frameHi := (1499454609007 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12169]
  agentFrame_pos := by norm_num only [agent12169]
  worldRadius := (2337154999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12169]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (323242189 / 250000000000 : ℝ)
  lowerTail := (328410893 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (157240069 / 20000000000 : ℝ)
  ledger := by
    have h : (239384409 / 200000000000 : ℚ) +
        (5273604543 / 500000000000000000 : ℚ) / (2337154999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (323242189 / 250000000000 : ℚ) + (328410893 / 200000000000 : ℚ) ≤
        (157240069 / 20000000000 : ℚ) := by norm_num only
    have hc : (((239384409 / 200000000000 : ℚ) +
        (5273604543 / 500000000000000000 : ℚ) / (2337154999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (323242189 / 250000000000 : ℚ) + (328410893 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((157240069 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12169]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12169 :
    2 * 160 < 12169 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998697 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12169 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12170 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12170. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12170 : WorldParameters where
  hiddenCharge := (239374341 / 200000000000 : ℝ)
  frame := (126658082419 / 200000000000 : ℝ)
  moment := (10544940461 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12170 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (299881243063 / 200000000000 : ℝ)
    root := (748463357 / 100000000000 : ℝ) }

noncomputable def scalar12170 : ScalarCertificate 12170 world12170 agent12170 where
  dimensionLo := 12170
  dimensionHi := 12170
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2337558399 / 1000000000000 : ℝ)
  frameLo := (126658082419 / 200000000000 : ℝ)
  frameHi := (299881243063 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12170]
  agentFrame_pos := by norm_num only [agent12170]
  worldRadius := (2337558399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12170]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (258362571 / 200000000000 : ℝ)
  lowerTail := (1640693779 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (982294369 / 125000000000 : ℝ)
  ledger := by
    have h : (239374341 / 200000000000 : ℚ) +
        (10544940461 / 1000000000000000000 : ℚ) / (2337558399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (258362571 / 200000000000 : ℚ) + (1640693779 / 1000000000000 : ℚ) ≤
        (982294369 / 125000000000 : ℚ) := by norm_num only
    have hc : (((239374341 / 200000000000 : ℚ) +
        (10544940461 / 1000000000000000000 : ℚ) / (2337558399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (258362571 / 200000000000 : ℚ) + (1640693779 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((982294369 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12170]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12170 :
    2 * 160 < 12170 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999611 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12170 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12171 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12171. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12171 : WorldParameters where
  hiddenCharge := (1196821379 / 1000000000000 : ℝ)
  frame := (316637653871 / 500000000000 : ℝ)
  moment := (5271336259 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12171 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (374839462567 / 250000000000 : ℝ)
    root := (7483966157 / 1000000000000 : ℝ) }

noncomputable def scalar12171 : ScalarCertificate 12171 world12171 agent12171 where
  dimensionLo := 12171
  dimensionHi := 12171
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2337961899 / 1000000000000 : ℝ)
  frameLo := (316637653871 / 500000000000 : ℝ)
  frameHi := (374839462567 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12171]
  agentFrame_pos := by norm_num only [agent12171]
  worldRadius := (2337961899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12171]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (645329093 / 500000000000 : ℝ)
  lowerTail := (1639334469 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7854709667 / 1000000000000 : ℝ)
  ledger := by
    have h : (1196821379 / 1000000000000 : ℚ) +
        (5271336259 / 500000000000000000 : ℚ) / (2337961899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (645329093 / 500000000000 : ℚ) + (1639334469 / 1000000000000 : ℚ) ≤
        (7854709667 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1196821379 / 1000000000000 : ℚ) +
        (5271336259 / 500000000000000000 : ℚ) / (2337961899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (645329093 / 500000000000 : ℚ) + (1639334469 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7854709667 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12171]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12171 :
    2 * 160 < 12171 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999621 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12171 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12172 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12172. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12172 : WorldParameters where
  hiddenCharge := (1196771067 / 1000000000000 : ℝ)
  frame := (316630102971 / 500000000000 : ℝ)
  moment := (1317550657 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12172 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499309513847 / 1000000000000 : ℝ)
    root := (748329903 / 100000000000 : ℝ) }

noncomputable def scalar12172 : ScalarCertificate 12172 world12172 agent12172 where
  dimensionLo := 12172
  dimensionHi := 12172
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2338365399 / 1000000000000 : ℝ)
  frameLo := (316630102971 / 500000000000 : ℝ)
  frameHi := (1499309513847 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12172]
  agentFrame_pos := by norm_num only [agent12172]
  worldRadius := (2338365399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12172]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (257900957 / 200000000000 : ℝ)
  lowerTail := (818988283 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3925533913 / 500000000000 : ℝ)
  ledger := by
    have h : (1196771067 / 1000000000000 : ℚ) +
        (1317550657 / 125000000000000000 : ℚ) / (2338365399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (257900957 / 200000000000 : ℚ) + (818988283 / 500000000000 : ℚ) ≤
        (3925533913 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1196771067 / 1000000000000 : ℚ) +
        (1317550657 / 125000000000000000 : ℚ) / (2338365399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (257900957 / 200000000000 : ℚ) + (818988283 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3925533913 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12172]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12172 :
    2 * 160 < 12172 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999641 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12172 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12173 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12173. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12173 : WorldParameters where
  hiddenCharge := (1196720769 / 1000000000000 : ℝ)
  frame := (633245106693 / 1000000000000 : ℝ)
  moment := (421525547 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12173 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (93703825377 / 62500000000 : ℝ)
    root := (7482632037 / 1000000000000 : ℝ) }

noncomputable def scalar12173 : ScalarCertificate 12173 world12173 agent12173 where
  dimensionLo := 12173
  dimensionHi := 12173
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2338768799 / 1000000000000 : ℝ)
  frameLo := (633245106693 / 1000000000000 : ℝ)
  frameHi := (93703825377 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12173]
  agentFrame_pos := by norm_num only [agent12173]
  worldRadius := (2338768799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12173]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (64417623 / 50000000000 : ℝ)
  lowerTail := (1636619857 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7847429191 / 1000000000000 : ℝ)
  ledger := by
    have h : (1196720769 / 1000000000000 : ℚ) +
        (421525547 / 40000000000000000 : ℚ) / (2338768799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (64417623 / 50000000000 : ℚ) + (1636619857 / 1000000000000 : ℚ) ≤
        (7847429191 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1196720769 / 1000000000000 : ℚ) +
        (421525547 / 40000000000000000 : ℚ) / (2338768799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (64417623 / 50000000000 : ℚ) + (1636619857 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7847429191 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12173]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12173 :
    2 * 160 < 12173 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998011 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12173 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12174 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12174. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12174 : WorldParameters where
  hiddenCharge := (239334097 / 200000000000 : ℝ)
  frame := (126646001999 / 200000000000 : ℝ)
  moment := (1316984097 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12174 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (299842584151 / 200000000000 : ℝ)
    root := (748196533 / 100000000000 : ℝ) }

noncomputable def scalar12174 : ScalarCertificate 12174 world12174 agent12174 where
  dimensionLo := 12174
  dimensionHi := 12174
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2339172399 / 1000000000000 : ℝ)
  frameLo := (126646001999 / 200000000000 : ℝ)
  frameHi := (299842584151 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12174]
  agentFrame_pos := by norm_num only [agent12174]
  worldRadius := (2339172399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12174]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1287201529 / 1000000000000 : ℝ)
  lowerTail := (817632349 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7843793937 / 1000000000000 : ℝ)
  ledger := by
    have h : (239334097 / 200000000000 : ℚ) +
        (1316984097 / 125000000000000000 : ℚ) / (2339172399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1287201529 / 1000000000000 : ℚ) + (817632349 / 500000000000 : ℚ) ≤
        (7843793937 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((239334097 / 200000000000 : ℚ) +
        (1316984097 / 125000000000000000 : ℚ) / (2339172399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1287201529 / 1000000000000 : ℚ) + (817632349 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7843793937 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12174]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12174 :
    2 * 160 < 12174 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997951 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12174 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12175 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12175. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12175 : WorldParameters where
  hiddenCharge := (239324043 / 200000000000 : ℝ)
  frame := (79151864481 / 125000000000 : ℝ)
  moment := (10533607557 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12175 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499164664047 / 1000000000000 : ℝ)
    root := (7481298757 / 1000000000000 : ℝ) }

noncomputable def scalar12175 : ScalarCertificate 12175 world12175 agent12175 where
  dimensionLo := 12175
  dimensionHi := 12175
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2339575899 / 1000000000000 : ℝ)
  frameLo := (79151864481 / 125000000000 : ℝ)
  frameHi := (1499164664047 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12175]
  agentFrame_pos := by norm_num only [agent12175]
  worldRadius := (2339575899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12175]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (160756459 / 125000000000 : ℝ)
  lowerTail := (163391073 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7840161881 / 1000000000000 : ℝ)
  ledger := by
    have h : (239324043 / 200000000000 : ℚ) +
        (10533607557 / 1000000000000000000 : ℚ) / (2339575899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (160756459 / 125000000000 : ℚ) + (163391073 / 100000000000 : ℚ) ≤
        (7840161881 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((239324043 / 200000000000 : ℚ) +
        (10533607557 / 1000000000000000000 : ℚ) / (2339575899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (160756459 / 125000000000 : ℚ) + (163391073 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7840161881 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12175]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12175 :
    2 * 160 < 12175 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999171 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12175 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12176 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12176. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12176 : WorldParameters where
  hiddenCharge := (1196569959 / 1000000000000 : ℝ)
  frame := (2532799297 / 4000000000 : ℝ)
  moment := (5265671509 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12176 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499116435887 / 1000000000000 : ℝ)
    root := (748063247 / 100000000000 : ℝ) }

noncomputable def scalar12176 : ScalarCertificate 12176 world12176 agent12176 where
  dimensionLo := 12176
  dimensionHi := 12176
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2339979299 / 1000000000000 : ℝ)
  frameLo := (2532799297 / 4000000000 : ℝ)
  frameHi := (1499116435887 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12176]
  agentFrame_pos := by norm_num only [agent12176]
  worldRadius := (2339979299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12176]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (642451501 / 500000000000 : ℝ)
  lowerTail := (816279037 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1567306651 / 200000000000 : ℝ)
  ledger := by
    have h : (1196569959 / 1000000000000 : ℚ) +
        (5265671509 / 500000000000000000 : ℚ) / (2339979299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (642451501 / 500000000000 : ℚ) + (816279037 / 500000000000 : ℚ) ≤
        (1567306651 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1196569959 / 1000000000000 : ℚ) +
        (5265671509 / 500000000000000000 : ℚ) / (2339979299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (642451501 / 500000000000 : ℚ) + (816279037 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1567306651 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12176]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12176 :
    2 * 160 < 12176 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997167 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12176 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12177 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12177. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12177 : WorldParameters where
  hiddenCharge := (1196519717 / 1000000000000 : ℝ)
  frame := (791480919 / 1250000000 : ℝ)
  moment := (263226979 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12177 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499068236257 / 1000000000000 : ℝ)
    root := (1869991579 / 250000000000 : ℝ) }

noncomputable def scalar12177 : ScalarCertificate 12177 world12177 agent12177 where
  dimensionLo := 12177
  dimensionHi := 12177
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2340382799 / 1000000000000 : ℝ)
  frameLo := (791480919 / 1250000000 : ℝ)
  frameHi := (1499068236257 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12177]
  agentFrame_pos := by norm_num only [agent12177]
  worldRadius := (2340382799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12177]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (641877777 / 500000000000 : ℝ)
  lowerTail := (12743803 / 7812500000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7832907819 / 1000000000000 : ℝ)
  ledger := by
    have h : (1196519717 / 1000000000000 : ℚ) +
        (263226979 / 25000000000000000 : ℚ) / (2340382799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (641877777 / 500000000000 : ℚ) + (12743803 / 7812500000 : ℚ) ≤
        (7832907819 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1196519717 / 1000000000000 : ℚ) +
        (263226979 / 25000000000000000 : ℚ) / (2340382799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (641877777 / 500000000000 : ℚ) + (12743803 / 7812500000 : ℚ) : ℚ) : ℝ) ≤
        ((7832907819 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12177]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12177 :
    2 * 160 < 12177 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997199 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12177 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12178 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12178. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12178 : WorldParameters where
  hiddenCharge := (74779343 / 62500000000 : ℝ)
  frame := (633169648699 / 1000000000000 : ℝ)
  moment := (10526815981 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12178 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499020059091 / 1000000000000 : ℝ)
    root := (7479300449 / 1000000000000 : ℝ) }

noncomputable def scalar12178 : ScalarCertificate 12178 world12178 agent12178 where
  dimensionLo := 12178
  dimensionHi := 12178
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2340786299 / 1000000000000 : ℝ)
  frameLo := (633169648699 / 1000000000000 : ℝ)
  frameHi := (1499020059091 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12178]
  agentFrame_pos := by norm_num only [agent12178]
  worldRadius := (2340786299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12178]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1282609341 / 1000000000000 : ℝ)
  lowerTail := (1629856859 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7829285751 / 1000000000000 : ℝ)
  ledger := by
    have h : (74779343 / 62500000000 : ℚ) +
        (10526815981 / 1000000000000000000 : ℚ) / (2340786299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1282609341 / 1000000000000 : ℚ) + (1629856859 / 1000000000000 : ℚ) ≤
        (7829285751 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((74779343 / 62500000000 : ℚ) +
        (10526815981 / 1000000000000000000 : ℚ) / (2340786299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1282609341 / 1000000000000 : ℚ) + (1629856859 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7829285751 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12178]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12178 :
    2 * 160 < 12178 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995999 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12178 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12179 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12179. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12179 : WorldParameters where
  hiddenCharge := (598209637 / 500000000000 : ℝ)
  frame := (126630912949 / 200000000000 : ℝ)
  moment := (5262276741 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12179 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (299794382083 / 200000000000 : ℝ)
    root := (3739317357 / 500000000000 : ℝ) }

noncomputable def scalar12179 : ScalarCertificate 12179 world12179 agent12179 where
  dimensionLo := 12179
  dimensionHi := 12179
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2341189799 / 1000000000000 : ℝ)
  frameLo := (126630912949 / 200000000000 : ℝ)
  frameHi := (299794382083 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12179]
  agentFrame_pos := by norm_num only [agent12179]
  worldRadius := (2341189799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12179]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1281464273 / 1000000000000 : ℝ)
  lowerTail := (1628508209 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3912833433 / 500000000000 : ℝ)
  ledger := by
    have h : (598209637 / 500000000000 : ℚ) +
        (5262276741 / 500000000000000000 : ℚ) / (2341189799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1281464273 / 1000000000000 : ℚ) + (1628508209 / 1000000000000 : ℚ) ≤
        (3912833433 / 500000000000 : ℚ) := by norm_num only
    have hc : (((598209637 / 500000000000 : ℚ) +
        (5262276741 / 500000000000000000 : ℚ) / (2341189799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1281464273 / 1000000000000 : ℚ) + (1628508209 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3912833433 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12179]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12179 :
    2 * 160 < 12179 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995953 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12179 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12180 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12180. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12180 : WorldParameters where
  hiddenCharge := (1196369073 / 1000000000000 : ℝ)
  frame := (633139483337 / 1000000000000 : ℝ)
  moment := (5261145831 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12180 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498923790213 / 1000000000000 : ℝ)
    root := (1495593853 / 200000000000 : ℝ) }

noncomputable def scalar12180 : ScalarCertificate 12180 world12180 agent12180 where
  dimensionLo := 12180
  dimensionHi := 12180
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2341593299 / 1000000000000 : ℝ)
  frameLo := (633139483337 / 1000000000000 : ℝ)
  frameHi := (1498923790213 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12180]
  agentFrame_pos := by norm_num only [agent12180]
  worldRadius := (2341593299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12180]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1280320461 / 1000000000000 : ℝ)
  lowerTail := (1627160953 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1564410279 / 200000000000 : ℝ)
  ledger := by
    have h : (1196369073 / 1000000000000 : ℚ) +
        (5261145831 / 500000000000000000 : ℚ) / (2341593299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1280320461 / 1000000000000 : ℚ) + (1627160953 / 1000000000000 : ℚ) ≤
        (1564410279 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1196369073 / 1000000000000 : ℚ) +
        (5261145831 / 500000000000000000 : ℚ) / (2341593299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1280320461 / 1000000000000 : ℚ) + (1627160953 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1564410279 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12180]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12180 :
    2 * 160 < 12180 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994233 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12180 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12181 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12181. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12181 : WorldParameters where
  hiddenCharge := (598159443 / 500000000000 : ℝ)
  frame := (158281101119 / 250000000000 : ℝ)
  moment := (10520030521 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12181 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749437846209 / 500000000000 : ℝ)
    root := (149546079 / 20000000000 : ℝ) }

noncomputable def scalar12181 : ScalarCertificate 12181 world12181 agent12181 where
  dimensionLo := 12181
  dimensionHi := 12181
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2341996799 / 1000000000000 : ℝ)
  frameLo := (158281101119 / 250000000000 : ℝ)
  frameHi := (749437846209 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12181]
  agentFrame_pos := by norm_num only [agent12181]
  worldRadius := (2341996799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12181]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1279177767 / 1000000000000 : ℝ)
  lowerTail := (1625814937 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7818439047 / 1000000000000 : ℝ)
  ledger := by
    have h : (598159443 / 500000000000 : ℚ) +
        (10520030521 / 1000000000000000000 : ℚ) / (2341996799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1279177767 / 1000000000000 : ℚ) + (1625814937 / 1000000000000 : ℚ) ≤
        (7818439047 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((598159443 / 500000000000 : ℚ) +
        (10520030521 / 1000000000000000000 : ℚ) / (2341996799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1279177767 / 1000000000000 : ℚ) + (1625814937 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7818439047 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12181]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12181 :
    2 * 160 < 12181 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999601 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12181 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12182 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12182. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12182 : WorldParameters where
  hiddenCharge := (1196268713 / 1000000000000 : ℝ)
  frame := (3956933301 / 6250000000 : ℝ)
  moment := (525888503 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12182 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498827623057 / 1000000000000 : ℝ)
    root := (7476638919 / 1000000000000 : ℝ) }

noncomputable def scalar12182 : ScalarCertificate 12182 world12182 agent12182 where
  dimensionLo := 12182
  dimensionHi := 12182
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2342400299 / 1000000000000 : ℝ)
  frameLo := (3956933301 / 6250000000 : ℝ)
  frameHi := (1498827623057 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12182]
  agentFrame_pos := by norm_num only [agent12182]
  worldRadius := (2342400299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12182]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (639018163 / 500000000000 : ℝ)
  lowerTail := (1624470311 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3907415053 / 500000000000 : ℝ)
  ledger := by
    have h : (1196268713 / 1000000000000 : ℚ) +
        (525888503 / 50000000000000000 : ℚ) / (2342400299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (639018163 / 500000000000 : ℚ) + (1624470311 / 1000000000000 : ℚ) ≤
        (3907415053 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1196268713 / 1000000000000 : ℚ) +
        (525888503 / 50000000000000000 : ℚ) / (2342400299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (639018163 / 500000000000 : ℚ) + (1624470311 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3907415053 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12182]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12182 :
    2 * 160 < 12182 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997657 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12182 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12183 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12183. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12183 : WorldParameters where
  hiddenCharge := (598109277 / 500000000000 : ℝ)
  frame := (633094254389 / 1000000000000 : ℝ)
  moment := (2628877569 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12183 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498779582113 / 1000000000000 : ℝ)
    root := (7475974021 / 1000000000000 : ℝ) }

noncomputable def scalar12183 : ScalarCertificate 12183 world12183 agent12183 where
  dimensionLo := 12183
  dimensionHi := 12183
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2342803799 / 1000000000000 : ℝ)
  frameLo := (633094254389 / 1000000000000 : ℝ)
  frameHi := (1498779582113 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12183]
  agentFrame_pos := by norm_num only [agent12183]
  worldRadius := (2342803799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12183]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (159612003 / 125000000000 : ℝ)
  lowerTail := (811563477 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1562244867 / 200000000000 : ℝ)
  ledger := by
    have h : (598109277 / 500000000000 : ℚ) +
        (2628877569 / 250000000000000000 : ℚ) / (2342803799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (159612003 / 125000000000 : ℚ) + (811563477 / 500000000000 : ℚ) ≤
        (1562244867 / 200000000000 : ℚ) := by norm_num only
    have hc : (((598109277 / 500000000000 : ℚ) +
        (2628877569 / 250000000000000000 : ℚ) / (2342803799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (159612003 / 125000000000 : ℚ) + (811563477 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1562244867 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12183]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12183 :
    2 * 160 < 12183 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499797 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12183 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12159 :
    (1197426208474735517993 / 1000000000000000000000000 : ℝ) ≤ world12159.hiddenCharge ∧
    (633456728612575021636671 / 1000000000000000000000000 : ℝ) ≤ world12159.frame ∧
    (2642483221518041 / 250000000000000000000000 : ℝ) ≤ world12159.moment ∧
    (1499940034872448417580893 / 1000000000000000000000000 : ℝ) ≤ agent12159.frame ∧
    (149839771774873916511 / 20000000000000000000000 : ℝ) ≤ agent12159.root ∧
    scalar12159.worldRadius ≤ (2333120299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1271469494070445842103 / 1000000000000000000000000 : ℝ) ≤ agent12159.charge ∧
    (1304594182058160601263 / 1000000000000000000000000 : ℝ) ≤ scalar12159.upperTail ∧
    (827867485738013044757 / 500000000000000000000000 : ℝ) ≤ scalar12159.lowerTail ∧
    scalar12159.totalBudget ≤ (3949336077310618065239 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12159, agent12159, scalar12159] <;> simp only [true_and]

theorem source_rounding12160 :
    (598687864596813889393 / 500000000000000000000000 : ℝ) ≤ world12160.hiddenCharge ∧
    (6334415961405093326247 / 10000000000000000000000 : ℝ) ≤ world12160.frame ∧
    (10567657429669339 / 1000000000000000000000000 : ℝ) ≤ world12160.moment ∧
    (74994568288593629055759 / 50000000000000000000000 : ℝ) ≤ agent12160.frame ∧
    (187282971292420237989 / 25000000000000000000000 : ℝ) ≤ agent12160.root ∧
    scalar12160.worldRadius ≤ (2333523699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1271156432775063722491 / 1000000000000000000000000 : ℝ) ≤ agent12160.charge ∧
    (651713031498596759541 / 500000000000000000000000 : ℝ) ≤ scalar12160.upperTail ∧
    (82718036420854177109 / 50000000000000000000000 : ℝ) ≤ scalar12160.lowerTail ∧
    scalar12160.totalBudget ≤ (7894990145080571175569 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12160, agent12160, scalar12160] <;> simp only [true_and]

theorem source_rounding12161 :
    (149665657986407296711 / 125000000000000000000000 : ℝ) ≤ world12161.hiddenCharge ∧
    (633426466228225371920957 / 1000000000000000000000000 : ℝ) ≤ world12161.frame ∧
    (165084104025029 / 15625000000000000000000 : ℝ) ≤ world12161.moment ∧
    (299968546312363711489077 / 200000000000000000000000 : ℝ) ≤ agent12161.frame ∧
    (7490649402711637415659 / 1000000000000000000000000 : ℝ) ≤ agent12161.root ∧
    scalar12161.worldRadius ≤ (2333927199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1270843756316098845191 / 1000000000000000000000000 : ℝ) ≤ agent12161.charge ∧
    (1302259329933941303709 / 1000000000000000000000000 : ℝ) ≤ scalar12161.upperTail ∧
    (826494015711522552729 / 500000000000000000000000 : ℝ) ≤ scalar12161.lowerTail ∧
    scalar12161.totalBudget ≤ (3945655838385864835013 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12161, agent12161, scalar12161] <;> simp only [true_and]

theorem source_rounding12162 :
    (1197274812562562813417 / 1000000000000000000000000 : ℝ) ≤ world12162.hiddenCharge ∧
    (633411338875032982601111 / 1000000000000000000000000 : ℝ) ≤ world12162.frame ∧
    (5281554284802817 / 500000000000000000000000 : ℝ) ≤ world12162.moment ∧
    (749897060059220075150189 / 500000000000000000000000 : ℝ) ≤ agent12162.frame ∧
    (1497996017867883831699 / 200000000000000000000000 : ℝ) ≤ agent12162.root ∧
    scalar12162.worldRadius ≤ (2334330599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1270531464126692597861 / 1000000000000000000000000 : ℝ) ≤ agent12162.charge ∧
    (65054683225938101133 / 50000000000000000000000 : ℝ) ≤ scalar12162.upperTail ∧
    (1651616512892500372967 / 1000000000000000000000000 : ℝ) ≤ scalar12162.lowerTail ∧
    scalar12162.totalBudget ≤ (7887636398066815968063 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12162, agent12162, scalar12162] <;> simp only [true_and]

theorem source_rounding12163 :
    (1197224375202480284181 / 1000000000000000000000000 : ℝ) ≤ world12163.hiddenCharge ∧
    (158349053520060524335801 / 250000000000000000000000 : ℝ) ≤ world12163.frame ∧
    (10560835165416773 / 1000000000000000000000000 : ℝ) ≤ world12163.moment ∧
    (299949106284599791505351 / 200000000000000000000000 : ℝ) ≤ agent12163.frame ∧
    (3744655531861136148803 / 500000000000000000000000 : ℝ) ≤ agent12163.root ∧
    scalar12163.worldRadius ≤ (2334734099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (635109777820475399231 / 500000000000000000000000 : ℝ) ≤ agent12163.charge ∧
    (1299929333805774340701 / 1000000000000000000000000 : ℝ) ≤ scalar12163.upperTail ∧
    (1650246473774607607921 / 1000000000000000000000000 : ℝ) ≤ scalar12163.lowerTail ∧
    scalar12163.totalBudget ≤ (1970991135364880641103 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12163, agent12163, scalar12163] <;> simp only [true_and]

theorem source_rounding12164 :
    (1197173951805948324629 / 1000000000000000000000000 : ℝ) ≤ world12164.hiddenCharge ∧
    (126676218368632589736737 / 200000000000000000000000 : ℝ) ≤ world12164.frame ∧
    (5279281222385671 / 500000000000000000000000 : ℝ) ≤ world12164.moment ∧
    (1499696977559110742116399 / 1000000000000000000000000 : ℝ) ≤ agent12164.frame ∧
    (3744321124787647810251 / 500000000000000000000000 : ℝ) ≤ agent12164.root ∧
    scalar12164.worldRadius ≤ (2335137499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (634954015146970931043 / 500000000000000000000000 : ℝ) ≤ agent12164.charge ∧
    (1298766173551987444917 / 1000000000000000000000000 : ℝ) ≤ scalar12164.upperTail ∧
    (103054858441704612823 / 62500000000000000000000 : ℝ) ≤ scalar12164.lowerTail ∧
    scalar12164.totalBudget ≤ (7880296096543430485841 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12164, agent12164, scalar12164] <;> simp only [true_and]

theorem source_rounding12165 :
    (1197123542367909478907 / 1000000000000000000000000 : ℝ) ≤ world12165.hiddenCharge ∧
    (316682986081553032841493 / 500000000000000000000000 : ℝ) ≤ world12165.frame ∧
    (5278145203702821 / 500000000000000000000000 : ℝ) ≤ world12165.moment ∧
    (1499648452455543943240929 / 1000000000000000000000000 : ℝ) ≤ agent12165.frame ∧
    (3743986785338498990429 / 500000000000000000000000 : ℝ) ≤ agent12165.root ∧
    scalar12165.worldRadius ≤ (2335540999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (253919377504338994313 / 200000000000000000000000 : ℝ) ≤ agent12165.charge ∧
    (129760425388170265979 / 100000000000000000000000 : ℝ) ≤ scalar12165.upperTail ∧
    (1647510380789332929759 / 1000000000000000000000000 : ℝ) ≤ scalar12165.lowerTail ∧
    scalar12165.totalBudget ≤ (7876630885442538159437 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12165, agent12165, scalar12165] <;> simp only [true_and]

theorem source_rounding12166 :
    (239414629376661460773 / 200000000000000000000000 : ℝ) ≤ world12166.hiddenCharge ∧
    (63335085503938219684159 / 100000000000000000000000 : ℝ) ≤ world12166.frame ∧
    (10554019053056049 / 1000000000000000000000000 : ℝ) ≤ world12166.moment ∧
    (749799975021095497732359 / 500000000000000000000000 : ℝ) ≤ agent12166.frame ∧
    (1871826294768737552937 / 250000000000000000000000 : ℝ) ≤ agent12166.root ∧
    scalar12166.worldRadius ≤ (2335944499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1269286126761198251871 / 1000000000000000000000000 : ℝ) ≤ agent12166.charge ∧
    (259288717530414585491 / 200000000000000000000000 : ℝ) ≤ scalar12166.upperTail ∧
    (823072205773547871831 / 500000000000000000000000 : ℝ) ≤ scalar12166.lowerTail ∧
    scalar12166.totalBudget ≤ (787296908637536203587 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12166, agent12166, scalar12166] <;> simp only [true_and]

theorem source_rounding12167 :
    (3740696141709653207 / 3125000000000000000000 : ℝ) ≤ world12167.hiddenCharge ∧
    (31666787023565121435831 / 50000000000000000000000 : ℝ) ≤ world12167.frame ∧
    (131896854768239 / 12500000000000000000000 : ℝ) ≤ world12167.moment ∧
    (299910295270149874004773 / 200000000000000000000000 : ℝ) ≤ agent12167.frame ∧
    (3743318461239717403703 / 500000000000000000000000 : ℝ) ≤ agent12167.root ∧
    scalar12167.worldRadius ≤ (2336347999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1268975747450396948297 / 1000000000000000000000000 : ℝ) ≤ agent12167.charge ∧
    (1295284082622867853833 / 1000000000000000000000000 : ℝ) ≤ scalar12167.upperTail ∧
    (1644779734329963473811 / 1000000000000000000000000 : ℝ) ≤ scalar12167.lowerTail ∧
    scalar12167.totalBudget ≤ (78693105128829257313 / 10000000000000000000000 : ℝ) := by
  norm_num only [world12167, agent12167, scalar12167] <;> simp only [true_and]

theorem source_rounding12168 :
    (74810774859637680247 / 62500000000000000000000 : ℝ) ≤ world12168.hiddenCharge ∧
    (316660314229088971920877 / 500000000000000000000000 : ℝ) ≤ world12168.frame ∧
    (2109895678470297 / 200000000000000000000000 : ℝ) ≤ world12168.moment ∧
    (1499503031361775264381663 / 1000000000000000000000000 : ℝ) ≤ agent12168.frame ∧
    (1497193790574993724451 / 200000000000000000000000 : ℝ) ≤ agent12168.root ∧
    scalar12168.worldRadius ≤ (2336751399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (253733149805638321677 / 200000000000000000000000 : ℝ) ≤ agent12168.charge ∧
    (258825155137270156929 / 200000000000000000000000 : ℝ) ≤ scalar12168.upperTail ∧
    (205427047670747980627 / 125000000000000000000000 : ℝ) ≤ scalar12168.lowerTail ∧
    scalar12168.totalBudget ≤ (983206924904536848359 / 125000000000000000000000 : ℝ) := by
  norm_num only [world12168, agent12168, scalar12168] <;> simp only [true_and]

theorem source_rounding12169 :
    (14961525551244993179 / 12500000000000000000000 : ℝ) ≤ world12169.hiddenCharge ∧
    (633305518999320344806377 / 1000000000000000000000000 : ℝ) ≤ world12169.frame ∧
    (10547209085469901 / 1000000000000000000000000 : ℝ) ≤ world12169.moment ∧
    (299890921801211257575037 / 200000000000000000000000 : ℝ) ≤ agent12169.frame ∧
    (935662639754427520121 / 125000000000000000000000 : ℝ) ≤ agent12169.root ∧
    scalar12169.worldRadius ≤ (2337154999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (253671226186887253527 / 200000000000000000000000 : ℝ) ≤ agent12169.charge ∧
    (32324218892861288417 / 25000000000000000000000 : ℝ) ≤ scalar12169.upperTail ∧
    (41051361603023677079 / 25000000000000000000000 : ℝ) ≤ scalar12169.lowerTail ∧
    scalar12169.totalBudget ≤ (7862003450496263212743 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12169, agent12169, scalar12169] <;> simp only [true_and]

theorem source_rounding12170 :
    (1196871704378231652657 / 1000000000000000000000000 : ℝ) ≤ world12170.hiddenCharge ∧
    (15832260302351035165709 / 25000000000000000000000 : ℝ) ≤ world12170.frame ∧
    (5272470230275627 / 500000000000000000000000 : ℝ) ≤ world12170.moment ∧
    (1499406215314537735235359 / 1000000000000000000000000 : ℝ) ≤ agent12170.frame ∧
    (7484633569882294580477 / 1000000000000000000000000 : ℝ) ≤ agent12170.root ∧
    scalar12170.worldRadius ≤ (2337558399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (317011723152484159737 / 250000000000000000000000 : ℝ) ≤ agent12170.charge ∧
    (645906427326082737783 / 500000000000000000000000 : ℝ) ≤ scalar12170.upperTail ∧
    (410173444737420043121 / 250000000000000000000000 : ℝ) ≤ scalar12170.lowerTail ∧
    scalar12170.totalBudget ≤ (7858354952946287119169 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12170, agent12170, scalar12170] <;> simp only [true_and]

theorem source_rounding12171 :
    (598410689292528028017 / 500000000000000000000000 : ℝ) ≤ world12171.hiddenCharge ∧
    (79159413467706640583951 / 125000000000000000000000 : ℝ) ≤ world12171.frame ∧
    (5271336258666303 / 500000000000000000000000 : ℝ) ≤ world12171.moment ∧
    (1499357850267847634681117 / 1000000000000000000000000 : ℝ) ≤ agent12171.frame ∧
    (1870991539063250673441 / 250000000000000000000000 : ℝ) ≤ agent12171.root ∧
    scalar12171.worldRadius ≤ (2337961899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1267738033496448305817 / 1000000000000000000000000 : ℝ) ≤ agent12171.charge ∧
    (645329092664437430221 / 500000000000000000000000 : ℝ) ≤ scalar12171.upperTail ∧
    (409833617205763064289 / 250000000000000000000000 : ℝ) ≤ scalar12171.lowerTail ∧
    scalar12171.totalBudget ≤ (7854709667476424376967 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12171, agent12171, scalar12171] <;> simp only [true_and]

theorem source_rounding12172 :
    (239354213343005785031 / 200000000000000000000000 : ℝ) ≤ world12172.hiddenCharge ∧
    (633260205941467787086247 / 1000000000000000000000000 : ℝ) ≤ world12172.frame ∧
    (2108081051110209 / 200000000000000000000000 : ℝ) ≤ world12172.moment ∧
    (1499309513846638069376851 / 1000000000000000000000000 : ℝ) ≤ agent12172.frame ∧
    (7483299029006080203329 / 1000000000000000000000000 : ℝ) ≤ agent12172.root ∧
    scalar12172.worldRadius ≤ (2338365399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1267429553036674919251 / 1000000000000000000000000 : ℝ) ≤ agent12172.charge ∧
    (1289504784255867754553 / 1000000000000000000000000 : ℝ) ≤ scalar12172.upperTail ∧
    (1637976565589919680709 / 1000000000000000000000000 : ℝ) ≤ scalar12172.lowerTail ∧
    scalar12172.totalBudget ≤ (7851067826482734108393 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12172, agent12172, scalar12172] <;> simp only [true_and]

theorem source_rounding12173 :
    (29918019219077787621 / 25000000000000000000000 : ℝ) ≤ world12173.hiddenCharge ∧
    (316622553346398973982429 / 500000000000000000000000 : ℝ) ≤ world12173.frame ∧
    (10538138674943887 / 1000000000000000000000000 : ℝ) ≤ world12173.moment ∧
    (1499261206031585146692121 / 1000000000000000000000000 : ℝ) ≤ agent12173.frame ∧
    (935329004505304571347 / 125000000000000000000000 : ℝ) ≤ agent12173.root ∧
    scalar12173.worldRadius ≤ (2338768799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (633560725337133199213 / 500000000000000000000000 : ℝ) ≤ agent12173.charge ∧
    (644176229955148553263 / 500000000000000000000000 : ℝ) ≤ scalar12173.upperTail ∧
    (65464794262767120733 / 40000000000000000000000 : ℝ) ≤ scalar12173.lowerTail ∧
    scalar12173.totalBudget ≤ (7847429191315142901557 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12173, agent12173, scalar12173] <;> simp only [true_and]

theorem source_rounding12174 :
    (1196670484724266046543 / 1000000000000000000000000 : ℝ) ≤ world12174.hiddenCharge ∧
    (633230009994956406814989 / 1000000000000000000000000 : ℝ) ≤ world12174.frame ∧
    (421434911009941 / 40000000000000000000000 : ℝ) ≤ world12174.moment ∧
    (374803230188741231631221 / 250000000000000000000000 : ℝ) ≤ agent12174.frame ∧
    (3740982664578840124589 / 500000000000000000000000 : ℝ) ≤ agent12174.root ∧
    scalar12174.worldRadius ≤ (2339172399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (633406862926908567523 / 500000000000000000000000 : ℝ) ≤ agent12174.charge ∧
    (128720152888235574463 / 100000000000000000000000 : ℝ) ≤ scalar12174.upperTail ∧
    (817632348710636507809 / 500000000000000000000000 : ℝ) ≤ scalar12174.lowerTail ∧
    scalar12174.totalBudget ≤ (7843793937769752461133 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12174, agent12174, scalar12174] <;> simp only [true_and]

theorem source_rounding12175 :
    (598310107296727243769 / 500000000000000000000000 : ℝ) ≤ world12175.hiddenCharge ∧
    (316607457923628137026707 / 500000000000000000000000 : ℝ) ≤ world12175.frame ∧
    (2633401889050593 / 250000000000000000000000 : ℝ) ≤ world12175.moment ∧
    (749582332023235993279193 / 500000000000000000000000 : ℝ) ≤ agent12175.frame ∧
    (3740649378158087865729 / 500000000000000000000000 : ℝ) ≤ agent12175.root ∧
    scalar12175.worldRadius ≤ (2339575899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (50660255120834568057 / 40000000000000000000000 : ℝ) ≤ agent12175.charge ∧
    (257210334357620046199 / 200000000000000000000000 : ℝ) ≤ scalar12175.upperTail ∧
    (816955364761237144477 / 500000000000000000000000 : ℝ) ≤ scalar12175.lowerTail ∧
    scalar12175.totalBudget ≤ (3920080940950440995169 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12175, agent12175, scalar12175] <;> simp only [true_and]

theorem source_rounding12176 :
    (239313991673129277541 / 200000000000000000000000 : ℝ) ≤ world12176.hiddenCharge ∧
    (6331998242490106975999 / 10000000000000000000000 : ℝ) ≤ world12176.frame ∧
    (10531343017543177 / 1000000000000000000000000 : ℝ) ≤ world12176.moment ∧
    (59964657435474152251103 / 40000000000000000000000 : ℝ) ≤ agent12176.frame ∧
    (7480632469250646388253 / 1000000000000000000000000 : ℝ) ≤ agent12176.root ∧
    scalar12176.worldRadius ≤ (2339979299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (633099703310942781127 / 500000000000000000000000 : ℝ) ≤ agent12176.charge ∧
    (1284903001079966881361 / 1000000000000000000000000 : ℝ) ≤ scalar12176.upperTail ∧
    (1632558073500697139997 / 1000000000000000000000000 : ℝ) ≤ scalar12176.lowerTail ∧
    scalar12176.totalBudget ≤ (1567306651046675155543 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12176, agent12176, scalar12176] <;> simp only [true_and]

theorem source_rounding12177 :
    (7478248225223810413 / 6250000000000000000000 : ℝ) ≤ world12177.hiddenCharge ∧
    (158296183799883325195739 / 250000000000000000000000 : ℝ) ≤ world12177.frame ∧
    (10529079159008661 / 1000000000000000000000000 : ℝ) ≤ world12177.moment ∧
    (374767059064220441793241 / 250000000000000000000000 : ℝ) ≤ agent12177.frame ∧
    (7479966315988868168831 / 1000000000000000000000000 : ℝ) ≤ agent12177.root ∧
    scalar12177.worldRadius ≤ (2340382799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (50635712444171931603 / 40000000000000000000000 : ℝ) ≤ agent12177.charge ∧
    (1283755553304209808783 / 1000000000000000000000000 : ℝ) ≤ scalar12177.upperTail ∧
    (815603391585360060727 / 500000000000000000000000 : ℝ) ≤ scalar12177.lowerTail ∧
    scalar12177.totalBudget ≤ (1566581563806773632733 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12177, agent12177, scalar12177] <;> simp only [true_and]

theorem source_rounding12178 :
    (1196469487598914571097 / 1000000000000000000000000 : ℝ) ≤ world12178.hiddenCharge ∧
    (633169648698137955103413 / 1000000000000000000000000 : ℝ) ≤ world12178.frame ∧
    (10526815980336669 / 1000000000000000000000000 : ℝ) ≤ world12178.moment ∧
    (749510029545009571057623 / 500000000000000000000000 : ℝ) ≤ agent12178.frame ∧
    (7479300448200721490409 / 1000000000000000000000000 : ℝ) ≤ agent12178.root ∧
    scalar12178.worldRadius ≤ (2340786299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (79099161932278549027 / 62500000000000000000000 : ℝ) ≤ agent12178.charge ∧
    (1282609340928257454707 / 1000000000000000000000000 : ℝ) ≤ scalar12178.upperTail ∧
    (32597137176683439947 / 20000000000000000000000 : ℝ) ≤ scalar12178.lowerTail ∧
    scalar12178.totalBudget ≤ (782928575139195079229 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12178, agent12178, scalar12178] <;> simp only [true_and]

theorem source_rounding12179 :
    (299104818262483749817 / 250000000000000000000000 : ℝ) ≤ world12179.hiddenCharge ∧
    (633154564744138630496141 / 1000000000000000000000000 : ℝ) ≤ world12179.frame ∧
    (1315569185158153 / 125000000000000000000000 : ℝ) ≤ world12179.moment ∧
    (1498971910414962200254459 / 1000000000000000000000000 : ℝ) ≤ agent12179.frame ∧
    (7478634713977350225903 / 1000000000000000000000000 : ℝ) ≤ agent12179.root ∧
    scalar12179.worldRadius ≤ (2341189799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (158160093188456374337 / 125000000000000000000000 : ℝ) ≤ agent12179.charge ∧
    (640732136427368631071 / 500000000000000000000000 : ℝ) ≤ scalar12179.upperTail ∧
    (1628508208583448982439 / 1000000000000000000000000 : ℝ) ≤ scalar12179.lowerTail ∧
    scalar12179.totalBudget ≤ (3912833433056728626699 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12179, agent12179, scalar12179] <;> simp only [true_and]

theorem source_rounding12180 :
    (598184536191924245311 / 500000000000000000000000 : ℝ) ≤ world12180.hiddenCharge ∧
    (633139483336849667225871 / 1000000000000000000000000 : ℝ) ≤ world12180.frame ∧
    (10522291661532531 / 1000000000000000000000000 : ℝ) ≤ world12180.moment ∧
    (2927585527758893223867 / 1953125000000000000000 : ℝ) ≤ agent12180.frame ∧
    (7477969264925833930189 / 1000000000000000000000000 : ℝ) ≤ agent12180.root ∧
    scalar12180.worldRadius ≤ (2341593299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (632487637164052323283 / 500000000000000000000000 : ℝ) ≤ agent12180.charge ∧
    (320080115231227862981 / 250000000000000000000000 : ℝ) ≤ scalar12180.upperTail ∧
    (406790238105555625173 / 250000000000000000000000 : ℝ) ≤ scalar12180.lowerTail ∧
    scalar12180.totalBudget ≤ (97775642448196330427 / 12500000000000000000000 : ℝ) := by
  norm_num only [world12180, agent12180, scalar12180] <;> simp only [true_and]

theorem source_rounding12181 :
    (59815944279781481507 / 50000000000000000000000 : ℝ) ≤ world12181.hiddenCharge ∧
    (2532497617902342370847 / 4000000000000000000000 : ℝ) ≤ world12181.frame ∧
    (2630007630219177 / 250000000000000000000000 : ℝ) ≤ world12181.moment ∧
    (749437846208572061450283 / 500000000000000000000000 : ℝ) ≤ agent12181.frame ∧
    (1869325987300160227339 / 250000000000000000000000 : ℝ) ≤ agent12181.root ∧
    scalar12181.worldRadius ≤ (2341996799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (63233508841448673611 / 50000000000000000000000 : ℝ) ≤ agent12181.charge ∧
    (1279177766806757901097 / 1000000000000000000000000 : ℝ) ≤ scalar12181.upperTail ∧
    (32516298723372837139 / 20000000000000000000000 : ℝ) ≤ scalar12181.lowerTail ∧
    scalar12181.totalBudget ≤ (1563687809583745772853 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12181, agent12181, scalar12181] <;> simp only [true_and]

theorem source_rounding12182 :
    (598134356340130302197 / 500000000000000000000000 : ℝ) ≤ world12182.hiddenCharge ∧
    (316554664079830651944587 / 500000000000000000000000 : ℝ) ≤ world12182.frame ∧
    (10517770059036211 / 1000000000000000000000000 : ℝ) ≤ world12182.moment ∧
    (14988276230566833395959 / 10000000000000000000000 : ℝ) ≤ agent12182.frame ∧
    (7476638918346091909127 / 1000000000000000000000000 : ℝ) ≤ agent12182.root ∧
    scalar12182.worldRadius ≤ (2342400299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (39511420389448232629 / 31250000000000000000000 : ℝ) ≤ agent12182.charge ∧
    (127803632584526532693 / 100000000000000000000000 : ℝ) ≤ scalar12182.upperTail ∧
    (324894062169502246777 / 200000000000000000000000 : ℝ) ≤ scalar12182.lowerTail ∧
    scalar12182.totalBudget ≤ (7814830106487823986707 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12182, agent12182, scalar12182] <;> simp only [true_and]

theorem source_rounding12183 :
    (1196218553632724599813 / 1000000000000000000000000 : ℝ) ≤ world12183.hiddenCharge ∧
    (158273563597097948589719 / 250000000000000000000000 : ℝ) ≤ world12183.frame ∧
    (1051551027574957 / 100000000000000000000000 : ℝ) ≤ world12183.moment ∧
    (149877958211208410533901 / 100000000000000000000000 : ℝ) ≤ agent12183.frame ∧
    (7475974020579936220453 / 1000000000000000000000000 : ℝ) ≤ agent12183.root ∧
    scalar12183.worldRadius ≤ (2342803799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (632030550340614506251 / 500000000000000000000000 : ℝ) ≤ agent12183.charge ∧
    (1276896023617857916829 / 1000000000000000000000000 : ℝ) ≤ scalar12183.upperTail ∧
    (324625390739683660393 / 200000000000000000000000 : ℝ) ≤ scalar12183.lowerTail ∧
    scalar12183.totalBudget ≤ (488201520949816009877 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12183, agent12183, scalar12183] <;> simp only [true_and]

noncomputable def paperAgent12159 : AgentParameters :=
  { agent12159 with charge := (635734749 / 500000000000 : ℝ) }

theorem agent_is_repriced12159 : agent12159 =
    BstLean.Part265.agentRepriced 12159 world12159 paperAgent12159 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12159, agent12159]

noncomputable def paperAgent12160 : AgentParameters :=
  { agent12160 with charge := (317789109 / 250000000000 : ℝ) }

theorem agent_is_repriced12160 : agent12160 =
    BstLean.Part265.agentRepriced 12160 world12160 paperAgent12160 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12160, agent12160]

noncomputable def paperAgent12161 : AgentParameters :=
  { agent12161 with charge := (15885547 / 12500000000 : ℝ) }

theorem agent_is_repriced12161 : agent12161 =
    BstLean.Part265.agentRepriced 12161 world12161 paperAgent12161 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12161, agent12161]

noncomputable def paperAgent12162 : AgentParameters :=
  { agent12162 with charge := (1270531467 / 1000000000000 : ℝ) }

theorem agent_is_repriced12162 : agent12162 =
    BstLean.Part265.agentRepriced 12162 world12162 paperAgent12162 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12162, agent12162]

noncomputable def paperAgent12163 : AgentParameters :=
  { agent12163 with charge := (1270219559 / 1000000000000 : ℝ) }

theorem agent_is_repriced12163 : agent12163 =
    BstLean.Part265.agentRepriced 12163 world12163 paperAgent12163 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12163, agent12163]

noncomputable def paperAgent12164 : AgentParameters :=
  { agent12164 with charge := (634954017 / 500000000000 : ℝ) }

theorem agent_is_repriced12164 : agent12164 =
    BstLean.Part265.agentRepriced 12164 world12164 paperAgent12164 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12164, agent12164]

noncomputable def paperAgent12165 : AgentParameters :=
  { agent12165 with charge := (1269596891 / 1000000000000 : ℝ) }

theorem agent_is_repriced12165 : agent12165 =
    BstLean.Part265.agentRepriced 12165 world12165 paperAgent12165 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12165, agent12165]

noncomputable def paperAgent12166 : AgentParameters :=
  { agent12166 with charge := (126928613 / 100000000000 : ℝ) }

theorem agent_is_repriced12166 : agent12166 =
    BstLean.Part265.agentRepriced 12166 world12166 paperAgent12166 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12166, agent12166]

noncomputable def paperAgent12167 : AgentParameters :=
  { agent12167 with charge := (1268975751 / 1000000000000 : ℝ) }

theorem agent_is_repriced12167 : agent12167 =
    BstLean.Part265.agentRepriced 12167 world12167 paperAgent12167 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12167, agent12167]

noncomputable def paperAgent12168 : AgentParameters :=
  { agent12168 with charge := (1268665753 / 1000000000000 : ℝ) }

theorem agent_is_repriced12168 : agent12168 =
    BstLean.Part265.agentRepriced 12168 world12168 paperAgent12168 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12168, agent12168]

noncomputable def paperAgent12169 : AgentParameters :=
  { agent12169 with charge := (634178067 / 500000000000 : ℝ) }

theorem agent_is_repriced12169 : agent12169 =
    BstLean.Part265.agentRepriced 12169 world12169 paperAgent12169 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12169, agent12169]

noncomputable def paperAgent12170 : AgentParameters :=
  { agent12170 with charge := (79252931 / 62500000000 : ℝ) }

theorem agent_is_repriced12170 : agent12170 =
    BstLean.Part265.agentRepriced 12170 world12170 paperAgent12170 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12170, agent12170]

noncomputable def paperAgent12171 : AgentParameters :=
  { agent12171 with charge := (1267738037 / 1000000000000 : ℝ) }

theorem agent_is_repriced12171 : agent12171 =
    BstLean.Part265.agentRepriced 12171 world12171 paperAgent12171 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12171, agent12171]

noncomputable def paperAgent12172 : AgentParameters :=
  { agent12172 with charge := (1267429557 / 1000000000000 : ℝ) }

theorem agent_is_repriced12172 : agent12172 =
    BstLean.Part265.agentRepriced 12172 world12172 paperAgent12172 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12172, agent12172]

noncomputable def paperAgent12173 : AgentParameters :=
  { agent12173 with charge := (633560727 / 500000000000 : ℝ) }

theorem agent_is_repriced12173 : agent12173 =
    BstLean.Part265.agentRepriced 12173 world12173 paperAgent12173 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12173, agent12173]

noncomputable def paperAgent12174 : AgentParameters :=
  { agent12174 with charge := (1266813729 / 1000000000000 : ℝ) }

theorem agent_is_repriced12174 : agent12174 =
    BstLean.Part265.agentRepriced 12174 world12174 paperAgent12174 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12174, agent12174]

noncomputable def paperAgent12175 : AgentParameters :=
  { agent12175 with charge := (1266506381 / 1000000000000 : ℝ) }

theorem agent_is_repriced12175 : agent12175 =
    BstLean.Part265.agentRepriced 12175 world12175 paperAgent12175 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12175, agent12175]

noncomputable def paperAgent12176 : AgentParameters :=
  { agent12176 with charge := (126619941 / 100000000000 : ℝ) }

theorem agent_is_repriced12176 : agent12176 =
    BstLean.Part265.agentRepriced 12176 world12176 paperAgent12176 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12176, agent12176]

noncomputable def paperAgent12177 : AgentParameters :=
  { agent12177 with charge := (253178563 / 200000000000 : ℝ) }

theorem agent_is_repriced12177 : agent12177 =
    BstLean.Part265.agentRepriced 12177 world12177 paperAgent12177 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12177, agent12177]

noncomputable def paperAgent12178 : AgentParameters :=
  { agent12178 with charge := (632793297 / 500000000000 : ℝ) }

theorem agent_is_repriced12178 : agent12178 =
    BstLean.Part265.agentRepriced 12178 world12178 paperAgent12178 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12178, agent12178]

noncomputable def paperAgent12179 : AgentParameters :=
  { agent12179 with charge := (1265280749 / 1000000000000 : ℝ) }

theorem agent_is_repriced12179 : agent12179 =
    BstLean.Part265.agentRepriced 12179 world12179 paperAgent12179 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12179, agent12179]

noncomputable def paperAgent12180 : AgentParameters :=
  { agent12180 with charge := (632487639 / 500000000000 : ℝ) }

theorem agent_is_repriced12180 : agent12180 =
    BstLean.Part265.agentRepriced 12180 world12180 paperAgent12180 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12180, agent12180]

noncomputable def paperAgent12181 : AgentParameters :=
  { agent12181 with charge := (63233509 / 50000000000 : ℝ) }

theorem agent_is_repriced12181 : agent12181 =
    BstLean.Part265.agentRepriced 12181 world12181 paperAgent12181 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12181, agent12181]

noncomputable def paperAgent12182 : AgentParameters :=
  { agent12182 with charge := (79022841 / 62500000000 : ℝ) }

theorem agent_is_repriced12182 : agent12182 =
    BstLean.Part265.agentRepriced 12182 world12182 paperAgent12182 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12182, agent12182]

noncomputable def paperAgent12183 : AgentParameters :=
  { agent12183 with charge := (79003819 / 62500000000 : ℝ) }

theorem agent_is_repriced12183 : agent12183 =
    BstLean.Part265.agentRepriced 12183 world12183 paperAgent12183 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12183, agent12183]

end BstLean.Part281
