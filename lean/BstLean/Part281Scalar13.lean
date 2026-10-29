import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12184 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12184. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12184 : WorldParameters where
  hiddenCharge := (1196168409 / 1000000000000 : ℝ)
  frame := (316539591581 / 500000000000 : ℝ)
  moment := (10513251171 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12184 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498731412377 / 1000000000000 : ℝ)
    root := (1868827333 / 250000000000 : ℝ) }

noncomputable def scalar12184 : ScalarCertificate 12184 world12184 agent12184 where
  dimensionLo := 12184
  dimensionHi := 12184
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2343207599 / 1000000000000 : ℝ)
  frameLo := (316539591581 / 500000000000 : ℝ)
  frameHi := (1498731412377 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12184]
  agentFrame_pos := by norm_num only [agent12184]
  worldRadius := (2343207599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12184]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1275756527 / 1000000000000 : ℝ)
  lowerTail := (1621784379 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7807620423 / 1000000000000 : ℝ)
  ledger := by
    have h : (1196168409 / 1000000000000 : ℚ) +
        (10513251171 / 1000000000000000000 : ℚ) / (2343207599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1275756527 / 1000000000000 : ℚ) + (1621784379 / 1000000000000 : ℚ) ≤
        (7807620423 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1196168409 / 1000000000000 : ℚ) +
        (10513251171 / 1000000000000000000 : ℚ) / (2343207599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1275756527 / 1000000000000 : ℚ) + (1621784379 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7807620423 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12184]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12184 :
    2 * 160 < 12184 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994677 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12184 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12185 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12185. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12185 : WorldParameters where
  hiddenCharge := (598059139 / 500000000000 : ℝ)
  frame := (316532057239 / 500000000000 : ℝ)
  moment := (1313874093 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12185 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749341535767 / 500000000000 : ℝ)
    root := (116791327 / 15625000000 : ℝ) }

noncomputable def scalar12185 : ScalarCertificate 12185 world12185 agent12185 where
  dimensionLo := 12185
  dimensionHi := 12185
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2343611599 / 1000000000000 : ℝ)
  frameLo := (316532057239 / 500000000000 : ℝ)
  frameHi := (749341535767 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12185]
  agentFrame_pos := by norm_num only [agent12185]
  worldRadius := (2343611599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12185]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1274617651 / 1000000000000 : ℝ)
  lowerTail := (1620442341 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7804018103 / 1000000000000 : ℝ)
  ledger := by
    have h : (598059139 / 500000000000 : ℚ) +
        (1313874093 / 125000000000000000 : ℚ) / (2343611599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1274617651 / 1000000000000 : ℚ) + (1620442341 / 1000000000000 : ℚ) ≤
        (7804018103 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((598059139 / 500000000000 : ℚ) +
        (1313874093 / 125000000000000000 : ℚ) / (2343611599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1274617651 / 1000000000000 : ℚ) + (1620442341 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7804018103 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12185]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12185 :
    2 * 160 < 12185 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999803 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12185 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12186 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12186. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12186 : WorldParameters where
  hiddenCharge := (3737713 / 3125000000 : ℝ)
  frame := (39565565521 / 62500000000 : ℝ)
  moment := (2101746999 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12186 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498634765127 / 1000000000000 : ℝ)
    root := (467123791 / 62500000000 : ℝ) }

noncomputable def scalar12186 : ScalarCertificate 12186 world12186 agent12186 where
  dimensionLo := 12186
  dimensionHi := 12186
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2344015699 / 1000000000000 : ℝ)
  frameLo := (39565565521 / 62500000000 : ℝ)
  frameHi := (1498634765127 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12186]
  agentFrame_pos := by norm_num only [agent12186]
  worldRadius := (2344015699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12186]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (127348001 / 100000000000 : ℝ)
  lowerTail := (1619101687 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7800419003 / 1000000000000 : ℝ)
  ledger := by
    have h : (3737713 / 3125000000 : ℚ) +
        (2101746999 / 200000000000000000 : ℚ) / (2344015699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127348001 / 100000000000 : ℚ) + (1619101687 / 1000000000000 : ℚ) ≤
        (7800419003 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((3737713 / 3125000000 : ℚ) +
        (2101746999 / 200000000000000000 : ℚ) / (2344015699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (127348001 / 100000000000 : ℚ) + (1619101687 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7800419003 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12186]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12186 :
    2 * 160 < 12186 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998291 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12186 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12187 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12187. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12187 : WorldParameters where
  hiddenCharge := (1196018057 / 1000000000000 : ℝ)
  frame := (633033984737 / 1000000000000 : ℝ)
  moment := (10506477923 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12187 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498586487091 / 1000000000000 : ℝ)
    root := (1868329167 / 250000000000 : ℝ) }

noncomputable def scalar12187 : ScalarCertificate 12187 world12187 agent12187 where
  dimensionLo := 12187
  dimensionHi := 12187
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2344419699 / 1000000000000 : ℝ)
  frameLo := (633033984737 / 1000000000000 : ℝ)
  frameHi := (1498586487091 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12187]
  agentFrame_pos := by norm_num only [agent12187]
  worldRadius := (2344419699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12187]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (63617177 / 50000000000 : ℝ)
  lowerTail := (1617762331 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1559364659 / 200000000000 : ℝ)
  ledger := by
    have h : (1196018057 / 1000000000000 : ℚ) +
        (10506477923 / 1000000000000000000 : ℚ) / (2344419699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (63617177 / 50000000000 : ℚ) + (1617762331 / 1000000000000 : ℚ) ≤
        (1559364659 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1196018057 / 1000000000000 : ℚ) +
        (10506477923 / 1000000000000000000 : ℚ) / (2344419699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (63617177 / 50000000000 : ℚ) + (1617762331 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1559364659 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12187]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12187 :
    2 * 160 < 12187 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996039 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12187 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12188 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12188. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12188 : WorldParameters where
  hiddenCharge := (1195967967 / 1000000000000 : ℝ)
  frame := (316509461839 / 500000000000 : ℝ)
  moment := (10504221529 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12188 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498538231363 / 1000000000000 : ℝ)
    root := (7472652813 / 1000000000000 : ℝ) }

noncomputable def scalar12188 : ScalarCertificate 12188 world12188 agent12188 where
  dimensionLo := 12188
  dimensionHi := 12188
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2344823699 / 1000000000000 : ℝ)
  frameLo := (316509461839 / 500000000000 : ℝ)
  frameHi := (1498538231363 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12188]
  agentFrame_pos := by norm_num only [agent12188]
  worldRadius := (2344823699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12188]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1271208181 / 1000000000000 : ℝ)
  lowerTail := (323284841 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7793230689 / 1000000000000 : ℝ)
  ledger := by
    have h : (1195967967 / 1000000000000 : ℚ) +
        (10504221529 / 1000000000000000000 : ℚ) / (2344823699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1271208181 / 1000000000000 : ℚ) + (323284841 / 200000000000 : ℚ) ≤
        (7793230689 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1195967967 / 1000000000000 : ℚ) +
        (10504221529 / 1000000000000000000 : ℚ) / (2344823699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1271208181 / 1000000000000 : ℚ) + (323284841 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7793230689 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12188]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12188 :
    2 * 160 < 12188 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999791 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12188 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12189 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12189. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12189 : WorldParameters where
  hiddenCharge := (1195917891 / 1000000000000 : ℝ)
  frame := (633003865161 / 1000000000000 : ℝ)
  moment := (2625491453 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12189 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749245005007 / 500000000000 : ℝ)
    root := (7471989241 / 1000000000000 : ℝ) }

noncomputable def scalar12189 : ScalarCertificate 12189 world12189 agent12189 where
  dimensionLo := 12189
  dimensionHi := 12189
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2345227699 / 1000000000000 : ℝ)
  frameLo := (633003865161 / 1000000000000 : ℝ)
  frameHi := (749245005007 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12189]
  agentFrame_pos := by norm_num only [agent12189]
  worldRadius := (2345227699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12189]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1270074089 / 1000000000000 : ℝ)
  lowerTail := (1615087493 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1947410381 / 250000000000 : ℝ)
  ledger := by
    have h : (1195917891 / 1000000000000 : ℚ) +
        (2625491453 / 250000000000000000 : ℚ) / (2345227699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1270074089 / 1000000000000 : ℚ) + (1615087493 / 1000000000000 : ℚ) ≤
        (1947410381 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1195917891 / 1000000000000 : ℚ) +
        (2625491453 / 250000000000000000 : ℚ) / (2345227699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1270074089 / 1000000000000 : ℚ) + (1615087493 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1947410381 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12189]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12189 :
    2 * 160 < 12189 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999027 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12189 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12190 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12190. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12190 : WorldParameters where
  hiddenCharge := (1195867829 / 1000000000000 : ℝ)
  frame := (632988809183 / 1000000000000 : ℝ)
  moment := (10499710771 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12190 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (299688362187 / 200000000000 : ℝ)
    root := (3735662901 / 500000000000 : ℝ) }

noncomputable def scalar12190 : ScalarCertificate 12190 world12190 agent12190 where
  dimensionLo := 12190
  dimensionHi := 12190
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2345631699 / 1000000000000 : ℝ)
  frameLo := (632988809183 / 1000000000000 : ℝ)
  frameHi := (299688362187 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12190]
  agentFrame_pos := by norm_num only [agent12190]
  worldRadius := (2345631699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12190]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (79308819 / 62500000000 : ℝ)
  lowerTail := (161375201 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3893027727 / 500000000000 : ℝ)
  ledger := by
    have h : (1195867829 / 1000000000000 : ℚ) +
        (10499710771 / 1000000000000000000 : ℚ) / (2345631699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (79308819 / 62500000000 : ℚ) + (161375201 / 100000000000 : ℚ) ≤
        (3893027727 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1195867829 / 1000000000000 : ℚ) +
        (10499710771 / 1000000000000000000 : ℚ) / (2345631699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (79308819 / 62500000000 : ℚ) + (161375201 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3893027727 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12190]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12190 :
    2 * 160 < 12190 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998213 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12190 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12191 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12191. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12191 : WorldParameters where
  hiddenCharge := (59790889 / 50000000000 : ℝ)
  frame := (19780429867 / 31250000000 : ℝ)
  moment := (10497456407 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12191 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187299205019 / 125000000000 : ℝ)
    root := (7470662571 / 1000000000000 : ℝ) }

noncomputable def scalar12191 : ScalarCertificate 12191 world12191 agent12191 where
  dimensionLo := 12191
  dimensionHi := 12191
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2346035699 / 1000000000000 : ℝ)
  frameLo := (19780429867 / 31250000000 : ℝ)
  frameHi := (187299205019 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12191]
  agentFrame_pos := by norm_num only [agent12191]
  worldRadius := (2346035699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12191]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (253561861 / 200000000000 : ℝ)
  lowerTail := (322483569 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3891236323 / 500000000000 : ℝ)
  ledger := by
    have h : (59790889 / 50000000000 : ℚ) +
        (10497456407 / 1000000000000000000 : ℚ) / (2346035699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253561861 / 200000000000 : ℚ) + (322483569 / 200000000000 : ℚ) ≤
        (3891236323 / 500000000000 : ℚ) := by norm_num only
    have hc : (((59790889 / 50000000000 : ℚ) +
        (10497456407 / 1000000000000000000 : ℚ) / (2346035699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253561861 / 200000000000 : ℚ) + (322483569 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3891236323 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12191]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12191 :
    2 * 160 < 12191 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996861 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12191 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12192 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12192. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12192 : WorldParameters where
  hiddenCharge := (597883873 / 500000000000 : ℝ)
  frame := (158239676211 / 250000000000 : ℝ)
  moment := (10495202719 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12192 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749172748823 / 500000000000 : ℝ)
    root := (7469999623 / 1000000000000 : ℝ) }

noncomputable def scalar12192 : ScalarCertificate 12192 world12192 agent12192 where
  dimensionLo := 12192
  dimensionHi := 12192
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2346439699 / 1000000000000 : ℝ)
  frameLo := (158239676211 / 250000000000 : ℝ)
  frameHi := (749172748823 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12192]
  agentFrame_pos := by norm_num only [agent12192]
  worldRadius := (2346439699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12192]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (253335749 / 200000000000 : ℝ)
  lowerTail := (1611085057 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1555778643 / 200000000000 : ℝ)
  ledger := by
    have h : (597883873 / 500000000000 : ℚ) +
        (10495202719 / 1000000000000000000 : ℚ) / (2346439699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253335749 / 200000000000 : ℚ) + (1611085057 / 1000000000000 : ℚ) ≤
        (1555778643 / 200000000000 : ℚ) := by norm_num only
    have hc : (((597883873 / 500000000000 : ℚ) +
        (10495202719 / 1000000000000000000 : ℚ) / (2346439699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (253335749 / 200000000000 : ℚ) + (1611085057 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1555778643 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12192]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12192 :
    2 * 160 < 12192 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999641 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12192 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12193 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12193. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12193 : WorldParameters where
  hiddenCharge := (47828709 / 40000000000 : ℝ)
  frame := (316471828241 / 500000000000 : ℝ)
  moment := (5246474853 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12193 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749148691699 / 500000000000 : ℝ)
    root := (7469336807 / 1000000000000 : ℝ) }

noncomputable def scalar12193 : ScalarCertificate 12193 world12193 agent12193 where
  dimensionLo := 12193
  dimensionHi := 12193
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2346843799 / 1000000000000 : ℝ)
  frameLo := (316471828241 / 500000000000 : ℝ)
  frameHi := (749148691699 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12193]
  agentFrame_pos := by norm_num only [agent12193]
  worldRadius := (2346843799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12193]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (632774693 / 500000000000 : ℝ)
  lowerTail := (402438403 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7775316921 / 1000000000000 : ℝ)
  ledger := by
    have h : (47828709 / 40000000000 : ℚ) +
        (5246474853 / 500000000000000000 : ℚ) / (2346843799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (632774693 / 500000000000 : ℚ) + (402438403 / 250000000000 : ℚ) ≤
        (7775316921 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((47828709 / 40000000000 : ℚ) +
        (5246474853 / 500000000000000000 : ℚ) / (2346843799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (632774693 / 500000000000 : ℚ) + (402438403 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7775316921 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12193]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12193 :
    2 * 160 < 12193 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995041 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12193 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12194 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12194. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12194 : WorldParameters where
  hiddenCharge := (597833859 / 500000000000 : ℝ)
  frame := (632928610657 / 1000000000000 : ℝ)
  moment := (1049069737 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12194 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498249291347 / 1000000000000 : ℝ)
    root := (7468674199 / 1000000000000 : ℝ) }

noncomputable def scalar12194 : ScalarCertificate 12194 world12194 agent12194 where
  dimensionLo := 12194
  dimensionHi := 12194
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2347247899 / 1000000000000 : ℝ)
  frameLo := (632928610657 / 1000000000000 : ℝ)
  frameHi := (1498249291347 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12194]
  agentFrame_pos := by norm_num only [agent12194]
  worldRadius := (2347247899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12194]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (252884237 / 200000000000 : ℝ)
  lowerTail := (32168469 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (310869753 / 40000000000 : ℝ)
  ledger := by
    have h : (597833859 / 500000000000 : ℚ) +
        (1049069737 / 100000000000000000 : ℚ) / (2347247899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (252884237 / 200000000000 : ℚ) + (32168469 / 20000000000 : ℚ) ≤
        (310869753 / 40000000000 : ℚ) := by norm_num only
    have hc : (((597833859 / 500000000000 : ℚ) +
        (1049069737 / 100000000000000000 : ℚ) / (2347247899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (252884237 / 200000000000 : ℚ) + (32168469 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((310869753 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12194]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12194 :
    2 * 160 < 12194 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998677 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12194 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12195 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12195. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12195 : WorldParameters where
  hiddenCharge := (47824709 / 40000000000 : ℝ)
  frame := (79114195921 / 125000000000 : ℝ)
  moment := (10488445709 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12195 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37455030839 / 25000000000 : ℝ)
    root := (7468011873 / 1000000000000 : ℝ) }

noncomputable def scalar12195 : ScalarCertificate 12195 world12195 agent12195 where
  dimensionLo := 12195
  dimensionHi := 12195
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2347651899 / 1000000000000 : ℝ)
  frameLo := (79114195921 / 125000000000 : ℝ)
  frameHi := (37455030839 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12195]
  agentFrame_pos := by norm_num only [agent12195]
  worldRadius := (2347651899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12195]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (157911771 / 125000000000 : ℝ)
  lowerTail := (1607094603 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7768174149 / 1000000000000 : ℝ)
  ledger := by
    have h : (47824709 / 40000000000 : ℚ) +
        (10488445709 / 1000000000000000000 : ℚ) / (2347651899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (157911771 / 125000000000 : ℚ) + (1607094603 / 1000000000000 : ℚ) ≤
        (7768174149 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((47824709 / 40000000000 : ℚ) +
        (10488445709 / 1000000000000000000 : ℚ) / (2347651899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (157911771 / 125000000000 : ℚ) + (1607094603 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7768174149 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12195]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12195 :
    2 * 160 < 12195 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995389 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12195 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12196 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12196. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12196 : WorldParameters where
  hiddenCharge := (597783873 / 500000000000 : ℝ)
  frame := (126579705323 / 200000000000 : ℝ)
  moment := (10486194723 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12196 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (374538299483 / 250000000000 : ℝ)
    root := (7467349679 / 1000000000000 : ℝ) }

noncomputable def scalar12196 : ScalarCertificate 12196 world12196 agent12196 where
  dimensionLo := 12196
  dimensionHi := 12196
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2348055899 / 1000000000000 : ℝ)
  frameLo := (126579705323 / 200000000000 : ℝ)
  frameHi := (374538299483 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12196]
  agentFrame_pos := by norm_num only [agent12196]
  worldRadius := (2348055899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12196]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1262168249 / 1000000000000 : ℝ)
  lowerTail := (1605766977 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3882303773 / 500000000000 : ℝ)
  ledger := by
    have h : (597783873 / 500000000000 : ℚ) +
        (10486194723 / 1000000000000000000 : ℚ) / (2348055899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1262168249 / 1000000000000 : ℚ) + (1605766977 / 1000000000000 : ℚ) ≤
        (3882303773 / 500000000000 : ℚ) := by norm_num only
    have hc : (((597783873 / 500000000000 : ℚ) +
        (10486194723 / 1000000000000000000 : ℚ) / (2348055899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1262168249 / 1000000000000 : ℚ) + (1605766977 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3882303773 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12196]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12196 :
    2 * 160 < 12196 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999631 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12196 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12197 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12197. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12197 : WorldParameters where
  hiddenCharge := (1195517781 / 1000000000000 : ℝ)
  frame := (632883488397 / 1000000000000 : ℝ)
  moment := (2620986103 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12197 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1498105190487 / 1000000000000 : ℝ)
    root := (1866671923 / 250000000000 : ℝ) }

noncomputable def scalar12197 : ScalarCertificate 12197 world12197 agent12197 where
  dimensionLo := 12197
  dimensionHi := 12197
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2348459999 / 1000000000000 : ℝ)
  frameLo := (632883488397 / 1000000000000 : ℝ)
  frameHi := (1498105190487 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12197]
  agentFrame_pos := by norm_num only [agent12197]
  worldRadius := (2348459999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12197]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (630521791 / 500000000000 : ℝ)
  lowerTail := (401110187 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7761044183 / 1000000000000 : ℝ)
  ledger := by
    have h : (1195517781 / 1000000000000 : ℚ) +
        (2620986103 / 250000000000000000 : ℚ) / (2348459999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (630521791 / 500000000000 : ℚ) + (401110187 / 250000000000 : ℚ) ≤
        (7761044183 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1195517781 / 1000000000000 : ℚ) +
        (2620986103 / 250000000000000000 : ℚ) / (2348459999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (630521791 / 500000000000 : ℚ) + (401110187 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7761044183 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12197]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12197 :
    2 * 160 < 12197 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997677 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12197 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12198 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12198. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12198 : WorldParameters where
  hiddenCharge := (1195467829 / 1000000000000 : ℝ)
  frame := (632868452713 / 1000000000000 : ℝ)
  moment := (1310211847 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12198 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187257151401 / 125000000000 : ℝ)
    root := (7466025987 / 1000000000000 : ℝ) }

noncomputable def scalar12198 : ScalarCertificate 12198 world12198 agent12198 where
  dimensionLo := 12198
  dimensionHi := 12198
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2348863999 / 1000000000000 : ℝ)
  frameLo := (632868452713 / 1000000000000 : ℝ)
  frameHi := (187257151401 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12198]
  agentFrame_pos := by norm_num only [agent12198]
  worldRadius := (2348863999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12198]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1259920071 / 1000000000000 : ℝ)
  lowerTail := (1603115799 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (484842761 / 62500000000 : ℝ)
  ledger := by
    have h : (1195467829 / 1000000000000 : ℚ) +
        (1310211847 / 125000000000000000 : ℚ) / (2348863999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1259920071 / 1000000000000 : ℚ) + (1603115799 / 1000000000000 : ℚ) ≤
        (484842761 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1195467829 / 1000000000000 : ℚ) +
        (1310211847 / 125000000000000000 : ℚ) / (2348863999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1259920071 / 1000000000000 : ℚ) + (1603115799 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((484842761 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12198]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12198 :
    2 * 160 < 12198 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999311 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12198 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12199 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12199. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12199 : WorldParameters where
  hiddenCharge := (1195417891 / 1000000000000 : ℝ)
  frame := (158213354891 / 250000000000 : ℝ)
  moment := (5239722907 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12199 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (749004630037 / 500000000000 : ℝ)
    root := (3732682207 / 500000000000 : ℝ) }

noncomputable def scalar12199 : ScalarCertificate 12199 world12199 agent12199 where
  dimensionLo := 12199
  dimensionHi := 12199
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2349268099 / 1000000000000 : ℝ)
  frameLo := (158213354891 / 250000000000 : ℝ)
  frameHi := (749004630037 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12199]
  agentFrame_pos := by norm_num only [agent12199]
  worldRadius := (2349268099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12199]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1258797753 / 1000000000000 : ℝ)
  lowerTail := (1601792183 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3876963643 / 500000000000 : ℝ)
  ledger := by
    have h : (1195417891 / 1000000000000 : ℚ) +
        (5239722907 / 500000000000000000 : ℚ) / (2349268099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1258797753 / 1000000000000 : ℚ) + (1601792183 / 1000000000000 : ℚ) ≤
        (3876963643 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1195417891 / 1000000000000 : ℚ) +
        (5239722907 / 500000000000000000 : ℚ) / (2349268099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1258797753 / 1000000000000 : ℚ) + (1601792183 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3876963643 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12199]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12199 :
    2 * 160 < 12199 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995721 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12199 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12200 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12200. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12200 : WorldParameters where
  hiddenCharge := (1195367967 / 1000000000000 : ℝ)
  frame := (632838388947 / 1000000000000 : ℝ)
  moment := (5238598763 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12200 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748980665513 / 500000000000 : ℝ)
    root := (7464703047 / 1000000000000 : ℝ) }

noncomputable def scalar12200 : ScalarCertificate 12200 world12200 agent12200 where
  dimensionLo := 12200
  dimensionHi := 12200
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2349672099 / 1000000000000 : ℝ)
  frameLo := (632838388947 / 1000000000000 : ℝ)
  frameHi := (748980665513 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12200]
  agentFrame_pos := by norm_num only [agent12200]
  worldRadius := (2349672099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12200]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1257676509 / 1000000000000 : ℝ)
  lowerTail := (320093951 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7750373571 / 1000000000000 : ℝ)
  ledger := by
    have h : (1195367967 / 1000000000000 : ℚ) +
        (5238598763 / 500000000000000000 : ℚ) / (2349672099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1257676509 / 1000000000000 : ℚ) + (320093951 / 200000000000 : ℚ) ≤
        (7750373571 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1195367967 / 1000000000000 : ℚ) +
        (5238598763 / 500000000000000000 : ℚ) / (2349672099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1257676509 / 1000000000000 : ℚ) + (320093951 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7750373571 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12200]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12200 :
    2 * 160 < 12200 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (34374997 / 3125000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12200 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12201 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12201. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12201 : WorldParameters where
  hiddenCharge := (1195318057 / 1000000000000 : ℝ)
  frame := (632823360863 / 1000000000000 : ℝ)
  moment := (1309368739 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12201 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1497913436129 / 1000000000000 : ℝ)
    root := (7464041963 / 1000000000000 : ℝ) }

noncomputable def scalar12201 : ScalarCertificate 12201 world12201 agent12201 where
  dimensionLo := 12201
  dimensionHi := 12201
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2350076099 / 1000000000000 : ℝ)
  frameLo := (632823360863 / 1000000000000 : ℝ)
  frameHi := (1497913436129 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12201]
  agentFrame_pos := by norm_num only [agent12201]
  worldRadius := (2350076099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12201]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (251311303 / 200000000000 : ℝ)
  lowerTail := (19989359 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3873411627 / 500000000000 : ℝ)
  ledger := by
    have h : (1195318057 / 1000000000000 : ℚ) +
        (1309368739 / 125000000000000000 : ℚ) / (2350076099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (251311303 / 200000000000 : ℚ) + (19989359 / 12500000000 : ℚ) ≤
        (3873411627 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1195318057 / 1000000000000 : ℚ) +
        (1309368739 / 125000000000000000 : ℚ) / (2350076099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (251311303 / 200000000000 : ℚ) + (19989359 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((3873411627 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12201]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12201 :
    2 * 160 < 12201 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499703 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12201 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12202 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12202. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12202 : WorldParameters where
  hiddenCharge := (3735213 / 3125000000 : ℝ)
  frame := (63280833531 / 100000000000 : ℝ)
  moment := (2618175743 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12202 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1497865563281 / 1000000000000 : ℝ)
    root := (7463381009 / 1000000000000 : ℝ) }

noncomputable def scalar12202 : ScalarCertificate 12202 world12202 agent12202 where
  dimensionLo := 12202
  dimensionHi := 12202
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2350480299 / 1000000000000 : ℝ)
  frameLo := (63280833531 / 100000000000 : ℝ)
  frameHi := (1497865563281 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12202]
  agentFrame_pos := by norm_num only [agent12202]
  worldRadius := (2350480299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12202]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1255437761 / 1000000000000 : ℝ)
  lowerTail := (1597829071 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (774327599 / 100000000000 : ℝ)
  ledger := by
    have h : (3735213 / 3125000000 : ℚ) +
        (2618175743 / 250000000000000000 : ℚ) / (2350480299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1255437761 / 1000000000000 : ℚ) + (1597829071 / 1000000000000 : ℚ) ≤
        (774327599 / 100000000000 : ℚ) := by norm_num only
    have hc : (((3735213 / 3125000000 : ℚ) +
        (2618175743 / 250000000000000000 : ℚ) / (2350480299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1255437761 / 1000000000000 : ℚ) + (1597829071 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((774327599 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12202]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12202 :
    2 * 160 < 12202 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999249 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12202 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12203 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12203. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12203 : WorldParameters where
  hiddenCharge := (597609139 / 500000000000 : ℝ)
  frame := (19774791009 / 31250000000 : ℝ)
  moment := (2094091341 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12203 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187227214813 / 125000000000 : ℝ)
    root := (7462720261 / 1000000000000 : ℝ) }

noncomputable def scalar12203 : ScalarCertificate 12203 world12203 agent12203 where
  dimensionLo := 12203
  dimensionHi := 12203
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2350884299 / 1000000000000 : ℝ)
  frameLo := (19774791009 / 31250000000 : ℝ)
  frameHi := (187227214813 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12203]
  agentFrame_pos := by norm_num only [agent12203]
  worldRadius := (2350884299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12203]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (627160013 / 500000000000 : ℝ)
  lowerTail := (399127637 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7739731947 / 1000000000000 : ℝ)
  ledger := by
    have h : (597609139 / 500000000000 : ℚ) +
        (2094091341 / 200000000000000000 : ℚ) / (2350884299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (627160013 / 500000000000 : ℚ) + (399127637 / 250000000000 : ℚ) ≤
        (7739731947 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((597609139 / 500000000000 : ℚ) +
        (2094091341 / 200000000000000000 : ℚ) / (2350884299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (627160013 / 500000000000 : ℚ) + (399127637 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7739731947 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12203]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12203 :
    2 * 160 < 12203 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998019 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12203 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12204 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12204. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12204 : WorldParameters where
  hiddenCharge := (1195168409 / 1000000000000 : ℝ)
  frame := (632778291797 / 1000000000000 : ℝ)
  moment := (10468211111 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12204 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1497769901781 / 1000000000000 : ℝ)
    root := (1492411959 / 200000000000 : ℝ) }

noncomputable def scalar12204 : ScalarCertificate 12204 world12204 agent12204 where
  dimensionLo := 12204
  dimensionHi := 12204
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2351288299 / 1000000000000 : ℝ)
  frameLo := (632778291797 / 1000000000000 : ℝ)
  frameHi := (1497769901781 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12204]
  agentFrame_pos := by norm_num only [agent12204]
  worldRadius := (2351288299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12204]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1253203513 / 1000000000000 : ℝ)
  lowerTail := (199399173 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3868095617 / 500000000000 : ℝ)
  ledger := by
    have h : (1195168409 / 1000000000000 : ℚ) +
        (10468211111 / 1000000000000000000 : ℚ) / (2351288299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1253203513 / 1000000000000 : ℚ) + (199399173 / 125000000000 : ℚ) ≤
        (3868095617 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1195168409 / 1000000000000 : ℚ) +
        (10468211111 / 1000000000000000000 : ℚ) / (2351288299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1253203513 / 1000000000000 : ℚ) + (199399173 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3868095617 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12204]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12204 :
    2 * 160 < 12204 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994597 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12204 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12205 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12205. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12205 : WorldParameters where
  hiddenCharge := (597559277 / 500000000000 : ℝ)
  frame := (126552654767 / 200000000000 : ℝ)
  moment := (1046596619 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12205 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (374430526763 / 250000000000 : ℝ)
    root := (373069973 / 50000000000 : ℝ) }

noncomputable def scalar12205 : ScalarCertificate 12205 world12205 agent12205 where
  dimensionLo := 12205
  dimensionHi := 12205
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2351692299 / 1000000000000 : ℝ)
  frameLo := (126552654767 / 200000000000 : ℝ)
  frameHi := (374430526763 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12205]
  agentFrame_pos := by norm_num only [agent12205]
  worldRadius := (2351692299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12205]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1252088087 / 1000000000000 : ℝ)
  lowerTail := (1593877427 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3866326783 / 500000000000 : ℝ)
  ledger := by
    have h : (597559277 / 500000000000 : ℚ) +
        (1046596619 / 100000000000000000 : ℚ) / (2351692299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1252088087 / 1000000000000 : ℚ) + (1593877427 / 1000000000000 : ℚ) ≤
        (3866326783 / 500000000000 : ℚ) := by norm_num only
    have hc : (((597559277 / 500000000000 : ℚ) +
        (1046596619 / 100000000000000000 : ℚ) / (2351692299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1252088087 / 1000000000000 : ℚ) + (1593877427 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3866326783 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12205]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12205 :
    2 * 160 < 12205 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999467 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12205 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12206 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12206. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12206 : WorldParameters where
  hiddenCharge := (149383589 / 125000000000 : ℝ)
  frame := (632748258403 / 1000000000000 : ℝ)
  moment := (5231860971 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12206 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (74883717017 / 50000000000 : ℝ)
    root := (746073933 / 100000000000 : ℝ) }

noncomputable def scalar12206 : ScalarCertificate 12206 world12206 agent12206 where
  dimensionLo := 12206
  dimensionHi := 12206
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2352096499 / 1000000000000 : ℝ)
  frameLo := (632748258403 / 1000000000000 : ℝ)
  frameHi := (74883717017 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12206]
  agentFrame_pos := by norm_num only [agent12206]
  worldRadius := (2352096499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12206]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1250973973 / 1000000000000 : ℝ)
  lowerTail := (1592562939 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7729119107 / 1000000000000 : ℝ)
  ledger := by
    have h : (149383589 / 125000000000 : ℚ) +
        (5231860971 / 500000000000000000 : ℚ) / (2352096499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1250973973 / 1000000000000 : ℚ) + (1592562939 / 1000000000000 : ℚ) ≤
        (7729119107 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((149383589 / 125000000000 : ℚ) +
        (5231860971 / 500000000000000000 : ℚ) / (2352096499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1250973973 / 1000000000000 : ℚ) + (1592562939 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7729119107 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12206]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12206 :
    2 * 160 < 12206 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (219999997 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12206 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12207 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12207. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12207 : WorldParameters where
  hiddenCharge := (298754721 / 250000000000 : ℝ)
  frame := (316366622749 / 500000000000 : ℝ)
  moment := (5230739183 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12207 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (748813303833 / 500000000000 : ℝ)
    root := (3730039741 / 500000000000 : ℝ) }

noncomputable def scalar12207 : ScalarCertificate 12207 world12207 agent12207 where
  dimensionLo := 12207
  dimensionHi := 12207
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2352500499 / 1000000000000 : ℝ)
  frameLo := (316366622749 / 500000000000 : ℝ)
  frameHi := (748813303833 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12207]
  agentFrame_pos := by norm_num only [agent12207]
  worldRadius := (2352500499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12207]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (156232619 / 125000000000 : ℝ)
  lowerTail := (795624831 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7725588021 / 1000000000000 : ℝ)
  ledger := by
    have h : (298754721 / 250000000000 : ℚ) +
        (5230739183 / 500000000000000000 : ℚ) / (2352500499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (156232619 / 125000000000 : ℚ) + (795624831 / 500000000000 : ℚ) ≤
        (7725588021 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((298754721 / 250000000000 : ℚ) +
        (5230739183 / 500000000000000000 : ℚ) / (2352500499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (156232619 / 125000000000 : ℚ) + (795624831 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7725588021 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12207]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12207 :
    2 * 160 < 12207 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994539 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12207 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12208 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12208. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12208 : WorldParameters where
  hiddenCharge := (119496907 / 100000000000 : ℝ)
  frame := (316359117561 / 500000000000 : ℝ)
  moment := (5229617731 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12208 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (374394722723 / 250000000000 : ℝ)
    root := (1864854941 / 250000000000 : ℝ) }

noncomputable def scalar12208 : ScalarCertificate 12208 world12208 agent12208 where
  dimensionLo := 12208
  dimensionHi := 12208
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2352904499 / 1000000000000 : ℝ)
  frameLo := (316359117561 / 500000000000 : ℝ)
  frameHi := (374394722723 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12208]
  agentFrame_pos := by norm_num only [agent12208]
  worldRadius := (2352904499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12208]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (124874899 / 100000000000 : ℝ)
  lowerTail := (794968779 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7722059917 / 1000000000000 : ℝ)
  ledger := by
    have h : (119496907 / 100000000000 : ℚ) +
        (5229617731 / 500000000000000000 : ℚ) / (2352904499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124874899 / 100000000000 : ℚ) + (794968779 / 500000000000 : ℚ) ≤
        (7722059917 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((119496907 / 100000000000 : ℚ) +
        (5229617731 / 500000000000000000 : ℚ) / (2352904499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124874899 / 100000000000 : ℚ) + (794968779 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7722059917 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12208]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12208 :
    2 * 160 < 12208 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999919 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12208 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12184 :
    (239233681689600897511 / 200000000000000000000000 : ℝ) ≤ world12184.hiddenCharge ∧
    (316539591580546175675661 / 500000000000000000000000 : ℝ) ≤ world12184.frame ∧
    (5256625585377667 / 500000000000000000000000 : ℝ) ≤ world12184.moment ∧
    (299746282475227242436481 / 200000000000000000000000 : ℝ) ≤ agent12184.frame ∧
    (3737654665799678441081 / 500000000000000000000000 : ℝ) ≤ agent12184.root ∧
    scalar12184.worldRadius ≤ (2343207599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (631878560469785673193 / 500000000000000000000000 : ℝ) ≤ agent12184.charge ∧
    (1275756526808251493713 / 1000000000000000000000000 : ℝ) ≤ scalar12184.upperTail ∧
    (25340380918553714399 / 15625000000000000000000 : ℝ) ≤ scalar12184.lowerTail ∧
    scalar12184.totalBudget ≤ (3903810211660686334557 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12184, agent12184, scalar12184] <;> simp only [true_and]

theorem source_rounding12185 :
    (119611827712108677727 / 100000000000000000000000 : ℝ) ≤ world12185.hiddenCharge ∧
    (633064114477078608801737 / 1000000000000000000000000 : ℝ) ≤ world12185.frame ∧
    (10510992743792233 / 1000000000000000000000000 : ℝ) ≤ world12185.moment ∧
    (23416922992705111773827 / 15625000000000000000000 : ℝ) ≤ agent12185.frame ∧
    (7474644927038603503099 / 1000000000000000000000000 : ℝ) ≤ agent12185.root ∧
    scalar12185.worldRadius ≤ (2343611599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (315863378173059144591 / 250000000000000000000000 : ℝ) ≤ agent12185.charge ∧
    (637308825307652240909 / 500000000000000000000000 : ℝ) ≤ scalar12185.upperTail ∧
    (1620442340381699439869 / 1000000000000000000000000 : ℝ) ≤ scalar12185.lowerTail ∧
    scalar12185.totalBudget ≤ (487751131470898964363 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12185, agent12185, scalar12185] <;> simp only [true_and]

theorem source_rounding12186 :
    (299017039911740732051 / 250000000000000000000000 : ℝ) ≤ world12186.hiddenCharge ∧
    (39565565520979147824287 / 62500000000000000000000 : ℝ) ≤ world12186.frame ∧
    (420349399783969 / 40000000000000000000000 : ℝ) ≤ world12186.moment ∧
    (299726953025241911260021 / 200000000000000000000000 : ℝ) ≤ agent12186.frame ∧
    (934247581901297278819 / 125000000000000000000000 : ℝ) ≤ agent12186.root ∧
    scalar12186.worldRadius ≤ (2344015699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (631575137697507026453 / 500000000000000000000000 : ℝ) ≤ agent12186.charge ∧
    (1273480009355838074283 / 1000000000000000000000000 : ℝ) ≤ scalar12186.upperTail ∧
    (323820337352321842777 / 200000000000000000000000 : ℝ) ≤ scalar12186.lowerTail ∧
    scalar12186.totalBudget ≤ (3900209501581509815937 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12186, agent12186, scalar12186] <;> simp only [true_and]

theorem source_rounding12187 :
    (1196018056020622766433 / 1000000000000000000000000 : ℝ) ≤ world12187.hiddenCharge ∧
    (633033984736171637707423 / 1000000000000000000000000 : ℝ) ≤ world12187.frame ∧
    (10506477922915239 / 1000000000000000000000000 : ℝ) ≤ world12187.moment ∧
    (1498586487090664014485249 / 1000000000000000000000000 : ℝ) ≤ agent12187.frame ∧
    (1494663333500435161799 / 200000000000000000000000 : ℝ) ≤ agent12187.root ∧
    scalar12187.worldRadius ≤ (2344419699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1262847408504614578307 / 1000000000000000000000000 : ℝ) ≤ agent12187.charge ∧
    (636171769998965657201 / 500000000000000000000000 : ℝ) ≤ scalar12187.upperTail ∧
    (25277536406525308553 / 15625000000000000000000 : ℝ) ≤ scalar12187.lowerTail ∧
    scalar12187.totalBudget ≤ (7796823295590895502593 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12187, agent12187, scalar12187] <;> simp only [true_and]

theorem source_rounding12188 :
    (597983983118529875241 / 500000000000000000000000 : ℝ) ≤ world12188.hiddenCharge ∧
    (633018923677910867821207 / 1000000000000000000000000 : ℝ) ≤ world12188.frame ∧
    (525211076423969 / 50000000000000000000000 : ℝ) ≤ world12188.moment ∧
    (299707646272578339580563 / 200000000000000000000000 : ℝ) ≤ agent12188.frame ∧
    (95649955997310347 / 12800000000000000000 : ℝ) ≤ agent12188.root ∧
    scalar12188.worldRadius ≤ (2344823699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (252508982295733736449 / 200000000000000000000000 : ℝ) ≤ agent12188.charge ∧
    (635604090196256530389 / 500000000000000000000000 : ℝ) ≤ scalar12188.upperTail ∧
    (404106051238096203023 / 250000000000000000000000 : ℝ) ≤ scalar12188.lowerTail ∧
    scalar12188.totalBudget ≤ (487076918123956582437 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12188, agent12188, scalar12188] <;> simp only [true_and]

theorem source_rounding12189 :
    (1195917890291269653039 / 1000000000000000000000000 : ℝ) ≤ world12189.hiddenCharge ∧
    (6330038651602005390489 / 10000000000000000000000 : ℝ) ≤ world12189.frame ∧
    (5250982905515441 / 500000000000000000000000 : ℝ) ≤ world12189.moment ∧
    (749245005006696040533463 / 500000000000000000000000 : ℝ) ≤ agent12189.frame ∧
    (7471989240898346279847 / 1000000000000000000000000 : ℝ) ≤ agent12189.root ∧
    scalar12189.worldRadius ≤ (2345227699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1262242783775724870921 / 1000000000000000000000000 : ℝ) ≤ agent12189.charge ∧
    (127007408853544818783 / 100000000000000000000000 : ℝ) ≤ scalar12189.upperTail ∧
    (403771873172428936807 / 250000000000000000000000 : ℝ) ≤ scalar12189.lowerTail ∧
    scalar12189.totalBudget ≤ (7789641524284688591311 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12189, agent12189, scalar12189] <;> simp only [true_and]

theorem source_rounding12190 :
    (239173565635650374539 / 200000000000000000000000 : ℝ) ≤ world12190.hiddenCharge ∧
    (316494404591178719501307 / 500000000000000000000000 : ℝ) ≤ world12190.frame ∧
    (328115961572161 / 31250000000000000000000 : ℝ) ≤ world12190.moment ∧
    (187305226366785827802603 / 125000000000000000000000 : ℝ) ≤ agent12190.frame ∧
    (7471325801766605863927 / 1000000000000000000000000 : ℝ) ≤ agent12190.root ∧
    scalar12190.worldRadius ≤ (2345631699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1261941024855247891797 / 1000000000000000000000000 : ℝ) ≤ agent12190.charge ∧
    (634470551846284045647 / 500000000000000000000000 : ℝ) ≤ scalar12190.upperTail ∧
    (25214875143729486859 / 15625000000000000000000 : ℝ) ≤ scalar12190.lowerTail ∧
    scalar12190.totalBudget ≤ (7786055454556267315561 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12190, agent12190, scalar12190] <;> simp only [true_and]

theorem source_rounding12191 :
    (1195817779893004179443 / 1000000000000000000000000 : ℝ) ≤ world12191.hiddenCharge ∧
    (632973755743698777140847 / 1000000000000000000000000 : ℝ) ≤ world12191.frame ∧
    (10497456406053571 / 1000000000000000000000000 : ℝ) ≤ world12191.moment ∧
    (299678728030249438690907 / 200000000000000000000000 : ℝ) ≤ agent12191.frame ∧
    (233458205327581345091 / 31250000000000000000000 : ℝ) ≤ agent12191.root ∧
    scalar12191.worldRadius ≤ (2346035699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (252327926835523399983 / 200000000000000000000000 : ℝ) ≤ agent12191.charge ∧
    (79238081506725427563 / 62500000000000000000000 : ℝ) ≤ scalar12191.upperTail ∧
    (50388057632521497843 / 31250000000000000000000 : ℝ) ≤ scalar12191.lowerTail ∧
    scalar12191.totalBudget ≤ (7782472646630987258011 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12191, agent12191, scalar12191] <;> simp only [true_and]

theorem source_rounding12192 :
    (597883872715265952901 / 500000000000000000000000 : ℝ) ≤ world12192.hiddenCharge ∧
    (632958704843541758730593 / 1000000000000000000000000 : ℝ) ≤ world12192.frame ∧
    (209904054360077 / 20000000000000000000000 : ℝ) ≤ world12192.moment ∧
    (149834549764536882245357 / 100000000000000000000000 : ℝ) ≤ agent12192.frame ∧
    (1867499905642876508659 / 250000000000000000000000 : ℝ) ≤ agent12192.root ∧
    scalar12192.worldRadius ≤ (2346439699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1261338611204124227777 / 1000000000000000000000000 : ℝ) ≤ agent12192.charge ∧
    (1266678744251067662439 / 1000000000000000000000000 : ℝ) ≤ scalar12192.upperTail ∧
    (1611085056319106243371 / 1000000000000000000000000 : ℝ) ≤ scalar12192.lowerTail ∧
    scalar12192.totalBudget ≤ (3889446607656071503251 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12192, agent12192, scalar12192] <;> simp only [true_and]

theorem source_rounding12193 :
    (74732357799114922137 / 62500000000000000000000 : ℝ) ≤ world12193.hiddenCharge ∧
    (25317746259248161043201 / 40000000000000000000000 : ℝ) ≤ world12193.frame ∧
    (1311618713237459 / 125000000000000000000000 : ℝ) ≤ world12193.moment ∧
    (1498297383397769977598911 / 1000000000000000000000000 : ℝ) ≤ agent12193.frame ∧
    (3734668403283521892711 / 500000000000000000000000 : ℝ) ≤ agent12193.root ∧
    scalar12193.worldRadius ≤ (2346843799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1261037955396972658801 / 1000000000000000000000000 : ℝ) ≤ agent12193.charge ∧
    (632774692813262093787 / 500000000000000000000000 : ℝ) ≤ scalar12193.upperTail ∧
    (1609753611346795738893 / 1000000000000000000000000 : ℝ) ≤ scalar12193.lowerTail ∧
    scalar12193.totalBudget ≤ (7775316921488556010733 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12193, agent12193, scalar12193] <;> simp only [true_and]

theorem source_rounding12194 :
    (1195667717953930736827 / 1000000000000000000000000 : ℝ) ≤ world12194.hiddenCharge ∧
    (632928610656003345403667 / 1000000000000000000000000 : ℝ) ≤ world12194.frame ∧
    (10490697369480843 / 1000000000000000000000000 : ℝ) ≤ world12194.moment ∧
    (5992997165386531144669 / 4000000000000000000000 : ℝ) ≤ agent12194.frame ∧
    (3734337099005201113809 / 500000000000000000000000 : ℝ) ≤ agent12194.root ∧
    scalar12194.worldRadius ≤ (2347247899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (126073766621927470433 / 100000000000000000000000 : ℝ) ≤ agent12194.charge ∧
    (126442118439226718311 / 100000000000000000000000 : ℝ) ≤ scalar12194.upperTail ∧
    (402105862326732926261 / 250000000000000000000000 : ℝ) ≤ scalar12194.lowerTail ∧
    scalar12194.totalBudget ≤ (1554348765145993027691 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12194, agent12194, scalar12194] <;> simp only [true_and]

theorem source_rounding12195 :
    (119561772492981748431 / 100000000000000000000000 : ℝ) ≤ world12195.hiddenCharge ∧
    (632913567367257822825603 / 1000000000000000000000000 : ℝ) ≤ world12195.frame ∧
    (10488445708487347 / 1000000000000000000000000 : ℝ) ≤ world12195.moment ∧
    (749100616779657418397697 / 500000000000000000000000 : ℝ) ≤ agent12195.frame ∧
    (7468011872380045498379 / 1000000000000000000000000 : ℝ) ≤ agent12195.root ∧
    scalar12195.worldRadius ≤ (2347651899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1260437743135050384187 / 1000000000000000000000000 : ℝ) ≤ agent12195.charge ∧
    (252658833415986455213 / 200000000000000000000000 : ℝ) ≤ scalar12195.upperTail ∧
    (401773650738574468131 / 250000000000000000000000 : ℝ) ≤ scalar12195.lowerTail ∧
    scalar12195.totalBudget ≤ (3884087074638862446793 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12195, agent12195, scalar12195] <;> simp only [true_and]

theorem source_rounding12196 :
    (298891936427127732943 / 250000000000000000000000 : ℝ) ≤ world12196.hiddenCharge ∧
    (158224631653571453005289 / 250000000000000000000000 : ℝ) ≤ world12196.frame ∧
    (2097238944531859 / 200000000000000000000000 : ℝ) ≤ world12196.moment ∧
    (1498153197931357772603181 / 1000000000000000000000000 : ℝ) ≤ agent12196.frame ∧
    (1866837419576082570491 / 250000000000000000000000 : ℝ) ≤ agent12196.root ∧
    scalar12196.worldRadius ≤ (2348055899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1260138185609225610771 / 1000000000000000000000000 : ℝ) ≤ agent12196.charge ∧
    (315542062162593997677 / 250000000000000000000000 : ℝ) ≤ scalar12196.upperTail ∧
    (160576697674443016561 / 100000000000000000000000 : ℝ) ≤ scalar12196.lowerTail ∧
    scalar12196.totalBudget ≤ (3882303773012621338947 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12196, agent12196, scalar12196] <;> simp only [true_and]

theorem source_rounding12197 :
    (298879445071256329373 / 250000000000000000000000 : ℝ) ≤ world12197.hiddenCharge ∧
    (158220872099101484155779 / 250000000000000000000000 : ℝ) ≤ world12197.frame ∧
    (262098610293423 / 25000000000000000000000 : ℝ) ≤ world12197.moment ∧
    (187263148810866595157759 / 125000000000000000000000 : ℝ) ≤ agent12197.frame ∧
    (1493337538255544277903 / 200000000000000000000000 : ℝ) ≤ agent12197.root ∧
    scalar12197.worldRadius ≤ (2348459999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1259838993107630476689 / 1000000000000000000000000 : ℝ) ≤ agent12197.charge ∧
    (315260895375381922467 / 250000000000000000000000 : ℝ) ≤ scalar12197.upperTail ∧
    (320888149458804278017 / 200000000000000000000000 : ℝ) ≤ scalar12197.lowerTail ∧
    scalar12197.totalBudget ≤ (1940261045984921169223 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12197, agent12197, scalar12197] <;> simp only [true_and]

theorem source_rounding12198 :
    (597733914327187936717 / 500000000000000000000000 : ℝ) ≤ world12198.hiddenCharge ∧
    (632868452712936857782571 / 1000000000000000000000000 : ℝ) ≤ world12198.frame ∧
    (2620423693865133 / 250000000000000000000000 : ℝ) ≤ world12198.moment ∧
    (74902860560363725523903 / 50000000000000000000000 : ℝ) ≤ agent12198.frame ∧
    (3733012993366012583991 / 500000000000000000000000 : ℝ) ≤ agent12198.root ∧
    scalar12198.worldRadius ≤ (2348863999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (314885041274249386479 / 250000000000000000000000 : ℝ) ≤ agent12198.charge ∧
    (251984014114731509353 / 200000000000000000000000 : ℝ) ≤ scalar12198.upperTail ∧
    (400778949529702209643 / 250000000000000000000000 : ℝ) ≤ scalar12198.lowerTail ∧
    scalar12198.totalBudget ≤ (7757484176202807956983 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12198, agent12198, scalar12198] <;> simp only [true_and]

theorem source_rounding12199 :
    (1195417890811580134479 / 1000000000000000000000000 : ℝ) ≤ world12199.hiddenCharge ∧
    (158213354890799446101113 / 250000000000000000000000 : ℝ) ≤ world12199.frame ∧
    (10479445813570561 / 1000000000000000000000000 : ℝ) ≤ world12199.moment ∧
    (1498009260073640989081181 / 1000000000000000000000000 : ℝ) ≤ agent12199.frame ∧
    (7465364413390128766129 / 1000000000000000000000000 : ℝ) ≤ agent12199.root ∧
    scalar12199.worldRadius ≤ (2349268099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1259241701044960148461 / 1000000000000000000000000 : ℝ) ≤ agent12199.charge ∧
    (157349719041063391283 / 125000000000000000000000 : ℝ) ≤ scalar12199.upperTail ∧
    (800896091400880865843 / 500000000000000000000000 : ℝ) ≤ scalar12199.lowerTail ∧
    scalar12199.totalBudget ≤ (3101570914419384999 / 400000000000000000000 : ℝ) := by
  norm_num only [world12199, agent12199, scalar12199] <;> simp only [true_and]

theorem source_rounding12200 :
    (597683983375829621949 / 500000000000000000000000 : ℝ) ≤ world12200.hiddenCharge ∧
    (632838388946508058344957 / 1000000000000000000000000 : ℝ) ≤ world12200.frame ∧
    (10477197525807619 / 1000000000000000000000000 : ℝ) ≤ world12200.moment ∧
    (748980665512994177559903 / 500000000000000000000000 : ℝ) ≤ agent12200.frame ∧
    (1866175761674955547873 / 250000000000000000000000 : ℝ) ≤ agent12200.root ∧
    scalar12200.worldRadius ≤ (2349672099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (314735900105012669639 / 250000000000000000000000 : ℝ) ≤ agent12200.charge ∧
    (628838254327612823803 / 500000000000000000000000 : ℝ) ≤ scalar12200.upperTail ∧
    (800234877192750811433 / 500000000000000000000000 : ℝ) ≤ scalar12200.lowerTail ∧
    scalar12200.totalBudget ≤ (3875186785832115564177 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12200, agent12200, scalar12200] <;> simp only [true_and]

theorem source_rounding12201 :
    (298829514117408834103 / 250000000000000000000000 : ℝ) ≤ world12201.hiddenCharge ∧
    (158205840215546787572551 / 250000000000000000000000 : ℝ) ≤ world12201.frame ∧
    (10474949911912387 / 1000000000000000000000000 : ℝ) ≤ world12201.moment ∧
    (1497913436128542949967307 / 1000000000000000000000000 : ℝ) ≤ agent12201.frame ∧
    (3732020981023150115649 / 500000000000000000000000 : ℝ) ≤ agent12201.root ∧
    scalar12201.worldRadius ≤ (2350076099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1258645862691698896337 / 1000000000000000000000000 : ℝ) ≤ agent12201.charge ∧
    (1256556514770597760621 / 1000000000000000000000000 : ℝ) ≤ scalar12201.upperTail ∧
    (1599148719717576332267 / 1000000000000000000000000 : ℝ) ≤ scalar12201.lowerTail ∧
    scalar12201.totalBudget ≤ (3873411627095655873031 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12201, agent12201, scalar12201] <;> simp only [true_and]

theorem source_rounding12202 :
    (298817039990133211387 / 250000000000000000000000 : ℝ) ≤ world12202.hiddenCharge ∧
    (126561667061910999578641 / 200000000000000000000000 : ℝ) ≤ world12202.frame ∧
    (1309087871453209 / 125000000000000000000000 : ℝ) ≤ world12202.moment ∧
    (74893278164012691354813 / 50000000000000000000000 : ℝ) ≤ agent12202.frame ∧
    (3731690504123441683271 / 500000000000000000000000 : ℝ) ≤ agent12202.root ∧
    scalar12202.worldRadius ≤ (2350480299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (125834848733023023303 / 100000000000000000000000 : ℝ) ≤ agent12202.charge ∧
    (7846486001836300499 / 6250000000000000000000 : ℝ) ≤ scalar12202.upperTail ∧
    (1597829070636939639349 / 1000000000000000000000000 : ℝ) ≤ scalar12202.lowerTail ∧
    scalar12202.totalBudget ≤ (7743275990343871996817 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12202, agent12202, scalar12202] <;> simp only [true_and]

theorem source_rounding12203 :
    (1195218277219379807237 / 1000000000000000000000000 : ℝ) ≤ world12203.hiddenCharge ∧
    (632793312287931616544087 / 1000000000000000000000000 : ℝ) ≤ world12203.frame ∧
    (5235228352344229 / 500000000000000000000000 : ℝ) ≤ world12203.moment ∧
    (748908859251898117485843 / 500000000000000000000000 : ℝ) ≤ agent12203.frame ∧
    (466420016293920816169 / 62500000000000000000000 : ℝ) ≤ agent12203.root ∧
    scalar12203.worldRadius ≤ (2350884299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (157256434225858012451 / 125000000000000000000000 : ℝ) ≤ agent12203.charge ∧
    (627160012666823396589 / 500000000000000000000000 : ℝ) ≤ scalar12203.upperTail ∧
    (1596510547882665035797 / 1000000000000000000000000 : ℝ) ≤ scalar12203.lowerTail ∧
    scalar12203.totalBudget ≤ (773973194722849782033 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12203, agent12203, scalar12203] <;> simp only [true_and]

theorem source_rounding12204 :
    (298792102060301311659 / 250000000000000000000000 : ℝ) ≤ world12204.hiddenCharge ∧
    (31638914589831866529731 / 50000000000000000000000 : ℝ) ≤ world12204.frame ∧
    (10468211110841803 / 1000000000000000000000000 : ℝ) ≤ world12204.moment ∧
    (1497769901780543493133589 / 1000000000000000000000000 : ℝ) ≤ agent12204.frame ∧
    (1492411958950495741171 / 200000000000000000000000 : ℝ) ≤ agent12204.root ∧
    scalar12204.worldRadius ≤ (2351288299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (39304838174803506217 / 31250000000000000000000 : ℝ) ≤ agent12204.charge ∧
    (1253203512434610170751 / 1000000000000000000000000 : ℝ) ≤ scalar12204.upperTail ∧
    (319038676690206012033 / 200000000000000000000000 : ℝ) ≤ scalar12204.lowerTail ∧
    scalar12204.totalBudget ≤ (7736191234409366543237 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12204, agent12204, scalar12204] <;> simp only [true_and]

theorem source_rounding12205 :
    (2987796382552601209 / 2500000000000000000000 : ℝ) ≤ world12205.hiddenCharge ∧
    (632763273834992757626841 / 1000000000000000000000000 : ℝ) ≤ world12205.frame ∧
    (5232983094913443 / 500000000000000000000000 : ℝ) ≤ world12205.moment ∧
    (748861053525962391282593 / 500000000000000000000000 : ℝ) ≤ agent12205.frame ∧
    (1865349864826944282461 / 250000000000000000000000 : ℝ) ≤ agent12205.root ∧
    scalar12205.worldRadius ≤ (2351692299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (78591158135236052589 / 62500000000000000000000 : ℝ) ≤ agent12205.charge ∧
    (125208808636979157991 / 100000000000000000000000 : ℝ) ≤ scalar12205.upperTail ∧
    (1593877426374659941901 / 1000000000000000000000000 : ℝ) ≤ scalar12205.lowerTail ∧
    scalar12205.totalBudget ≤ (3866326783270664102411 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12205, agent12205, scalar12205] <;> simp only [true_and]

theorem source_rounding12206 :
    (597534355776958914113 / 500000000000000000000000 : ℝ) ≤ world12206.hiddenCharge ∧
    (5061986067218549444231 / 8000000000000000000000 : ℝ) ≤ world12206.frame ∧
    (5231860970692481 / 500000000000000000000000 : ℝ) ≤ world12206.moment ∧
    (748837170169934470258161 / 500000000000000000000000 : ℝ) ≤ agent12206.frame ∧
    (3730369664861603721833 / 500000000000000000000000 : ℝ) ≤ agent12206.root ∧
    scalar12206.worldRadius ≤ (2352096499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1257162598990949264029 / 1000000000000000000000000 : ℝ) ≤ agent12206.charge ∧
    (1250973972456448806883 / 1000000000000000000000000 : ℝ) ≤ scalar12206.upperTail ∧
    (1592562938811813268401 / 1000000000000000000000000 : ℝ) ≤ scalar12206.lowerTail ∧
    scalar12206.totalBudget ≤ (3864559553651270905281 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12206, agent12206, scalar12206] <;> simp only [true_and]

theorem source_rounding12207 :
    (47800755353394979601 / 40000000000000000000000 : ℝ) ≤ world12207.hiddenCharge ∧
    (25309329819917449170777 / 40000000000000000000000 : ℝ) ≤ world12207.frame ∧
    (10461478365257513 / 1000000000000000000000000 : ℝ) ≤ world12207.moment ∧
    (1497626607665243125595121 / 1000000000000000000000000 : ℝ) ≤ agent12207.frame ∧
    (3730039740645439883493 / 500000000000000000000000 : ℝ) ≤ agent12207.root ∧
    scalar12207.worldRadius ≤ (2352500499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (314216756887501988217 / 250000000000000000000000 : ℝ) ≤ agent12207.charge ∧
    (1249860951219457364273 / 1000000000000000000000000 : ℝ) ≤ scalar12207.upperTail ∧
    (1591249661947458801023 / 1000000000000000000000000 : ℝ) ≤ scalar12207.lowerTail ∧
    scalar12207.totalBudget ≤ (3862794010892787259791 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12207, agent12207, scalar12207] <;> simp only [true_and]

theorem source_rounding12208 :
    (238993813971789732953 / 200000000000000000000000 : ℝ) ≤ world12208.hiddenCharge ∧
    (632718235121166694894997 / 1000000000000000000000000 : ℝ) ≤ world12208.frame ∧
    (10459235461186093 / 1000000000000000000000000 : ℝ) ≤ world12208.moment ∧
    (1497578890891236750171887 / 1000000000000000000000000 : ℝ) ≤ agent12208.frame ∧
    (7459419763016690411739 / 1000000000000000000000000 : ℝ) ≤ agent12208.root ∧
    scalar12208.worldRadius ≤ (2352904499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1256571815316616969169 / 1000000000000000000000000 : ℝ) ≤ agent12208.charge ∧
    (249749797923240687077 / 200000000000000000000000 : ℝ) ≤ scalar12208.upperTail ∧
    (31798751151617711819 / 20000000000000000000000 : ℝ) ≤ scalar12208.lowerTail ∧
    scalar12208.totalBudget ≤ (7722059917717934819397 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12208, agent12208, scalar12208] <;> simp only [true_and]

noncomputable def paperAgent12184 : AgentParameters :=
  { agent12184 with charge := (315939281 / 250000000000 : ℝ) }

theorem agent_is_repriced12184 : agent12184 =
    BstLean.Part265.agentRepriced 12184 world12184 paperAgent12184 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12184, agent12184]

noncomputable def paperAgent12185 : AgentParameters :=
  { agent12185 with charge := (315863379 / 250000000000 : ℝ) }

theorem agent_is_repriced12185 : agent12185 =
    BstLean.Part265.agentRepriced 12185 world12185 paperAgent12185 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12185, agent12185]

noncomputable def paperAgent12186 : AgentParameters :=
  { agent12186 with charge := (631575139 / 500000000000 : ℝ) }

theorem agent_is_repriced12186 : agent12186 =
    BstLean.Part265.agentRepriced 12186 world12186 paperAgent12186 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12186, agent12186]

noncomputable def paperAgent12187 : AgentParameters :=
  { agent12187 with charge := (1262847411 / 1000000000000 : ℝ) }

theorem agent_is_repriced12187 : agent12187 =
    BstLean.Part265.agentRepriced 12187 world12187 paperAgent12187 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12187, agent12187]

noncomputable def paperAgent12188 : AgentParameters :=
  { agent12188 with charge := (631272457 / 500000000000 : ℝ) }

theorem agent_is_repriced12188 : agent12188 =
    BstLean.Part265.agentRepriced 12188 world12188 paperAgent12188 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12188, agent12188]

noncomputable def paperAgent12189 : AgentParameters :=
  { agent12189 with charge := (1262242787 / 1000000000000 : ℝ) }

theorem agent_is_repriced12189 : agent12189 =
    BstLean.Part265.agentRepriced 12189 world12189 paperAgent12189 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12189, agent12189]

noncomputable def paperAgent12190 : AgentParameters :=
  { agent12190 with charge := (315485257 / 250000000000 : ℝ) }

theorem agent_is_repriced12190 : agent12190 =
    BstLean.Part265.agentRepriced 12190 world12190 paperAgent12190 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12190, agent12190]

noncomputable def paperAgent12191 : AgentParameters :=
  { agent12191 with charge := (630819819 / 500000000000 : ℝ) }

theorem agent_is_repriced12191 : agent12191 =
    BstLean.Part265.agentRepriced 12191 world12191 paperAgent12191 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12191, agent12191]

noncomputable def paperAgent12192 : AgentParameters :=
  { agent12192 with charge := (630669307 / 500000000000 : ℝ) }

theorem agent_is_repriced12192 : agent12192 =
    BstLean.Part265.agentRepriced 12192 world12192 paperAgent12192 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12192, agent12192]

noncomputable def paperAgent12193 : AgentParameters :=
  { agent12193 with charge := (1261037959 / 1000000000000 : ℝ) }

theorem agent_is_repriced12193 : agent12193 =
    BstLean.Part265.agentRepriced 12193 world12193 paperAgent12193 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12193, agent12193]

noncomputable def paperAgent12194 : AgentParameters :=
  { agent12194 with charge := (126073767 / 100000000000 : ℝ) }

theorem agent_is_repriced12194 : agent12194 =
    BstLean.Part265.agentRepriced 12194 world12194 paperAgent12194 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12194, agent12194]

noncomputable def paperAgent12195 : AgentParameters :=
  { agent12195 with charge := (630218873 / 500000000000 : ℝ) }

theorem agent_is_repriced12195 : agent12195 =
    BstLean.Part265.agentRepriced 12195 world12195 paperAgent12195 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12195, agent12195]

noncomputable def paperAgent12196 : AgentParameters :=
  { agent12196 with charge := (1260138189 / 1000000000000 : ℝ) }

theorem agent_is_repriced12196 : agent12196 =
    BstLean.Part265.agentRepriced 12196 world12196 paperAgent12196 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12196, agent12196]

noncomputable def paperAgent12197 : AgentParameters :=
  { agent12197 with charge := (1259838997 / 1000000000000 : ℝ) }

theorem agent_is_repriced12197 : agent12197 =
    BstLean.Part265.agentRepriced 12197 world12197 paperAgent12197 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12197, agent12197]

noncomputable def paperAgent12198 : AgentParameters :=
  { agent12198 with charge := (157442521 / 125000000000 : ℝ) }

theorem agent_is_repriced12198 : agent12198 =
    BstLean.Part265.agentRepriced 12198 world12198 paperAgent12198 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12198, agent12198]

noncomputable def paperAgent12199 : AgentParameters :=
  { agent12199 with charge := (157405213 / 125000000000 : ℝ) }

theorem agent_is_repriced12199 : agent12199 =
    BstLean.Part265.agentRepriced 12199 world12199 paperAgent12199 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12199, agent12199]

noncomputable def paperAgent12200 : AgentParameters :=
  { agent12200 with charge := (314735901 / 250000000000 : ℝ) }

theorem agent_is_repriced12200 : agent12200 =
    BstLean.Part265.agentRepriced 12200 world12200 paperAgent12200 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12200, agent12200]

noncomputable def paperAgent12201 : AgentParameters :=
  { agent12201 with charge := (629322933 / 500000000000 : ℝ) }

theorem agent_is_repriced12201 : agent12201 =
    BstLean.Part265.agentRepriced 12201 world12201 paperAgent12201 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12201, agent12201]

noncomputable def paperAgent12202 : AgentParameters :=
  { agent12202 with charge := (1258348491 / 1000000000000 : ℝ) }

theorem agent_is_repriced12202 : agent12202 =
    BstLean.Part265.agentRepriced 12202 world12202 paperAgent12202 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12202, agent12202]

noncomputable def paperAgent12203 : AgentParameters :=
  { agent12203 with charge := (1258051477 / 1000000000000 : ℝ) }

theorem agent_is_repriced12203 : agent12203 =
    BstLean.Part265.agentRepriced 12203 world12203 paperAgent12203 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12203, agent12203]

noncomputable def paperAgent12204 : AgentParameters :=
  { agent12204 with charge := (50310193 / 40000000000 : ℝ) }

theorem agent_is_repriced12204 : agent12204 =
    BstLean.Part265.agentRepriced 12204 world12204 paperAgent12204 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12204, agent12204]

noncomputable def paperAgent12205 : AgentParameters :=
  { agent12205 with charge := (1257458533 / 1000000000000 : ℝ) }

theorem agent_is_repriced12205 : agent12205 =
    BstLean.Part265.agentRepriced 12205 world12205 paperAgent12205 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12205, agent12205]

noncomputable def paperAgent12206 : AgentParameters :=
  { agent12206 with charge := (628581301 / 500000000000 : ℝ) }

theorem agent_is_repriced12206 : agent12206 =
    BstLean.Part265.agentRepriced 12206 world12206 paperAgent12206 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12206, agent12206]

noncomputable def paperAgent12207 : AgentParameters :=
  { agent12207 with charge := (1256867031 / 1000000000000 : ℝ) }

theorem agent_is_repriced12207 : agent12207 =
    BstLean.Part265.agentRepriced 12207 world12207 paperAgent12207 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12207, agent12207]

noncomputable def paperAgent12208 : AgentParameters :=
  { agent12208 with charge := (628285909 / 500000000000 : ℝ) }

theorem agent_is_repriced12208 : agent12208 =
    BstLean.Part265.agentRepriced 12208 world12208 paperAgent12208 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12208, agent12208]

end BstLean.Part281
