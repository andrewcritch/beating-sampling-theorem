import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12084 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12084. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12084 : WorldParameters where
  hiddenCharge := (75078273 / 62500000000 : ℝ)
  frame := (634599010253 / 1000000000000 : ℝ)
  moment := (1074256197 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12084 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503647036279 / 1000000000000 : ℝ)
    root := (3771414067 / 500000000000 : ℝ) }

noncomputable def scalar12084 : ScalarCertificate 12084 world12084 agent12084 where
  dimensionLo := 12084
  dimensionHi := 12084
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2302898699 / 1000000000000 : ℝ)
  frameLo := (634599010253 / 1000000000000 : ℝ)
  frameHi := (1503647036279 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12084]
  agentFrame_pos := by norm_num only [agent12084]
  worldRadius := (2302898699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12084]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1395724913 / 1000000000000 : ℝ)
  lowerTail := (881343497 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4092215653 / 500000000000 : ℝ)
  ledger := by
    have h : (75078273 / 62500000000 : ℚ) +
        (1074256197 / 100000000000000000 : ℚ) / (2302898699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1395724913 / 1000000000000 : ℚ) + (881343497 / 500000000000 : ℚ) ≤
        (4092215653 / 500000000000 : ℚ) := by norm_num only
    have hc : (((75078273 / 62500000000 : ℚ) +
        (1074256197 / 100000000000000000 : ℚ) / (2302898699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1395724913 / 1000000000000 : ℚ) + (881343497 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4092215653 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12084]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12084 :
    2 * 160 < 12084 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997323 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12084 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12085 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12085. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12085 : WorldParameters where
  hiddenCharge := (600600413 / 500000000000 : ℝ)
  frame := (634583683811 / 1000000000000 : ℝ)
  moment := (10740234427 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12085 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503596931357 / 1000000000000 : ℝ)
    root := (377107109 / 50000000000 : ℝ) }

noncomputable def scalar12085 : ScalarCertificate 12085 world12085 agent12085 where
  dimensionLo := 12085
  dimensionHi := 12085
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2303301099 / 1000000000000 : ℝ)
  frameLo := (634583683811 / 1000000000000 : ℝ)
  frameHi := (1503596931357 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12085]
  agentFrame_pos := by norm_num only [agent12085]
  worldRadius := (2303301099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12085]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1394462903 / 1000000000000 : ℝ)
  lowerTail := (440302337 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1636098733 / 200000000000 : ℝ)
  ledger := by
    have h : (600600413 / 500000000000 : ℚ) +
        (10740234427 / 1000000000000000000 : ℚ) / (2303301099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1394462903 / 1000000000000 : ℚ) + (440302337 / 250000000000 : ℚ) ≤
        (1636098733 / 200000000000 : ℚ) := by norm_num only
    have hc : (((600600413 / 500000000000 : ℚ) +
        (10740234427 / 1000000000000000000 : ℚ) / (2303301099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1394462903 / 1000000000000 : ℚ) + (440302337 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1636098733 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12085]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12085 :
    2 * 160 < 12085 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997761 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12085 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12086 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12086. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12086 : WorldParameters where
  hiddenCharge := (600574649 / 500000000000 : ℝ)
  frame := (317284179991 / 500000000000 : ℝ)
  moment := (2684476897 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12086 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (75177342837 / 50000000000 : ℝ)
    root := (117835257 / 15625000000 : ℝ) }

noncomputable def scalar12086 : ScalarCertificate 12086 world12086 agent12086 where
  dimensionLo := 12086
  dimensionHi := 12086
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2303703399 / 1000000000000 : ℝ)
  frameLo := (317284179991 / 500000000000 : ℝ)
  frameHi := (75177342837 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12086]
  agentFrame_pos := by norm_num only [agent12086]
  worldRadius := (2303703399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12086]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (696601077 / 500000000000 : ℝ)
  lowerTail := (175973309 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8176559673 / 1000000000000 : ℝ)
  ledger := by
    have h : (600574649 / 500000000000 : ℚ) +
        (2684476897 / 250000000000000000 : ℚ) / (2303703399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (696601077 / 500000000000 : ℚ) + (175973309 / 100000000000 : ℚ) ≤
        (8176559673 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((600574649 / 500000000000 : ℚ) +
        (2684476897 / 250000000000000000 : ℚ) / (2303703399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (696601077 / 500000000000 : ℚ) + (175973309 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8176559673 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12086]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12086 :
    2 * 160 < 12086 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999903 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12086 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12087 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12087. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12087 : WorldParameters where
  hiddenCharge := (150137223 / 125000000000 : ℝ)
  frame := (158638259691 / 250000000000 : ℝ)
  moment := (10735581453 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12087 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (18793710231 / 12500000000 : ℝ)
    root := (3770385469 / 500000000000 : ℝ) }

noncomputable def scalar12087 : ScalarCertificate 12087 world12087 agent12087 where
  dimensionLo := 12087
  dimensionHi := 12087
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2304105699 / 1000000000000 : ℝ)
  frameLo := (158638259691 / 250000000000 : ℝ)
  frameHi := (18793710231 / 12500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12087]
  agentFrame_pos := by norm_num only [agent12087]
  worldRadius := (2304105699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12087]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1391942771 / 1000000000000 : ℝ)
  lowerTail := (439564587 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8172629387 / 1000000000000 : ℝ)
  ledger := by
    have h : (150137223 / 125000000000 : ℚ) +
        (10735581453 / 1000000000000000000 : ℚ) / (2304105699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1391942771 / 1000000000000 : ℚ) + (439564587 / 250000000000 : ℚ) ≤
        (8172629387 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((150137223 / 125000000000 : ℚ) +
        (10735581453 / 1000000000000000000 : ℚ) / (2304105699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1391942771 / 1000000000000 : ℚ) + (439564587 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8172629387 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12087]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12087 :
    2 * 160 < 12087 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994217 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12087 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12088 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12088. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12088 : WorldParameters where
  hiddenCharge := (240209257 / 200000000000 : ℝ)
  frame := (634537720157 / 1000000000000 : ℝ)
  moment := (10733256023 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12088 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367052441 / 244140625 : ℝ)
    root := (7540085651 / 1000000000000 : ℝ) }

noncomputable def scalar12088 : ScalarCertificate 12088 world12088 agent12088 where
  dimensionLo := 12088
  dimensionHi := 12088
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2304508099 / 1000000000000 : ℝ)
  frameLo := (634537720157 / 1000000000000 : ℝ)
  frameHi := (367052441 / 244140625 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12088]
  agentFrame_pos := by norm_num only [agent12088]
  worldRadius := (2304508099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12088]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1390684757 / 1000000000000 : ℝ)
  lowerTail := (878392557 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (65349621 / 8000000000 : ℝ)
  ledger := by
    have h : (240209257 / 200000000000 : ℚ) +
        (10733256023 / 1000000000000000000 : ℚ) / (2304508099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1390684757 / 1000000000000 : ℚ) + (878392557 / 500000000000 : ℚ) ≤
        (65349621 / 8000000000 : ℚ) := by norm_num only
    have hc : (((240209257 / 200000000000 : ℚ) +
        (10733256023 / 1000000000000000000 : ℚ) / (2304508099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1390684757 / 1000000000000 : ℚ) + (878392557 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((65349621 / 8000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12088]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12088 :
    2 * 160 < 12088 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999409 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12088 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12089 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12089. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12089 : WorldParameters where
  hiddenCharge := (3002487 / 2500000000 : ℝ)
  frame := (1982882513 / 3125000000 : ℝ)
  moment := (335341603 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12089 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (300679362901 / 200000000000 : ℝ)
    root := (3769700293 / 500000000000 : ℝ) }

noncomputable def scalar12089 : ScalarCertificate 12089 world12089 agent12089 where
  dimensionLo := 12089
  dimensionHi := 12089
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2304910499 / 1000000000000 : ℝ)
  frameLo := (1982882513 / 3125000000 : ℝ)
  frameHi := (300679362901 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12089]
  agentFrame_pos := by norm_num only [agent12089]
  worldRadius := (2304910499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12089]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (694714053 / 500000000000 : ℝ)
  lowerTail := (1755313391 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (204119489 / 25000000000 : ℝ)
  ledger := by
    have h : (3002487 / 2500000000 : ℚ) +
        (335341603 / 31250000000000000 : ℚ) / (2304910499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (694714053 / 500000000000 : ℚ) + (1755313391 / 1000000000000 : ℚ) ≤
        (204119489 / 25000000000 : ℚ) := by norm_num only
    have hc : (((3002487 / 2500000000 : ℚ) +
        (335341603 / 31250000000000000 : ℚ) / (2304910499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (694714053 / 500000000000 : ℚ) + (1755313391 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((204119489 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12089]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12089 :
    2 * 160 < 12089 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997297 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12089 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12090 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12090. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12090 : WorldParameters where
  hiddenCharge := (120094333 / 100000000000 : ℝ)
  frame := (634507090773 / 1000000000000 : ℝ)
  moment := (1341075909 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12090 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751673427411 / 500000000000 : ℝ)
    root := (7538715743 / 1000000000000 : ℝ) }

noncomputable def scalar12090 : ScalarCertificate 12090 world12090 agent12090 where
  dimensionLo := 12090
  dimensionHi := 12090
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2305312899 / 1000000000000 : ℝ)
  frameLo := (634507090773 / 1000000000000 : ℝ)
  frameHi := (751673427411 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12090]
  agentFrame_pos := by norm_num only [agent12090]
  worldRadius := (2305312899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12090]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (694086383 / 500000000000 : ℝ)
  lowerTail := (219230389 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8160860071 / 1000000000000 : ℝ)
  ledger := by
    have h : (120094333 / 100000000000 : ℚ) +
        (1341075909 / 125000000000000000 : ℚ) / (2305312899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (694086383 / 500000000000 : ℚ) + (219230389 / 125000000000 : ℚ) ≤
        (8160860071 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((120094333 / 100000000000 : ℚ) +
        (1341075909 / 125000000000000000 : ℚ) / (2305312899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (694086383 / 500000000000 : ℚ) + (219230389 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8160860071 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12090]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12090 :
    2 * 160 < 12090 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999767 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12090 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12091 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12091. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12091 : WorldParameters where
  hiddenCharge := (600445937 / 500000000000 : ℝ)
  frame := (317245889997 / 500000000000 : ℝ)
  moment := (10726283951 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12091 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503296931409 / 1000000000000 : ℝ)
    root := (7538031121 / 1000000000000 : ℝ) }

noncomputable def scalar12091 : ScalarCertificate 12091 world12091 agent12091 where
  dimensionLo := 12091
  dimensionHi := 12091
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2305715199 / 1000000000000 : ℝ)
  frameLo := (317245889997 / 500000000000 : ℝ)
  frameHi := (1503296931409 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12091]
  agentFrame_pos := by norm_num only [agent12091]
  worldRadius := (2305715199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12091]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1386918703 / 1000000000000 : ℝ)
  lowerTail := (876187123 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (815694427 / 100000000000 : ℝ)
  ledger := by
    have h : (600445937 / 500000000000 : ℚ) +
        (10726283951 / 1000000000000000000 : ℚ) / (2305715199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1386918703 / 1000000000000 : ℚ) + (876187123 / 500000000000 : ℚ) ≤
        (815694427 / 100000000000 : ℚ) := by norm_num only
    have hc : (((600445937 / 500000000000 : ℚ) +
        (10726283951 / 1000000000000000000 : ℚ) / (2305715199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1386918703 / 1000000000000 : ℚ) + (876187123 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((815694427 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12091]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12091 :
    2 * 160 < 12091 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994871 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12091 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12092 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12092. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12092 : WorldParameters where
  hiddenCharge := (75052527 / 62500000000 : ℝ)
  frame := (39654779489 / 62500000000 : ℝ)
  moment := (5361980667 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12092 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751623516051 / 500000000000 : ℝ)
    root := (3768673361 / 500000000000 : ℝ) }

noncomputable def scalar12092 : ScalarCertificate 12092 world12092 agent12092 where
  dimensionLo := 12092
  dimensionHi := 12092
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2306117599 / 1000000000000 : ℝ)
  frameLo := (39654779489 / 62500000000 : ℝ)
  frameHi := (751623516051 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12092]
  agentFrame_pos := by norm_num only [agent12092]
  worldRadius := (2306117599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12092]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1385666029 / 1000000000000 : ℝ)
  lowerTail := (350181383 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2038258009 / 250000000000 : ℝ)
  ledger := by
    have h : (75052527 / 62500000000 : ℚ) +
        (5361980667 / 500000000000000000 : ℚ) / (2306117599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1385666029 / 1000000000000 : ℚ) + (350181383 / 200000000000 : ℚ) ≤
        (2038258009 / 250000000000 : ℚ) := by norm_num only
    have hc : (((75052527 / 62500000000 : ℚ) +
        (5361980667 / 500000000000000000 : ℚ) / (2306117599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1385666029 / 1000000000000 : ℚ) + (350181383 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2038258009 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12092]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12092 :
    2 * 160 < 12092 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199998901 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12092 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12093 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12093. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12093 : WorldParameters where
  hiddenCharge := (300197251 / 250000000000 : ℝ)
  frame := (634461166261 / 1000000000000 : ℝ)
  moment := (10721639419 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12093 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503197156879 / 1000000000000 : ℝ)
    root := (471041409 / 62500000000 : ℝ) }

noncomputable def scalar12093 : ScalarCertificate 12093 world12093 agent12093 where
  dimensionLo := 12093
  dimensionHi := 12093
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2306519999 / 1000000000000 : ℝ)
  frameLo := (634461166261 / 1000000000000 : ℝ)
  frameHi := (1503197156879 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12093]
  agentFrame_pos := by norm_num only [agent12093]
  worldRadius := (2306519999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12093]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (69220733 / 50000000000 : ℝ)
  lowerTail := (874720511 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2037280841 / 250000000000 : ℝ)
  ledger := by
    have h : (300197251 / 250000000000 : ℚ) +
        (10721639419 / 1000000000000000000 : ℚ) / (2306519999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (69220733 / 50000000000 : ℚ) + (874720511 / 500000000000 : ℚ) ≤
        (2037280841 / 250000000000 : ℚ) := by norm_num only
    have hc : (((300197251 / 250000000000 : ℚ) +
        (10721639419 / 1000000000000000000 : ℚ) / (2306519999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (69220733 / 50000000000 : ℚ) + (874720511 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2037280841 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12093]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12093 :
    2 * 160 < 12093 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999729 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12093 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12094 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12094. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12094 : WorldParameters where
  hiddenCharge := (1200737591 / 1000000000000 : ℝ)
  frame := (79305732913 / 125000000000 : ℝ)
  moment := (5359659103 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12094 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751573658931 / 500000000000 : ℝ)
    root := (7535978587 / 1000000000000 : ℝ) }

noncomputable def scalar12094 : ScalarCertificate 12094 world12094 agent12094 where
  dimensionLo := 12094
  dimensionHi := 12094
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2306922399 / 1000000000000 : ℝ)
  frameLo := (79305732913 / 125000000000 : ℝ)
  frameHi := (751573658931 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12094]
  agentFrame_pos := by norm_num only [agent12094]
  worldRadius := (2306922399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12094]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (691582323 / 500000000000 : ℝ)
  lowerTail := (218497079 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (814521837 / 100000000000 : ℝ)
  ledger := by
    have h : (1200737591 / 1000000000000 : ℚ) +
        (5359659103 / 500000000000000000 : ℚ) / (2306922399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (691582323 / 500000000000 : ℚ) + (218497079 / 125000000000 : ℚ) ≤
        (814521837 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1200737591 / 1000000000000 : ℚ) +
        (5359659103 / 500000000000000000 : ℚ) / (2306922399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (691582323 / 500000000000 : ℚ) + (218497079 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((814521837 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12094]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12094 :
    2 * 160 < 12094 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998833 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12094 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12095 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12095. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12095 : WorldParameters where
  hiddenCharge := (75042887 / 62500000000 : ℝ)
  frame := (634430562953 / 1000000000000 : ℝ)
  moment := (2143399539 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12095 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1503097502889 / 1000000000000 : ℝ)
    root := (1883823713 / 250000000000 : ℝ) }

noncomputable def scalar12095 : ScalarCertificate 12095 world12095 agent12095 where
  dimensionLo := 12095
  dimensionHi := 12095
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2307324699 / 1000000000000 : ℝ)
  frameLo := (634430562953 / 1000000000000 : ℝ)
  frameHi := (1503097502889 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12095]
  agentFrame_pos := by norm_num only [agent12095]
  worldRadius := (2307324699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12095]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1381915853 / 1000000000000 : ℝ)
  lowerTail := (1746513583 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (814131693 / 100000000000 : ℝ)
  ledger := by
    have h : (75042887 / 62500000000 : ℚ) +
        (2143399539 / 200000000000000000 : ℚ) / (2307324699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1381915853 / 1000000000000 : ℚ) + (1746513583 / 1000000000000 : ℚ) ≤
        (814131693 / 100000000000 : ℚ) := by norm_num only
    have hc : (((75042887 / 62500000000 : ℚ) +
        (2143399539 / 200000000000000000 : ℚ) / (2307324699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1381915853 / 1000000000000 : ℚ) + (1746513583 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((814131693 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12095]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12095 :
    2 * 160 < 12095 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996473 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12095 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12096 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12096. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12096 : WorldParameters where
  hiddenCharge := (150079351 / 125000000000 : ℝ)
  frame := (79301908151 / 125000000000 : ℝ)
  moment := (5357338943 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12096 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46970237963 / 31250000000 : ℝ)
    root := (3767305669 / 500000000000 : ℝ) }

noncomputable def scalar12096 : ScalarCertificate 12096 world12096 agent12096 where
  dimensionLo := 12096
  dimensionHi := 12096
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2307727199 / 1000000000000 : ℝ)
  frameLo := (79301908151 / 125000000000 : ℝ)
  frameHi := (46970237963 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12096]
  agentFrame_pos := by norm_num only [agent12096]
  worldRadius := (2307727199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12096]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1380668117 / 1000000000000 : ℝ)
  lowerTail := (218131453 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8137418107 / 1000000000000 : ℝ)
  ledger := by
    have h : (150079351 / 125000000000 : ℚ) +
        (5357338943 / 500000000000000000 : ℚ) / (2307727199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1380668117 / 1000000000000 : ℚ) + (218131453 / 125000000000 : ℚ) ≤
        (8137418107 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((150079351 / 125000000000 : ℚ) +
        (5357338943 / 500000000000000000 : ℚ) / (2307727199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1380668117 / 1000000000000 : ℚ) + (218131453 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8137418107 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12096]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12096 :
    2 * 160 < 12096 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996079 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12096 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12097 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12097. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12097 : WorldParameters where
  hiddenCharge := (1200583437 / 1000000000000 : ℝ)
  frame := (634399970067 / 1000000000000 : ℝ)
  moment := (10712358779 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12097 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1502997507961 / 1000000000000 : ℝ)
    root := (1506785609 / 200000000000 : ℝ) }

noncomputable def scalar12097 : ScalarCertificate 12097 world12097 agent12097 where
  dimensionLo := 12097
  dimensionHi := 12097
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2308130099 / 1000000000000 : ℝ)
  frameLo := (634399970067 / 1000000000000 : ℝ)
  frameHi := (1502997507961 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12097]
  agentFrame_pos := by norm_num only [agent12097]
  worldRadius := (2308130099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12097]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (21553453 / 15625000000 : ℝ)
  lowerTail := (1743590147 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (508345031 / 62500000000 : ℝ)
  ledger := by
    have h : (1200583437 / 1000000000000 : ℚ) +
        (10712358779 / 1000000000000000000 : ℚ) / (2308130099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (21553453 / 15625000000 : ℚ) + (1743590147 / 1000000000000 : ℚ) ≤
        (508345031 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1200583437 / 1000000000000 : ℚ) +
        (10712358779 / 1000000000000000000 : ℚ) / (2308130099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (21553453 / 15625000000 : ℚ) + (1743590147 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((508345031 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12097]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12097 :
    2 * 160 < 12097 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995057 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12097 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12098 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12098. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12098 : WorldParameters where
  hiddenCharge := (600266041 / 500000000000 : ℝ)
  frame := (634384677529 / 1000000000000 : ℝ)
  moment := (10710040373 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12098 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (9393421407 / 6250000000 : ℝ)
    root := (7533244973 / 1000000000000 : ℝ) }

noncomputable def scalar12098 : ScalarCertificate 12098 world12098 agent12098 where
  dimensionLo := 12098
  dimensionHi := 12098
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2308532999 / 1000000000000 : ℝ)
  frameLo := (634384677529 / 1000000000000 : ℝ)
  frameHi := (9393421407 / 6250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12098]
  agentFrame_pos := by norm_num only [agent12098]
  worldRadius := (2308532999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12098]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (275635033 / 200000000000 : ℝ)
  lowerTail := (871065051 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (127025413 / 15625000000 : ℝ)
  ledger := by
    have h : (600266041 / 500000000000 : ℚ) +
        (10710040373 / 1000000000000000000 : ℚ) / (2308532999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (275635033 / 200000000000 : ℚ) + (871065051 / 500000000000 : ℚ) ≤
        (127025413 / 15625000000 : ℚ) := by norm_num only
    have hc : (((600266041 / 500000000000 : ℚ) +
        (10710040373 / 1000000000000000000 : ℚ) / (2308532999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (275635033 / 200000000000 : ℚ) + (871065051 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((127025413 / 15625000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12098]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12098 :
    2 * 160 < 12098 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999869 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12098 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12099 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12099. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12099 : WorldParameters where
  hiddenCharge := (60024037 / 50000000000 : ℝ)
  frame := (126873877519 / 200000000000 : ℝ)
  moment := (10707722667 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12099 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (150289737841 / 100000000000 : ℝ)
    root := (7532562121 / 1000000000000 : ℝ) }

noncomputable def scalar12099 : ScalarCertificate 12099 world12099 agent12099 where
  dimensionLo := 12099
  dimensionHi := 12099
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2308935899 / 1000000000000 : ℝ)
  frameLo := (126873877519 / 200000000000 : ℝ)
  frameHi := (150289737841 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12099]
  agentFrame_pos := by norm_num only [agent12099]
  worldRadius := (2308935899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12099]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (688465343 / 500000000000 : ℝ)
  lowerTail := (1740671553 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (812573603 / 100000000000 : ℝ)
  ledger := by
    have h : (60024037 / 50000000000 : ℚ) +
        (10707722667 / 1000000000000000000 : ℚ) / (2308935899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (688465343 / 500000000000 : ℚ) + (1740671553 / 1000000000000 : ℚ) ≤
        (812573603 / 100000000000 : ℚ) := by norm_num only
    have hc : (((60024037 / 50000000000 : ℚ) +
        (10707722667 / 1000000000000000000 : ℚ) / (2308935899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (688465343 / 500000000000 : ℚ) + (1740671553 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((812573603 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12099]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12099 :
    2 * 160 < 12099 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997501 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12099 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12100 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12100. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12100 : WorldParameters where
  hiddenCharge := (300107353 / 250000000000 : ℝ)
  frame := (634354100263 / 1000000000000 : ℝ)
  moment := (10705405663 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12100 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751423680871 / 500000000000 : ℝ)
    root := (7531879567 / 1000000000000 : ℝ) }

noncomputable def scalar12100 : ScalarCertificate 12100 world12100 agent12100 where
  dimensionLo := 12100
  dimensionHi := 12100
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2309338699 / 1000000000000 : ℝ)
  frameLo := (634354100263 / 1000000000000 : ℝ)
  frameHi := (751423680871 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12100]
  agentFrame_pos := by norm_num only [agent12100]
  worldRadius := (2309338699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12100]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1375687509 / 1000000000000 : ℝ)
  lowerTail := (1739214437 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8121849353 / 1000000000000 : ℝ)
  ledger := by
    have h : (300107353 / 250000000000 : ℚ) +
        (10705405663 / 1000000000000000000 : ℚ) / (2309338699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1375687509 / 1000000000000 : ℚ) + (1739214437 / 1000000000000 : ℚ) ≤
        (8121849353 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((300107353 / 250000000000 : ℚ) +
        (10705405663 / 1000000000000000000 : ℚ) / (2309338699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1375687509 / 1000000000000 : ℚ) + (1739214437 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8121849353 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12100]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12100 :
    2 * 160 < 12100 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997501 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12100 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12101 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12101. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12101 : WorldParameters where
  hiddenCharge := (1200378099 / 1000000000000 : ℝ)
  frame := (634338815533 / 1000000000000 : ℝ)
  moment := (10703089359 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12101 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (60111894761 / 40000000000 : ℝ)
    root := (7531197079 / 1000000000000 : ℝ) }

noncomputable def scalar12101 : ScalarCertificate 12101 world12101 agent12101 where
  dimensionLo := 12101
  dimensionHi := 12101
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2309741599 / 1000000000000 : ℝ)
  frameLo := (634338815533 / 1000000000000 : ℝ)
  frameHi := (60111894761 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12101]
  agentFrame_pos := by norm_num only [agent12101]
  worldRadius := (2309741599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12101]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (85902849 / 62500000000 : ℝ)
  lowerTail := (1737758711 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4058982979 / 500000000000 : ℝ)
  ledger := by
    have h : (1200378099 / 1000000000000 : ℚ) +
        (10703089359 / 1000000000000000000 : ℚ) / (2309741599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (85902849 / 62500000000 : ℚ) + (1737758711 / 1000000000000 : ℚ) ≤
        (4058982979 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1200378099 / 1000000000000 : ℚ) +
        (10703089359 / 1000000000000000000 : ℚ) / (2309741599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (85902849 / 62500000000 : ℚ) + (1737758711 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4058982979 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12101]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12101 :
    2 * 160 < 12101 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997857 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12101 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12102 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12102. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12102 : WorldParameters where
  hiddenCharge := (1200326801 / 1000000000000 : ℝ)
  frame := (158580883351 / 250000000000 : ℝ)
  moment := (2140154751 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12102 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (12021979299 / 8000000000 : ℝ)
    root := (7530514889 / 1000000000000 : ℝ) }

noncomputable def scalar12102 : ScalarCertificate 12102 world12102 agent12102 where
  dimensionLo := 12102
  dimensionHi := 12102
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2310144399 / 1000000000000 : ℝ)
  frameLo := (158580883351 / 250000000000 : ℝ)
  frameHi := (12021979299 / 8000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12102]
  agentFrame_pos := by norm_num only [agent12102]
  worldRadius := (2310144399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12102]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1373204983 / 1000000000000 : ℝ)
  lowerTail := (27129757 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8114086339 / 1000000000000 : ℝ)
  ledger := by
    have h : (1200326801 / 1000000000000 : ℚ) +
        (2140154751 / 200000000000000000 : ℚ) / (2310144399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1373204983 / 1000000000000 : ℚ) + (27129757 / 15625000000 : ℚ) ≤
        (8114086339 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1200326801 / 1000000000000 : ℚ) +
        (2140154751 / 200000000000000000 : ℚ) / (2310144399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1373204983 / 1000000000000 : ℚ) + (27129757 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((8114086339 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12102]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12102 :
    2 * 160 < 12102 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (549999711 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12102 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12103 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12103. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12103 : WorldParameters where
  hiddenCharge := (300068879 / 250000000000 : ℝ)
  frame := (5074466031 / 8000000000 : ℝ)
  moment := (213969177 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12103 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (300539495927 / 200000000000 : ℝ)
    root := (7529832919 / 1000000000000 : ℝ) }

noncomputable def scalar12103 : ScalarCertificate 12103 world12103 agent12103 where
  dimensionLo := 12103
  dimensionHi := 12103
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2310547399 / 1000000000000 : ℝ)
  frameLo := (5074466031 / 8000000000 : ℝ)
  frameHi := (300539495927 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12103]
  agentFrame_pos := by norm_num only [agent12103]
  worldRadius := (2310547399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12103]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (685982917 / 500000000000 : ℝ)
  lowerTail := (867425897 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1013776281 / 125000000000 : ℝ)
  ledger := by
    have h : (300068879 / 250000000000 : ℚ) +
        (213969177 / 20000000000000000 : ℚ) / (2310547399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (685982917 / 500000000000 : ℚ) + (867425897 / 500000000000 : ℚ) ≤
        (1013776281 / 125000000000 : ℚ) := by norm_num only
    have hc : (((300068879 / 250000000000 : ℚ) +
        (213969177 / 20000000000000000 : ℚ) / (2310547399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (685982917 / 500000000000 : ℚ) + (867425897 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1013776281 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12103]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12103 :
    2 * 160 < 12103 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (274999897 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12103 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12104 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12104. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12104 : WorldParameters where
  hiddenCharge := (600112123 / 500000000000 : ℝ)
  frame := (317146488473 / 500000000000 : ℝ)
  moment := (5348072323 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12104 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (375661894213 / 250000000000 : ℝ)
    root := (117642987 / 15625000000 : ℝ) }

noncomputable def scalar12104 : ScalarCertificate 12104 world12104 agent12104 where
  dimensionLo := 12104
  dimensionHi := 12104
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2310950199 / 1000000000000 : ℝ)
  frameLo := (317146488473 / 500000000000 : ℝ)
  frameHi := (375661894213 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12104]
  agentFrame_pos := by norm_num only [agent12104]
  worldRadius := (2310950199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12104]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (685363919 / 500000000000 : ℝ)
  lowerTail := (1733400409 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (405316887 / 50000000000 : ℝ)
  ledger := by
    have h : (600112123 / 500000000000 : ℚ) +
        (5348072323 / 500000000000000000 : ℚ) / (2310950199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (685363919 / 500000000000 : ℚ) + (1733400409 / 1000000000000 : ℚ) ≤
        (405316887 / 50000000000 : ℚ) := by norm_num only
    have hc : (((600112123 / 500000000000 : ℚ) +
        (5348072323 / 500000000000000000 : ℚ) / (2310950199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (685363919 / 500000000000 : ℚ) + (1733400409 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((405316887 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12104]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12104 :
    2 * 160 < 12104 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996899 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12104 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12105 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12105. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12105 : WorldParameters where
  hiddenCharge := (120017299 / 100000000000 : ℝ)
  frame := (126855540523 / 200000000000 : ℝ)
  moment := (10693831141 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12105 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751298852003 / 500000000000 : ℝ)
    root := (3764234819 / 500000000000 : ℝ) }

noncomputable def scalar12105 : ScalarCertificate 12105 world12105 agent12105 where
  dimensionLo := 12105
  dimensionHi := 12105
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2311353099 / 1000000000000 : ℝ)
  frameLo := (126855540523 / 200000000000 : ℝ)
  frameHi := (751298852003 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12105]
  agentFrame_pos := by norm_num only [agent12105]
  worldRadius := (2311353099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12105]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (273898247 / 200000000000 : ℝ)
  lowerTail := (173195057 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8102468809 / 1000000000000 : ℝ)
  ledger := by
    have h : (120017299 / 100000000000 : ℚ) +
        (10693831141 / 1000000000000000000 : ℚ) / (2311353099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (273898247 / 200000000000 : ℚ) + (173195057 / 100000000000 : ℚ) ≤
        (8102468809 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((120017299 / 100000000000 : ℚ) +
        (10693831141 / 1000000000000000000 : ℚ) / (2311353099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (273898247 / 200000000000 : ℚ) + (173195057 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8102468809 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12105]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12105 :
    2 * 160 < 12105 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999449 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12105 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12106 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12106. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12106 : WorldParameters where
  hiddenCharge := (300030437 / 250000000000 : ℝ)
  frame := (634262430883 / 1000000000000 : ℝ)
  moment := (5345759167 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12106 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (60101914443 / 40000000000 : ℝ)
    root := (7527788327 / 1000000000000 : ℝ) }

noncomputable def scalar12106 : ScalarCertificate 12106 world12106 agent12106 where
  dimensionLo := 12106
  dimensionHi := 12106
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2311755999 / 1000000000000 : ℝ)
  frameLo := (634262430883 / 1000000000000 : ℝ)
  frameHi := (60101914443 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12106]
  agentFrame_pos := by norm_num only [agent12106]
  worldRadius := (2311755999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12106]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (171031993 / 125000000000 : ℝ)
  lowerTail := (1730502183 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4049301727 / 500000000000 : ℝ)
  ledger := by
    have h : (300030437 / 250000000000 : ℚ) +
        (5345759167 / 500000000000000000 : ℚ) / (2311755999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (171031993 / 125000000000 : ℚ) + (1730502183 / 1000000000000 : ℚ) ≤
        (4049301727 / 500000000000 : ℚ) := by norm_num only
    have hc : (((300030437 / 250000000000 : ℚ) +
        (5345759167 / 500000000000000000 : ℚ) / (2311755999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (171031993 / 125000000000 : ℚ) + (1730502183 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4049301727 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12106]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12106 :
    2 * 160 < 12106 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996887 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12106 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12107 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12107. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12107 : WorldParameters where
  hiddenCharge := (1200070521 / 1000000000000 : ℝ)
  frame := (158561790437 / 250000000000 : ℝ)
  moment := (10689206227 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12107 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1502498048039 / 1000000000000 : ℝ)
    root := (1881776809 / 250000000000 : ℝ) }

noncomputable def scalar12107 : ScalarCertificate 12107 world12107 agent12107 where
  dimensionLo := 12107
  dimensionHi := 12107
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2312158899 / 1000000000000 : ℝ)
  frameLo := (158561790437 / 250000000000 : ℝ)
  frameHi := (1502498048039 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12107]
  agentFrame_pos := by norm_num only [agent12107]
  worldRadius := (2312158899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12107]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (683510981 / 500000000000 : ℝ)
  lowerTail := (432263811 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8094741669 / 1000000000000 : ℝ)
  ledger := by
    have h : (1200070521 / 1000000000000 : ℚ) +
        (10689206227 / 1000000000000000000 : ℚ) / (2312158899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (683510981 / 500000000000 : ℚ) + (432263811 / 250000000000 : ℚ) ≤
        (8094741669 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1200070521 / 1000000000000 : ℚ) +
        (10689206227 / 1000000000000000000 : ℚ) / (2312158899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (683510981 / 500000000000 : ℚ) + (432263811 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8094741669 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12107]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12107 :
    2 * 160 < 12107 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995797 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12107 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12108 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12108. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12108 : WorldParameters where
  hiddenCharge := (1200019307 / 1000000000000 : ℝ)
  frame := (63423189521 / 100000000000 : ℝ)
  moment := (5343447409 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12108 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1502448258809 / 1000000000000 : ℝ)
    root := (1881606591 / 250000000000 : ℝ) }

noncomputable def scalar12108 : ScalarCertificate 12108 world12108 agent12108 where
  dimensionLo := 12108
  dimensionHi := 12108
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2312561799 / 1000000000000 : ℝ)
  frameLo := (63423189521 / 100000000000 : ℝ)
  frameHi := (1502448258809 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12108]
  agentFrame_pos := by norm_num only [agent12108]
  worldRadius := (2312561799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12108]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (85361829 / 62500000000 : ℝ)
  lowerTail := (1727609721 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8090883391 / 1000000000000 : ℝ)
  ledger := by
    have h : (1200019307 / 1000000000000 : ℚ) +
        (5343447409 / 500000000000000000 : ℚ) / (2312561799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (85361829 / 62500000000 : ℚ) + (1727609721 / 1000000000000 : ℚ) ≤
        (8090883391 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1200019307 / 1000000000000 : ℚ) +
        (5343447409 / 500000000000000000 : ℚ) / (2312561799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (85361829 / 62500000000 : ℚ) + (1727609721 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8090883391 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12108]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12108 :
    2 * 160 < 12108 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999867 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12108 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12084 :
    (300313091931983938953 / 250000000000000000000000 : ℝ) ≤ world12084.hiddenCharge ∧
    (634599010252572723080213 / 1000000000000000000000000 : ℝ) ≤ world12084.frame ∧
    (671410123120481 / 62500000000000000000000 : ℝ) ≤ world12084.moment ∧
    (12029176290225863465109 / 8000000000000000000000 : ℝ) ≤ agent12084.frame ∧
    (3771414066873233432817 / 500000000000000000000000 : ℝ) ≤ agent12084.root ∧
    scalar12084.worldRadius ≤ (2302898699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (51843550355709498619 / 40000000000000000000000 : ℝ) ≤ agent12084.charge ∧
    (697862456065039910037 / 500000000000000000000000 : ℝ) ≤ scalar12084.upperTail ∧
    (440671748443616357947 / 250000000000000000000000 : ℝ) ≤ scalar12084.lowerTail ∧
    scalar12084.totalBudget ≤ (1023053913265638986341 / 125000000000000000000000 : ℝ) := by
  norm_num only [world12084, agent12084, scalar12084] <;> simp only [true_and]

theorem source_rounding12085 :
    (120120082543866767257 / 100000000000000000000000 : ℝ) ≤ world12085.hiddenCharge ∧
    (634583683810897401224627 / 1000000000000000000000000 : ℝ) ≤ world12085.frame ∧
    (2685058606623157 / 250000000000000000000000 : ℝ) ≤ world12085.moment ∧
    (375899232839153050818719 / 250000000000000000000000 : ℝ) ≤ agent12085.frame ∧
    (7542142179105754925107 / 1000000000000000000000000 : ℝ) ≤ agent12085.root ∧
    scalar12085.worldRadius ≤ (2303301099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1295745146068007993089 / 1000000000000000000000000 : ℝ) ≤ agent12085.charge ∧
    (697231451037000771201 / 500000000000000000000000 : ℝ) ≤ scalar12085.upperTail ∧
    (110075584189327495709 / 62500000000000000000000 : ℝ) ≤ scalar12085.lowerTail ∧
    scalar12085.totalBudget ≤ (16360987331269217459 / 2000000000000000000000 : ℝ) := by
  norm_num only [world12085, agent12085, scalar12085] <;> simp only [true_and]

theorem source_rounding12086 :
    (150143662189320258547 / 125000000000000000000000 : ℝ) ≤ world12086.hiddenCharge ∧
    (126913671996301175750843 / 200000000000000000000000 : ℝ) ≤ world12086.frame ∧
    (2684476896889981 / 250000000000000000000000 : ℝ) ≤ world12086.moment ∧
    (751773428369938696371581 / 500000000000000000000000 : ℝ) ≤ agent12086.frame ∧
    (942682055884069077429 / 125000000000000000000000 : ℝ) ≤ agent12086.root ∧
    scalar12086.worldRadius ≤ (2303703399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1295401963482418402141 / 1000000000000000000000000 : ℝ) ≤ agent12086.charge ∧
    (696601076511082613781 / 500000000000000000000000 : ℝ) ≤ scalar12086.upperTail ∧
    (1759733089514600593349 / 1000000000000000000000000 : ℝ) ≤ scalar12086.lowerTail ∧
    scalar12086.totalBudget ≤ (8176559673731840135321 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12086, agent12086, scalar12086] <;> simp only [true_and]

theorem source_rounding12087 :
    (600548891975190149053 / 500000000000000000000000 : ℝ) ≤ world12087.hiddenCharge ∧
    (317276519381844210537531 / 500000000000000000000000 : ℝ) ≤ world12087.frame ∧
    (10735581452855953 / 1000000000000000000000000 : ℝ) ≤ world12087.moment ∧
    (46984275577476544024493 / 31250000000000000000000 : ℝ) ≤ agent12087.frame ∧
    (3770385468749174484879 / 500000000000000000000000 : ℝ) ≤ agent12087.root ∧
    scalar12087.worldRadius ≤ (2304105699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (647529605245631741497 / 500000000000000000000000 : ℝ) ≤ agent12087.charge ∧
    (1391942770184512715639 / 1000000000000000000000000 : ℝ) ≤ scalar12087.upperTail ∧
    (87912917368550599553 / 50000000000000000000000 : ℝ) ≤ scalar12087.lowerTail ∧
    scalar12087.totalBudget ≤ (1021578673438481050499 / 125000000000000000000000 : ℝ) := by
  norm_num only [world12087, agent12087, scalar12087] <;> simp only [true_and]

theorem source_rounding12088 :
    (600523142370442389907 / 500000000000000000000000 : ℝ) ≤ world12088.hiddenCharge ∧
    (79317215019591958057751 / 125000000000000000000000 : ℝ) ≤ world12088.frame ∧
    (10733256022107161 / 1000000000000000000000000 : ℝ) ≤ world12088.moment ∧
    (751723399167675810692083 / 500000000000000000000000 : ℝ) ≤ agent12088.frame ∧
    (1885021412558696681471 / 250000000000000000000000 : ℝ) ≤ agent12088.root ∧
    scalar12088.worldRadius ≤ (2304508099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1294716886450951392873 / 1000000000000000000000000 : ℝ) ≤ agent12088.charge ∧
    (1390684756589827820211 / 1000000000000000000000000 : ℝ) ≤ scalar12088.upperTail ∧
    (1756785113000575416337 / 1000000000000000000000000 : ℝ) ≤ scalar12088.lowerTail ∧
    scalar12088.totalBudget ≤ (4084351312828157836531 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12088, agent12088, scalar12088] <;> simp only [true_and]

theorem source_rounding12089 :
    (1200994799880843132253 / 1000000000000000000000000 : ℝ) ≤ world12089.hiddenCharge ∧
    (634522404159938518031781 / 1000000000000000000000000 : ℝ) ≤ world12089.frame ∧
    (2682732823760059 / 250000000000000000000000 : ℝ) ≤ world12089.moment ∧
    (1503396814504770497688789 / 1000000000000000000000000 : ℝ) ≤ agent12089.frame ∧
    (753940058513366216257 / 100000000000000000000000 : ℝ) ≤ agent12089.root ∧
    scalar12089.worldRadius ≤ (2304910499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (32359374767975037823 / 25000000000000000000000 : ℝ) ≤ agent12089.charge ∧
    (694714052881479158509 / 500000000000000000000000 : ℝ) ≤ scalar12089.upperTail ∧
    (1755313390362925051681 / 1000000000000000000000000 : ℝ) ≤ scalar12089.lowerTail ∧
    scalar12089.totalBudget ≤ (8164779560983709696519 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12089, agent12089, scalar12089] <;> simp only [true_and]

theorem source_rounding12090 :
    (300235832341256008271 / 250000000000000000000000 : ℝ) ≤ world12090.hiddenCharge ∧
    (126901418154517613700353 / 200000000000000000000000 : ℝ) ≤ world12090.frame ∧
    (5364303635690973 / 500000000000000000000000 : ℝ) ≤ world12090.moment ∧
    (1503346854821684539772211 / 1000000000000000000000000 : ℝ) ≤ agent12090.frame ∧
    (7538715742046924876167 / 1000000000000000000000000 : ℝ) ≤ agent12090.root ∧
    scalar12090.worldRadius ≤ (2305312899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1294033522654042309747 / 1000000000000000000000000 : ℝ) ≤ agent12090.charge ∧
    (694086382571051220071 / 500000000000000000000000 : ℝ) ≤ scalar12090.upperTail ∧
    (1753843111044771078183 / 1000000000000000000000000 : ℝ) ≤ scalar12090.lowerTail ∧
    scalar12090.totalBudget ≤ (8160860071179881765457 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12090, agent12090, scalar12090] <;> simp only [true_and]

theorem source_rounding12091 :
    (9381967759282790787 / 7812500000000000000000 : ℝ) ≤ world12091.hiddenCharge ∧
    (634491779993975669377897 / 1000000000000000000000000 : ℝ) ≤ world12091.frame ∧
    (2145256790171827 / 200000000000000000000000 : ℝ) ≤ world12091.moment ∧
    (1503296931408667549659163 / 1000000000000000000000000 : ℝ) ≤ agent12091.frame ∧
    (7538031120826677581563 / 1000000000000000000000000 : ℝ) ≤ agent12091.root ∧
    scalar12091.worldRadius ≤ (2305715199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (646846240807904600721 / 500000000000000000000000 : ℝ) ≤ agent12091.charge ∧
    (277383740598051836489 / 200000000000000000000000 : ℝ) ≤ scalar12091.upperTail ∧
    (87618712292787731921 / 50000000000000000000000 : ℝ) ≤ scalar12091.lowerTail ∧
    scalar12091.totalBudget ≤ (1019618033874245412297 / 125000000000000000000000 : ℝ) := by
  norm_num only [world12091, agent12091, scalar12091] <;> simp only [true_and]

theorem source_rounding12092 :
    (300210107836284062347 / 250000000000000000000000 : ℝ) ≤ world12092.hiddenCharge ∧
    (39654779488962065604399 / 62500000000000000000000 : ℝ) ≤ world12092.frame ∧
    (2144792266639767 / 200000000000000000000000 : ℝ) ≤ world12092.moment ∧
    (375811758025269543891883 / 250000000000000000000000 : ℝ) ≤ agent12092.frame ∧
    (1884336680331293977357 / 250000000000000000000000 : ℝ) ≤ agent12092.root ∧
    scalar12092.worldRadius ≤ (2306117599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1293351866965142428043 / 1000000000000000000000000 : ℝ) ≤ agent12092.charge ∧
    (277133205758119473447 / 200000000000000000000000 : ℝ) ≤ scalar12092.upperTail ∧
    (350181382934371794919 / 200000000000000000000000 : ℝ) ≤ scalar12092.lowerTail ∧
    scalar12092.totalBudget ≤ (163060640726093060647 / 20000000000000000000000 : ℝ) := by
  norm_num only [world12092, agent12092, scalar12092] <;> simp only [true_and]

theorem source_rounding12093 :
    (300197250957654621043 / 250000000000000000000000 : ℝ) ≤ world12093.hiddenCharge ∧
    (79307645782516517192687 / 125000000000000000000000 : ℝ) ≤ world12093.frame ∧
    (2144327883625653 / 200000000000000000000000 : ℝ) ≤ world12093.moment ∧
    (1503197156878484779394471 / 1000000000000000000000000 : ℝ) ≤ agent12093.frame ∧
    (1507332508678965640757 / 200000000000000000000000 : ℝ) ≤ agent12093.root ∧
    scalar12093.worldRadius ≤ (2306519999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (646505839031992463231 / 500000000000000000000000 : ℝ) ≤ agent12093.charge ∧
    (1384414659941782865391 / 1000000000000000000000000 : ℝ) ≤ scalar12093.upperTail ∧
    (1749441021696115798463 / 1000000000000000000000000 : ℝ) ≤ scalar12093.lowerTail ∧
    scalar12093.totalBudget ≤ (8149123364523343433397 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12093, agent12093, scalar12093] <;> simp only [true_and]

theorem source_rounding12094 :
    (1200737590639419595481 / 1000000000000000000000000 : ℝ) ≤ world12094.hiddenCharge ∧
    (158611465825871266842763 / 250000000000000000000000 : ℝ) ≤ world12094.frame ∧
    (10719318205374613 / 1000000000000000000000000 : ℝ) ≤ world12094.moment ∧
    (375786829465462858951643 / 250000000000000000000000 : ℝ) ≤ agent12094.frame ∧
    (7535978586888195319879 / 1000000000000000000000000 : ℝ) ≤ agent12094.root ∧
    scalar12094.worldRadius ≤ (2306922399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (16158398928442252623 / 12500000000000000000000 : ℝ) ≤ agent12094.charge ∧
    (691582322771794327771 / 500000000000000000000000 : ℝ) ≤ scalar12094.upperTail ∧
    (1747976631662735571757 / 1000000000000000000000000 : ℝ) ≤ scalar12094.lowerTail ∧
    scalar12094.totalBudget ≤ (203630459253903006607 / 25000000000000000000000 : ℝ) := by
  norm_num only [world12094, agent12094, scalar12094] <;> simp only [true_and]

theorem source_rounding12095 :
    (24013723835326436297 / 20000000000000000000000 : ℝ) ≤ world12095.hiddenCharge ∧
    (634430562952744277980017 / 1000000000000000000000000 : ℝ) ≤ world12095.frame ∧
    (10716997694665363 / 1000000000000000000000000 : ℝ) ≤ world12095.moment ∧
    (375774375722075931383787 / 250000000000000000000000 : ℝ) ≤ agent12095.frame ∧
    (3767647425828995211179 / 500000000000000000000000 : ℝ) ≤ agent12095.root ∧
    scalar12095.worldRadius ≤ (2307324699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1292332574963470251349 / 1000000000000000000000000 : ℝ) ≤ agent12095.charge ∧
    (138191585254744527239 / 100000000000000000000000 : ℝ) ≤ scalar12095.upperTail ∧
    (1746513582614940680947 / 1000000000000000000000000 : ℝ) ≤ scalar12095.lowerTail ∧
    scalar12095.totalBudget ≤ (4070658465182070214307 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12095, agent12095, scalar12095] <;> simp only [true_and]

theorem source_rounding12096 :
    (1200634807206107054037 / 1000000000000000000000000 : ℝ) ≤ world12096.hiddenCharge ∧
    (634415265207202481440281 / 1000000000000000000000000 : ℝ) ≤ world12096.frame ∧
    (5357338942864011 / 500000000000000000000000 : ℝ) ≤ world12096.moment ∧
    (751523807407759547127233 / 500000000000000000000000 : ℝ) ≤ agent12096.frame ∧
    (7534611337557078783771 / 1000000000000000000000000 : ℝ) ≤ agent12096.root ∧
    scalar12096.worldRadius ≤ (2307727199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1291993659493493372393 / 1000000000000000000000000 : ℝ) ≤ agent12096.charge ∧
    (1380668116600505957877 / 1000000000000000000000000 : ℝ) ≤ scalar12096.upperTail ∧
    (1745051623829283537839 / 1000000000000000000000000 : ℝ) ≤ scalar12096.lowerTail ∧
    scalar12096.totalBudget ≤ (8137418107269063760959 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12096, agent12096, scalar12096] <;> simp only [true_and]

theorem source_rounding12097 :
    (37518232404798739271 / 31250000000000000000000 : ℝ) ≤ world12097.hiddenCharge ∧
    (634399970066152727572883 / 1000000000000000000000000 : ℝ) ≤ world12097.frame ∧
    (1071235877829023 / 100000000000000000000000 : ℝ) ≤ world12097.moment ∧
    (751498753980261294304553 / 500000000000000000000000 : ℝ) ≤ agent12097.frame ∧
    (7533928044438477583363 / 1000000000000000000000000 : ℝ) ≤ agent12097.root ∧
    scalar12097.worldRadius ≤ (2308130099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1291655167231782135233 / 1000000000000000000000000 : ℝ) ≤ agent12097.charge ∧
    (689710495510322613861 / 500000000000000000000000 : ℝ) ≤ scalar12097.upperTail ∧
    (435897536655122484903 / 250000000000000000000000 : ℝ) ≤ scalar12097.lowerTail ∧
    scalar12097.totalBudget ≤ (4066760248242857718319 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12097, agent12097, scalar12097] <;> simp only [true_and]

theorem source_rounding12098 :
    (1200532081003467769369 / 1000000000000000000000000 : ℝ) ≤ world12098.hiddenCharge ∧
    (39649042345555510188671 / 62500000000000000000000 : ℝ) ≤ world12098.frame ∧
    (2677510093019953 / 250000000000000000000000 : ℝ) ≤ world12098.moment ∧
    (751473712559598334350239 / 500000000000000000000000 : ℝ) ≤ agent12098.frame ∧
    (7533244972155355706189 / 1000000000000000000000000 : ℝ) ≤ agent12098.root ∧
    scalar12098.worldRadius ≤ (2308532999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1291317097545761240011 / 1000000000000000000000000 : ℝ) ≤ agent12098.charge ∧
    (689087582193090421543 / 500000000000000000000000 : ℝ) ≤ scalar12098.upperTail ∧
    (217766262652373112011 / 125000000000000000000000 : ℝ) ≤ scalar12098.lowerTail ∧
    scalar12098.totalBudget ≤ (1016203304058865125197 / 125000000000000000000000 : ℝ) := by
  norm_num only [world12098, agent12098, scalar12098] <;> simp only [true_and]

theorem source_rounding12099 :
    (1200480739350621965039 / 1000000000000000000000000 : ℝ) ≤ world12099.hiddenCharge ∧
    (634369387594702283255629 / 1000000000000000000000000 : ℝ) ≤ world12099.frame ∧
    (10707722666824727 / 1000000000000000000000000 : ℝ) ≤ world12099.moment ∧
    (1502897378409787452929587 / 1000000000000000000000000 : ℝ) ≤ agent12099.frame ∧
    (1883140530140258385631 / 250000000000000000000000 : ℝ) ≤ agent12099.root ∧
    scalar12099.worldRadius ≤ (2308935899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (645489724901972713079 / 500000000000000000000000 : ℝ) ≤ agent12099.charge ∧
    (688465342804204783211 / 500000000000000000000000 : ℝ) ≤ scalar12099.upperTail ∧
    (1740671552129552756881 / 1000000000000000000000000 : ℝ) ≤ scalar12099.lowerTail ∧
    scalar12099.totalBudget ≤ (8125736030320084807327 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12099, agent12099, scalar12099] <;> simp only [true_and]

theorem source_rounding12100 :
    (120042941198981387019 / 100000000000000000000000 : ℝ) ≤ world12100.hiddenCharge ∧
    (317177050131444420365791 / 500000000000000000000000 : ℝ) ≤ world12100.frame ∧
    (2676351415563253 / 250000000000000000000000 : ℝ) ≤ world12100.moment ∧
    (1502847361741333251712029 / 1000000000000000000000000 : ℝ) ≤ agent12100.frame ∧
    (7531879566632002619357 / 1000000000000000000000000 : ℝ) ≤ agent12100.root ∧
    scalar12100.worldRadius ≤ (2309338699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1290642223375937378191 / 1000000000000000000000000 : ℝ) ≤ agent12100.charge ∧
    (171960938572097767513 / 125000000000000000000000 : ℝ) ≤ scalar12100.upperTail ∧
    (869607218181656592677 / 500000000000000000000000 : ℝ) ≤ scalar12100.lowerTail ∧
    scalar12100.totalBudget ≤ (101523116918288300287 / 12500000000000000000000 : ℝ) := by
  norm_num only [world12100, agent12100, scalar12100] <;> simp only [true_and]

theorem source_rounding12101 :
    (600189049457918083391 / 500000000000000000000000 : ℝ) ≤ world12101.hiddenCharge ∧
    (634338815532741900907541 / 1000000000000000000000000 : ℝ) ≤ world12101.frame ∧
    (5351544679046389 / 500000000000000000000000 : ℝ) ≤ world12101.moment ∧
    (1502797369024030606012143 / 1000000000000000000000000 : ℝ) ≤ agent12101.frame ∧
    (7531197078852826241599 / 1000000000000000000000000 : ℝ) ≤ agent12101.root ∧
    scalar12101.worldRadius ≤ (2309741599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1290305417632425635873 / 1000000000000000000000000 : ℝ) ≤ agent12101.charge ∧
    (1374445583707065422363 / 1000000000000000000000000 : ℝ) ≤ scalar12101.upperTail ∧
    (347551742032501828021 / 200000000000000000000000 : ℝ) ≤ scalar12101.lowerTail ∧
    scalar12101.totalBudget ≤ (4058982979207882600979 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12101, agent12101, scalar12101] <;> simp only [true_and]

theorem source_rounding12102 :
    (240065360024697340769 / 200000000000000000000000 : ℝ) ≤ world12102.hiddenCharge ∧
    (63432353340355569497603 / 100000000000000000000000 : ℝ) ≤ world12102.frame ∧
    (535038687703619 / 50000000000000000000000 : ℝ) ≤ world12102.moment ∧
    (187843426546813334230629 / 125000000000000000000000 : ℝ) ≤ agent12102.frame ∧
    (1506102977689267522011 / 200000000000000000000000 : ℝ) ≤ agent12102.root ∧
    scalar12102.worldRadius ≤ (2310144399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1289969031945182508741 / 1000000000000000000000000 : ℝ) ≤ agent12102.charge ∧
    (1373204982670755674637 / 1000000000000000000000000 : ℝ) ≤ scalar12102.upperTail ∧
    (1736304447027759368307 / 1000000000000000000000000 : ℝ) ≤ scalar12102.lowerTail ∧
    scalar12102.totalBudget ≤ (1622817267920608059477 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12102, agent12102, scalar12102] <;> simp only [true_and]

theorem source_rounding12103 :
    (300068878901891437721 / 250000000000000000000000 : ℝ) ≤ world12103.hiddenCharge ∧
    (634308253874624813537613 / 1000000000000000000000000 : ℝ) ≤ world12103.frame ∧
    (2139691769984061 / 200000000000000000000000 : ℝ) ≤ world12103.moment ∧
    (751348739817292730450777 / 500000000000000000000000 : ℝ) ≤ agent12103.frame ∧
    (7529832918143441304431 / 1000000000000000000000000 : ℝ) ≤ agent12103.root ∧
    scalar12103.worldRadius ≤ (2310547399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1289633065687061994979 / 1000000000000000000000000 : ℝ) ≤ agent12103.charge ∧
    (68598291651754345327 / 50000000000000000000000 : ℝ) ≤ scalar12103.upperTail ∧
    (1734851793859983745439 / 1000000000000000000000000 : ℝ) ≤ scalar12103.lowerTail ∧
    scalar12103.totalBudget ≤ (8110210248405779436787 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12103, agent12103, scalar12103] <;> simp only [true_and]

theorem source_rounding12104 :
    (48008969814514985113 / 40000000000000000000000 : ℝ) ≤ world12104.hiddenCharge ∧
    (634292976945244018470351 / 1000000000000000000000000 : ℝ) ≤ world12104.frame ∧
    (2674036161341279 / 250000000000000000000000 : ℝ) ≤ world12104.moment ∧
    (1502647576851956255526849 / 1000000000000000000000000 : ℝ) ≤ agent12104.frame ∧
    (7529151167798212243099 / 1000000000000000000000000 : ℝ) ≤ agent12104.root ∧
    scalar12104.worldRadius ≤ (2310950199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (644648759115998852319 / 500000000000000000000000 : ℝ) ≤ agent12104.charge ∧
    (1370727837467156234233 / 1000000000000000000000000 : ℝ) ≤ scalar12104.upperTail ∧
    (13542190693593208143 / 7812500000000000000000 : ℝ) ≤ scalar12104.lowerTail ∧
    scalar12104.totalBudget ≤ (2026584435102088045369 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12104, agent12104, scalar12104] <;> simp only [true_and]

theorem source_rounding12105 :
    (1920276783014745131 / 1600000000000000000000 : ℝ) ≤ world12105.hiddenCharge ∧
    (7928471282683854674117 / 12500000000000000000000 : ℝ) ≤ world12105.frame ∧
    (10693831140135453 / 1000000000000000000000000 : ℝ) ≤ world12105.moment ∧
    (300519540801125450564589 / 200000000000000000000000 : ℝ) ≤ agent12105.frame ∧
    (941058704658109456573 / 125000000000000000000000 : ℝ) ≤ agent12105.root ∧
    scalar12105.worldRadius ≤ (2311353099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (257792477791000157437 / 200000000000000000000000 : ℝ) ≤ agent12105.charge ∧
    (1369491234934932517319 / 1000000000000000000000000 : ℝ) ≤ scalar12105.upperTail ∧
    (1731950569870376242643 / 1000000000000000000000000 : ℝ) ≤ scalar12105.lowerTail ∧
    scalar12105.totalBudget ≤ (8102468809962724662149 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12105, agent12105, scalar12105] <;> simp only [true_and]

theorem source_rounding12106 :
    (1200121747666395148917 / 1000000000000000000000000 : ℝ) ≤ world12106.hiddenCharge ∧
    (126852486176462642620443 / 200000000000000000000000 : ℝ) ≤ world12106.frame ∧
    (5345759166980071 / 500000000000000000000000 : ℝ) ≤ world12106.moment ∧
    (1502547861074632793752477 / 1000000000000000000000000 : ℝ) ≤ agent12106.frame ∧
    (7527788326397806869119 / 1000000000000000000000000 : ℝ) ≤ agent12106.root ∧
    scalar12106.worldRadius ≤ (2311755999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1288627677232157863381 / 1000000000000000000000000 : ℝ) ≤ agent12106.charge ∧
    (684127971810412529207 / 500000000000000000000000 : ℝ) ≤ scalar12106.upperTail ∧
    (865251091076420506369 / 500000000000000000000000 : ℝ) ≤ scalar12106.lowerTail ∧
    scalar12106.totalBudget ≤ (8098603454427409990411 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12106, agent12106, scalar12106] <;> simp only [true_and]

theorem source_rounding12107 :
    (1200070520204222898767 / 1000000000000000000000000 : ℝ) ≤ world12107.hiddenCharge ∧
    (634247161747354078333007 / 1000000000000000000000000 : ℝ) ≤ world12107.frame ∧
    (2672301556642049 / 250000000000000000000000 : ℝ) ≤ world12107.moment ∧
    (751249024019016665855971 / 500000000000000000000000 : ℝ) ≤ agent12107.frame ∧
    (940888404381441392563 / 125000000000000000000000 : ℝ) ≤ agent12107.root ∧
    scalar12107.worldRadius ≤ (2312158899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (644146691220314480729 / 500000000000000000000000 : ℝ) ≤ agent12107.charge ∧
    (341755490476641465209 / 250000000000000000000000 : ℝ) ≤ scalar12107.upperTail ∧
    (432263810979290601759 / 250000000000000000000000 : ℝ) ≤ scalar12107.lowerTail ∧
    scalar12107.totalBudget ≤ (8094741669167430986511 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12107, agent12107, scalar12107] <;> simp only [true_and]

theorem source_rounding12108 :
    (150002413374063572817 / 125000000000000000000000 : ℝ) ≤ world12108.hiddenCharge ∧
    (634231895209126910289043 / 1000000000000000000000000 : ℝ) ≤ world12108.frame ∧
    (213737896353773 / 20000000000000000000000 : ℝ) ≤ world12108.moment ∧
    (1502448258808182360940249 / 1000000000000000000000000 : ℝ) ≤ agent12108.frame ∧
    (7526426363080723428269 / 1000000000000000000000000 : ℝ) ≤ agent12108.root ∧
    scalar12108.worldRadius ≤ (2312561799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (643979751979322728807 / 500000000000000000000000 : ℝ) ≤ agent12108.charge ∧
    (682894631554304842783 / 500000000000000000000000 : ℝ) ≤ scalar12108.upperTail ∧
    (1727609720587711089203 / 1000000000000000000000000 : ℝ) ≤ scalar12108.lowerTail ∧
    scalar12108.totalBudget ≤ (404544169580939831889 / 50000000000000000000000 : ℝ) := by
  norm_num only [world12108, agent12108, scalar12108] <;> simp only [true_and]

noncomputable def paperAgent12084 : AgentParameters :=
  { agent12084 with charge := (1296088763 / 1000000000000 : ℝ) }

theorem agent_is_repriced12084 : agent12084 =
    BstLean.Part265.agentRepriced 12084 world12084 paperAgent12084 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12084, agent12084]

noncomputable def paperAgent12085 : AgentParameters :=
  { agent12085 with charge := (1295745149 / 1000000000000 : ℝ) }

theorem agent_is_repriced12085 : agent12085 =
    BstLean.Part265.agentRepriced 12085 world12085 paperAgent12085 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12085, agent12085]

noncomputable def paperAgent12086 : AgentParameters :=
  { agent12086 with charge := (1295401967 / 1000000000000 : ℝ) }

theorem agent_is_repriced12086 : agent12086 =
    BstLean.Part265.agentRepriced 12086 world12086 paperAgent12086 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12086, agent12086]

noncomputable def paperAgent12087 : AgentParameters :=
  { agent12087 with charge := (647529607 / 500000000000 : ℝ) }

theorem agent_is_repriced12087 : agent12087 =
    BstLean.Part265.agentRepriced 12087 world12087 paperAgent12087 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12087, agent12087]

noncomputable def paperAgent12088 : AgentParameters :=
  { agent12088 with charge := (129471689 / 100000000000 : ℝ) }

theorem agent_is_repriced12088 : agent12088 =
    BstLean.Part265.agentRepriced 12088 world12088 paperAgent12088 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12088, agent12088]

noncomputable def paperAgent12089 : AgentParameters :=
  { agent12089 with charge := (647187497 / 500000000000 : ℝ) }

theorem agent_is_repriced12089 : agent12089 =
    BstLean.Part265.agentRepriced 12089 world12089 paperAgent12089 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12089, agent12089]

noncomputable def paperAgent12090 : AgentParameters :=
  { agent12090 with charge := (647016763 / 500000000000 : ℝ) }

theorem agent_is_repriced12090 : agent12090 =
    BstLean.Part265.agentRepriced 12090 world12090 paperAgent12090 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12090, agent12090]

noncomputable def paperAgent12091 : AgentParameters :=
  { agent12091 with charge := (323423121 / 250000000000 : ℝ) }

theorem agent_is_repriced12091 : agent12091 =
    BstLean.Part265.agentRepriced 12091 world12091 paperAgent12091 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12091, agent12091]

noncomputable def paperAgent12092 : AgentParameters :=
  { agent12092 with charge := (129335187 / 100000000000 : ℝ) }

theorem agent_is_repriced12092 : agent12092 =
    BstLean.Part265.agentRepriced 12092 world12092 paperAgent12092 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12092, agent12092]

noncomputable def paperAgent12093 : AgentParameters :=
  { agent12093 with charge := (646505841 / 500000000000 : ℝ) }

theorem agent_is_repriced12093 : agent12093 =
    BstLean.Part265.agentRepriced 12093 world12093 paperAgent12093 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12093, agent12093]

noncomputable def paperAgent12094 : AgentParameters :=
  { agent12094 with charge := (646335959 / 500000000000 : ℝ) }

theorem agent_is_repriced12094 : agent12094 =
    BstLean.Part265.agentRepriced 12094 world12094 paperAgent12094 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12094, agent12094]

noncomputable def paperAgent12095 : AgentParameters :=
  { agent12095 with charge := (1292332579 / 1000000000000 : ℝ) }

theorem agent_is_repriced12095 : agent12095 =
    BstLean.Part265.agentRepriced 12095 world12095 paperAgent12095 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12095, agent12095]

noncomputable def paperAgent12096 : AgentParameters :=
  { agent12096 with charge := (1291993663 / 1000000000000 : ℝ) }

theorem agent_is_repriced12096 : agent12096 =
    BstLean.Part265.agentRepriced 12096 world12096 paperAgent12096 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12096, agent12096]

noncomputable def paperAgent12097 : AgentParameters :=
  { agent12097 with charge := (129165517 / 100000000000 : ℝ) }

theorem agent_is_repriced12097 : agent12097 =
    BstLean.Part265.agentRepriced 12097 world12097 paperAgent12097 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12097, agent12097]

noncomputable def paperAgent12098 : AgentParameters :=
  { agent12098 with charge := (1291317101 / 1000000000000 : ℝ) }

theorem agent_is_repriced12098 : agent12098 =
    BstLean.Part265.agentRepriced 12098 world12098 paperAgent12098 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12098, agent12098]

noncomputable def paperAgent12099 : AgentParameters :=
  { agent12099 with charge := (1290979453 / 1000000000000 : ℝ) }

theorem agent_is_repriced12099 : agent12099 =
    BstLean.Part265.agentRepriced 12099 world12099 paperAgent12099 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12099, agent12099]

noncomputable def paperAgent12100 : AgentParameters :=
  { agent12100 with charge := (645321113 / 500000000000 : ℝ) }

theorem agent_is_repriced12100 : agent12100 =
    BstLean.Part265.agentRepriced 12100 world12100 paperAgent12100 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12100, agent12100]

noncomputable def paperAgent12101 : AgentParameters :=
  { agent12101 with charge := (1290305421 / 1000000000000 : ℝ) }

theorem agent_is_repriced12101 : agent12101 =
    BstLean.Part265.agentRepriced 12101 world12101 paperAgent12101 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12101, agent12101]

noncomputable def paperAgent12102 : AgentParameters :=
  { agent12102 with charge := (257993807 / 200000000000 : ℝ) }

theorem agent_is_repriced12102 : agent12102 =
    BstLean.Part265.agentRepriced 12102 world12102 paperAgent12102 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12102, agent12102]

noncomputable def paperAgent12103 : AgentParameters :=
  { agent12103 with charge := (1289633069 / 1000000000000 : ℝ) }

theorem agent_is_repriced12103 : agent12103 =
    BstLean.Part265.agentRepriced 12103 world12103 paperAgent12103 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12103, agent12103]

noncomputable def paperAgent12104 : AgentParameters :=
  { agent12104 with charge := (1289297521 / 1000000000000 : ℝ) }

theorem agent_is_repriced12104 : agent12104 =
    BstLean.Part265.agentRepriced 12104 world12104 paperAgent12104 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12104, agent12104]

noncomputable def paperAgent12105 : AgentParameters :=
  { agent12105 with charge := (161120299 / 125000000000 : ℝ) }

theorem agent_is_repriced12105 : agent12105 =
    BstLean.Part265.agentRepriced 12105 world12105 paperAgent12105 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12105, agent12105]

noncomputable def paperAgent12106 : AgentParameters :=
  { agent12106 with charge := (8053923 / 6250000000 : ℝ) }

theorem agent_is_repriced12106 : agent12106 =
    BstLean.Part265.agentRepriced 12106 world12106 paperAgent12106 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12106, agent12106]

noncomputable def paperAgent12107 : AgentParameters :=
  { agent12107 with charge := (257658677 / 200000000000 : ℝ) }

theorem agent_is_repriced12107 : agent12107 =
    BstLean.Part265.agentRepriced 12107 world12107 paperAgent12107 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12107, agent12107]

noncomputable def paperAgent12108 : AgentParameters :=
  { agent12108 with charge := (1287959507 / 1000000000000 : ℝ) }

theorem agent_is_repriced12108 : agent12108 =
    BstLean.Part265.agentRepriced 12108 world12108 paperAgent12108 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12108, agent12108]

end BstLean.Part281
