import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12109 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12109. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12109 : WorldParameters where
  hiddenCharge := (1199968109 / 1000000000000 : ℝ)
  frame := (634216631267 / 1000000000000 : ℝ)
  moment := (2671146027 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12109 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751199252749 / 500000000000 : ℝ)
    root := (7525745711 / 1000000000000 : ℝ) }

noncomputable def scalar12109 : ScalarCertificate 12109 world12109 agent12109 where
  dimensionLo := 12109
  dimensionHi := 12109
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2312964699 / 1000000000000 : ℝ)
  frameLo := (634216631267 / 1000000000000 : ℝ)
  frameHi := (751199252749 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12109]
  agentFrame_pos := by norm_num only [agent12109]
  worldRadius := (2312964699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12109]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (170569737 / 125000000000 : ℝ)
  lowerTail := (1726165677 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1617405747 / 200000000000 : ℝ)
  ledger := by
    have h : (1199968109 / 1000000000000 : ℚ) +
        (2671146027 / 250000000000000000 : ℚ) / (2312964699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (170569737 / 125000000000 : ℚ) + (1726165677 / 1000000000000 : ℚ) ≤
        (1617405747 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1199968109 / 1000000000000 : ℚ) +
        (2671146027 / 250000000000000000 : ℚ) / (2312964699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (170569737 / 125000000000 : ℚ) + (1726165677 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1617405747 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12109]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12109 :
    2 * 160 < 12109 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997221 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12109 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12110 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12110. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12110 : WorldParameters where
  hiddenCharge := (299979231 / 250000000000 : ℝ)
  frame := (634201369921 / 1000000000000 : ℝ)
  moment := (2136454819 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12110 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751174387977 / 500000000000 : ℝ)
    root := (7525065277 / 1000000000000 : ℝ) }

noncomputable def scalar12110 : ScalarCertificate 12110 world12110 agent12110 where
  dimensionLo := 12110
  dimensionHi := 12110
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2313367599 / 1000000000000 : ℝ)
  frameLo := (634201369921 / 1000000000000 : ℝ)
  frameHi := (751174387977 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12110]
  agentFrame_pos := by norm_num only [agent12110]
  worldRadius := (2313367599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12110]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1363327809 / 1000000000000 : ℝ)
  lowerTail := (431180761 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8083177579 / 1000000000000 : ℝ)
  ledger := by
    have h : (299979231 / 250000000000 : ℚ) +
        (2136454819 / 200000000000000000 : ℚ) / (2313367599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1363327809 / 1000000000000 : ℚ) + (431180761 / 250000000000 : ℚ) ≤
        (8083177579 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((299979231 / 250000000000 : ℚ) +
        (2136454819 / 200000000000000000 : ℚ) / (2313367599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1363327809 / 1000000000000 : ℚ) + (431180761 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8083177579 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12110]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12110 :
    2 * 160 < 12110 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (34374999 / 3125000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12110 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12111 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12111. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12111 : WorldParameters where
  hiddenCharge := (1199865753 / 1000000000000 : ℝ)
  frame := (9909157987 / 15625000000 : ℝ)
  moment := (533998239 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12111 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751149541143 / 500000000000 : ℝ)
    root := (3762192531 / 500000000000 : ℝ) }

noncomputable def scalar12111 : ScalarCertificate 12111 world12111 agent12111 where
  dimensionLo := 12111
  dimensionHi := 12111
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2313770399 / 1000000000000 : ℝ)
  frameLo := (9909157987 / 15625000000 : ℝ)
  frameHi := (751149541143 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12111]
  agentFrame_pos := by norm_num only [agent12111]
  worldRadius := (2313770399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12111]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (136209897 / 100000000000 : ℝ)
  lowerTail := (861640897 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4039665017 / 500000000000 : ℝ)
  ledger := by
    have h : (1199865753 / 1000000000000 : ℚ) +
        (533998239 / 50000000000000000 : ℚ) / (2313770399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (136209897 / 100000000000 : ℚ) + (861640897 / 500000000000 : ℚ) ≤
        (4039665017 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1199865753 / 1000000000000 : ℚ) +
        (533998239 / 50000000000000000 : ℚ) / (2313770399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (136209897 / 100000000000 : ℚ) + (861640897 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4039665017 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12111]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12111 :
    2 * 160 < 12111 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995359 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12111 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12112 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12112. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12112 : WorldParameters where
  hiddenCharge := (1199814597 / 1000000000000 : ℝ)
  frame := (63417085501 / 100000000000 : ℝ)
  moment := (5338828081 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12112 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187781176543 / 125000000000 : ℝ)
    root := (7523705067 / 1000000000000 : ℝ) }

noncomputable def scalar12112 : ScalarCertificate 12112 world12112 agent12112 where
  dimensionLo := 12112
  dimensionHi := 12112
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2314173299 / 1000000000000 : ℝ)
  frameLo := (63417085501 / 100000000000 : ℝ)
  frameHi := (187781176543 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12112]
  agentFrame_pos := by norm_num only [agent12112]
  worldRadius := (2314173299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12112]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1360871487 / 1000000000000 : ℝ)
  lowerTail := (344368409 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4037742991 / 500000000000 : ℝ)
  ledger := by
    have h : (1199814597 / 1000000000000 : ℚ) +
        (5338828081 / 500000000000000000 : ℚ) / (2314173299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1360871487 / 1000000000000 : ℚ) + (344368409 / 200000000000 : ℚ) ≤
        (4037742991 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1199814597 / 1000000000000 : ℚ) +
        (5338828081 / 500000000000000000 : ℚ) / (2314173299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1360871487 / 1000000000000 : ℚ) + (344368409 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4037742991 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12112]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12112 :
    2 * 160 < 12112 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996087 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12112 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12113 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12113. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12113 : WorldParameters where
  hiddenCharge := (239952691 / 200000000000 : ℝ)
  frame := (126831120289 / 200000000000 : ℝ)
  moment := (5337674121 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12113 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1502199772171 / 1000000000000 : ℝ)
    root := (7523025289 / 1000000000000 : ℝ) }

noncomputable def scalar12113 : ScalarCertificate 12113 world12113 agent12113 where
  dimensionLo := 12113
  dimensionHi := 12113
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2314576099 / 1000000000000 : ℝ)
  frameLo := (126831120289 / 200000000000 : ℝ)
  frameHi := (1502199772171 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12113]
  agentFrame_pos := by norm_num only [agent12113]
  worldRadius := (2314576099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12113]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (169955653 / 125000000000 : ℝ)
  lowerTail := (860201821 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8071645477 / 1000000000000 : ℝ)
  ledger := by
    have h : (239952691 / 200000000000 : ℚ) +
        (5337674121 / 500000000000000000 : ℚ) / (2314576099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (169955653 / 125000000000 : ℚ) + (860201821 / 500000000000 : ℚ) ≤
        (8071645477 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((239952691 / 200000000000 : ℚ) +
        (5337674121 / 500000000000000000 : ℚ) / (2314576099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (169955653 / 125000000000 : ℚ) + (860201821 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8071645477 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12113]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12113 :
    2 * 160 < 12113 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999181 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12113 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12114 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12114. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12114 : WorldParameters where
  hiddenCharge := (1199712327 / 1000000000000 : ℝ)
  frame := (79267543809 / 125000000000 : ℝ)
  moment := (10673041019 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12114 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1502150161747 / 1000000000000 : ℝ)
    root := (7522345731 / 1000000000000 : ℝ) }

noncomputable def scalar12114 : ScalarCertificate 12114 world12114 agent12114 where
  dimensionLo := 12114
  dimensionHi := 12114
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2314978999 / 1000000000000 : ℝ)
  frameLo := (79267543809 / 125000000000 : ℝ)
  frameHi := (1502150161747 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12114]
  agentFrame_pos := by norm_num only [agent12114]
  worldRadius := (2314978999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12114]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (67921017 / 50000000000 : ℝ)
  lowerTail := (171896677 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4033904257 / 500000000000 : ℝ)
  ledger := by
    have h : (1199712327 / 1000000000000 : ℚ) +
        (10673041019 / 1000000000000000000 : ℚ) / (2314978999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67921017 / 50000000000 : ℚ) + (171896677 / 100000000000 : ℚ) ≤
        (4033904257 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1199712327 / 1000000000000 : ℚ) +
        (10673041019 / 1000000000000000000 : ℚ) / (2314978999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67921017 / 50000000000 : ℚ) + (171896677 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4033904257 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12114]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12114 :
    2 * 160 < 12114 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (343749837 / 31250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12114 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12115 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12115. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12115 : WorldParameters where
  hiddenCharge := (599830607 / 500000000000 : ℝ)
  frame := (634125102091 / 1000000000000 : ℝ)
  moment := (2667683623 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12115 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751050287493 / 500000000000 : ℝ)
    root := (752166639 / 100000000000 : ℝ) }

noncomputable def scalar12115 : ScalarCertificate 12115 world12115 agent12115 where
  dimensionLo := 12115
  dimensionHi := 12115
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2315381899 / 1000000000000 : ℝ)
  frameLo := (634125102091 / 1000000000000 : ℝ)
  frameHi := (751050287493 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12115]
  agentFrame_pos := by norm_num only [agent12115]
  worldRadius := (2315381899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12115]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1357196727 / 1000000000000 : ℝ)
  lowerTail := (858765651 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4031987517 / 500000000000 : ℝ)
  ledger := by
    have h : (599830607 / 500000000000 : ℚ) +
        (2667683623 / 250000000000000000 : ℚ) / (2315381899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1357196727 / 1000000000000 : ℚ) + (858765651 / 500000000000 : ℚ) ≤
        (4031987517 / 500000000000 : ℚ) := by norm_num only
    have hc : (((599830607 / 500000000000 : ℚ) +
        (2667683623 / 250000000000000000 : ℚ) / (2315381899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1357196727 / 1000000000000 : ℚ) + (858765651 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4031987517 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12115]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12115 :
    2 * 160 < 12115 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998633 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12115 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12116 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12116. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12116 : WorldParameters where
  hiddenCharge := (599805057 / 500000000000 : ℝ)
  frame := (317054928151 / 500000000000 : ℝ)
  moment := (10668428661 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12116 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1502051023999 / 1000000000000 : ℝ)
    root := (1880246817 / 250000000000 : ℝ) }

noncomputable def scalar12116 : ScalarCertificate 12116 world12116 agent12116 where
  dimensionLo := 12116
  dimensionHi := 12116
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2315784799 / 1000000000000 : ℝ)
  frameLo := (317054928151 / 500000000000 : ℝ)
  frameHi := (1502051023999 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12116]
  agentFrame_pos := by norm_num only [agent12116]
  worldRadius := (2315784799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12116]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (271194887 / 200000000000 : ℝ)
  lowerTail := (17160973 / 10000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1007518143 / 125000000000 : ℝ)
  ledger := by
    have h : (599805057 / 500000000000 : ℚ) +
        (10668428661 / 1000000000000000000 : ℚ) / (2315784799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (271194887 / 200000000000 : ℚ) + (17160973 / 10000000000 : ℚ) ≤
        (1007518143 / 125000000000 : ℚ) := by norm_num only
    have hc : (((599805057 / 500000000000 : ℚ) +
        (10668428661 / 1000000000000000000 : ℚ) / (2315784799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (271194887 / 200000000000 : ℚ) + (17160973 / 10000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1007518143 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12116]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12116 :
    2 * 160 < 12116 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998887 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12116 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12117 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12117. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12117 : WorldParameters where
  hiddenCharge := (1199559029 / 1000000000000 : ℝ)
  frame := (317047306551 / 500000000000 : ℝ)
  moment := (10666123527 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12117 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (751000748317 / 500000000000 : ℝ)
    root := (1880077091 / 250000000000 : ℝ) }

noncomputable def scalar12117 : ScalarCertificate 12117 world12117 agent12117 where
  dimensionLo := 12117
  dimensionHi := 12117
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2316187699 / 1000000000000 : ℝ)
  frameLo := (317047306551 / 500000000000 : ℝ)
  frameHi := (751000748317 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12117]
  agentFrame_pos := by norm_num only [agent12117]
  worldRadius := (2316187699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12117]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1354753411 / 1000000000000 : ℝ)
  lowerTail := (857332349 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1007039841 / 125000000000 : ℝ)
  ledger := by
    have h : (1199559029 / 1000000000000 : ℚ) +
        (10666123527 / 1000000000000000000 : ℚ) / (2316187699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1354753411 / 1000000000000 : ℚ) + (857332349 / 500000000000 : ℚ) ≤
        (1007039841 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1199559029 / 1000000000000 : ℚ) +
        (10666123527 / 1000000000000000000 : ℚ) / (2316187699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1354753411 / 1000000000000 : ℚ) + (857332349 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1007039841 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12117]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12117 :
    2 * 160 < 12117 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (171874959 / 15625000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12117 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12118 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12118. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12118 : WorldParameters where
  hiddenCharge := (599753979 / 500000000000 : ℝ)
  frame := (634079372493 / 1000000000000 : ℝ)
  moment := (666488693 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12118 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187743999867 / 125000000000 : ℝ)
    root := (7519629601 / 1000000000000 : ℝ) }

noncomputable def scalar12118 : ScalarCertificate 12118 world12118 agent12118 where
  dimensionLo := 12118
  dimensionHi := 12118
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2316590599 / 1000000000000 : ℝ)
  frameLo := (634079372493 / 1000000000000 : ℝ)
  frameHi := (187743999867 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12118]
  agentFrame_pos := by norm_num only [agent12118]
  worldRadius := (2316590599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12118]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (67676681 / 50000000000 : ℝ)
  lowerTail := (1713233463 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4026247857 / 500000000000 : ℝ)
  ledger := by
    have h : (599753979 / 500000000000 : ℚ) +
        (666488693 / 62500000000000000 : ℚ) / (2316590599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67676681 / 50000000000 : ℚ) + (1713233463 / 1000000000000 : ℚ) ≤
        (4026247857 / 500000000000 : ℚ) := by norm_num only
    have hc : (((599753979 / 500000000000 : ℚ) +
        (666488693 / 62500000000000000 : ℚ) / (2316590599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67676681 / 50000000000 : ℚ) + (1713233463 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4026247857 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12118]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12118 :
    2 * 160 < 12118 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999769 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12118 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12119 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12119. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12119 : WorldParameters where
  hiddenCharge := (1199456901 / 1000000000000 : ℝ)
  frame := (79258016809 / 125000000000 : ℝ)
  moment := (2132303069 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12119 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (300380506177 / 200000000000 : ℝ)
    root := (1879737783 / 250000000000 : ℝ) }

noncomputable def scalar12119 : ScalarCertificate 12119 world12119 agent12119 where
  dimensionLo := 12119
  dimensionHi := 12119
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2316993399 / 1000000000000 : ℝ)
  frameLo := (79258016809 / 125000000000 : ℝ)
  frameHi := (300380506177 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12119]
  agentFrame_pos := by norm_num only [agent12119]
  worldRadius := (2316993399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12119]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1352315099 / 1000000000000 : ℝ)
  lowerTail := (1711803629 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8048676347 / 1000000000000 : ℝ)
  ledger := by
    have h : (1199456901 / 1000000000000 : ℚ) +
        (2132303069 / 200000000000000000 : ℚ) / (2316993399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1352315099 / 1000000000000 : ℚ) + (1711803629 / 1000000000000 : ℚ) ≤
        (8048676347 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1199456901 / 1000000000000 : ℚ) +
        (2132303069 / 200000000000000000 : ℚ) / (2316993399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1352315099 / 1000000000000 : ℚ) + (1711803629 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8048676347 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12119]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12119 :
    2 * 160 < 12119 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999461 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12119 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12120 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12120. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12120 : WorldParameters where
  hiddenCharge := (1199405859 / 1000000000000 : ℝ)
  frame := (3962805619 / 6250000000 : ℝ)
  moment := (10659212297 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12120 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501853092459 / 1000000000000 : ℝ)
    root := (3759136441 / 500000000000 : ℝ) }

noncomputable def scalar12120 : ScalarCertificate 12120 world12120 agent12120 where
  dimensionLo := 12120
  dimensionHi := 12120
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2317396399 / 1000000000000 : ℝ)
  frameLo := (3962805619 / 6250000000 : ℝ)
  frameHi := (1501853092459 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12120]
  agentFrame_pos := by norm_num only [agent12120]
  worldRadius := (2317396399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12120]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (675549013 / 500000000000 : ℝ)
  lowerTail := (1710375407 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (16089721 / 2000000000 : ℝ)
  ledger := by
    have h : (1199405859 / 1000000000000 : ℚ) +
        (10659212297 / 1000000000000000000 : ℚ) / (2317396399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (675549013 / 500000000000 : ℚ) + (1710375407 / 1000000000000 : ℚ) ≤
        (16089721 / 2000000000 : ℚ) := by norm_num only
    have hc : (((1199405859 / 1000000000000 : ℚ) +
        (10659212297 / 1000000000000000000 : ℚ) / (2317396399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (675549013 / 500000000000 : ℚ) + (1710375407 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((16089721 / 2000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12120]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12120 :
    2 * 160 < 12120 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (439999857 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12120 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12121 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12121. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12121 : WorldParameters where
  hiddenCharge := (119935483 / 100000000000 : ℝ)
  frame := (126806733239 / 200000000000 : ℝ)
  moment := (1332113743 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12121 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (60072147103 / 40000000000 : ℝ)
    root := (234924839 / 31250000000 : ℝ) }

noncomputable def scalar12121 : ScalarCertificate 12121 world12121 agent12121 where
  dimensionLo := 12121
  dimensionHi := 12121
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2317799199 / 1000000000000 : ℝ)
  frameLo := (126806733239 / 200000000000 : ℝ)
  frameHi := (60072147103 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12121]
  agentFrame_pos := by norm_num only [agent12121]
  worldRadius := (2317799199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12121]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1349882057 / 1000000000000 : ℝ)
  lowerTail := (854474197 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (804104811 / 100000000000 : ℝ)
  ledger := by
    have h : (119935483 / 100000000000 : ℚ) +
        (1332113743 / 125000000000000000 : ℚ) / (2317799199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1349882057 / 1000000000000 : ℚ) + (854474197 / 500000000000 : ℚ) ≤
        (804104811 / 100000000000 : ℚ) := by norm_num only
    have hc : (((119935483 / 100000000000 : ℚ) +
        (1332113743 / 125000000000000000 : ℚ) / (2317799199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1349882057 / 1000000000000 : ℚ) + (854474197 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((804104811 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12121]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12121 :
    2 * 160 < 12121 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999907 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12121 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12122 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12122. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12122 : WorldParameters where
  hiddenCharge := (149912977 / 125000000000 : ℝ)
  frame := (317009217969 / 500000000000 : ℝ)
  moment := (5327304143 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12122 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501754298339 / 1000000000000 : ℝ)
    root := (7516917033 / 1000000000000 : ℝ) }

noncomputable def scalar12122 : ScalarCertificate 12122 world12122 agent12122 where
  dimensionLo := 12122
  dimensionHi := 12122
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2318202199 / 1000000000000 : ℝ)
  frameLo := (317009217969 / 500000000000 : ℝ)
  frameHi := (1501754298339 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12122]
  agentFrame_pos := by norm_num only [agent12122]
  worldRadius := (2318202199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12122]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1348667557 / 1000000000000 : ℝ)
  lowerTail := (853761511 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1004654911 / 125000000000 : ℝ)
  ledger := by
    have h : (149912977 / 125000000000 : ℚ) +
        (5327304143 / 500000000000000000 : ℚ) / (2318202199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1348667557 / 1000000000000 : ℚ) + (853761511 / 500000000000 : ℚ) ≤
        (1004654911 / 125000000000 : ℚ) := by norm_num only
    have hc : (((149912977 / 125000000000 : ℚ) +
        (5327304143 / 500000000000000000 : ℚ) / (2318202199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1348667557 / 1000000000000 : ℚ) + (853761511 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1004654911 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12122]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12122 :
    2 * 160 < 12122 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999217 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12122 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12123 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12123. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12123 : WorldParameters where
  hiddenCharge := (74953301 / 62500000000 : ℝ)
  frame := (317001604133 / 500000000000 : ℝ)
  moment := (10652307323 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12123 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (375426235651 / 250000000000 : ℝ)
    root := (3758119717 / 500000000000 : ℝ) }

noncomputable def scalar12123 : ScalarCertificate 12123 world12123 agent12123 where
  dimensionLo := 12123
  dimensionHi := 12123
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2318604999 / 1000000000000 : ℝ)
  frameLo := (317001604133 / 500000000000 : ℝ)
  frameHi := (375426235651 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12123]
  agentFrame_pos := by norm_num only [agent12123]
  worldRadius := (2318604999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12123]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (673727079 / 500000000000 : ℝ)
  lowerTail := (213262357 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1606686783 / 200000000000 : ℝ)
  ledger := by
    have h : (74953301 / 62500000000 : ℚ) +
        (10652307323 / 1000000000000000000 : ℚ) / (2318604999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (673727079 / 500000000000 : ℚ) + (213262357 / 125000000000 : ℚ) ≤
        (1606686783 / 200000000000 : ℚ) := by norm_num only
    have hc : (((74953301 / 62500000000 : ℚ) +
        (10652307323 / 1000000000000000000 : ℚ) / (2318604999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (673727079 / 500000000000 : ℚ) + (213262357 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1606686783 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12123]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12123 :
    2 * 160 < 12123 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999711 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12123 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12124 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12124. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12124 : WorldParameters where
  hiddenCharge := (119920183 / 100000000000 : ℝ)
  frame := (31699399159 / 50000000000 : ℝ)
  moment := (10650007053 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12124 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501655616413 / 1000000000000 : ℝ)
    root := (1878890513 / 250000000000 : ℝ) }

noncomputable def scalar12124 : ScalarCertificate 12124 world12124 agent12124 where
  dimensionLo := 12124
  dimensionHi := 12124
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2319007899 / 1000000000000 : ℝ)
  frameLo := (31699399159 / 50000000000 : ℝ)
  frameHi := (1501655616413 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12124]
  agentFrame_pos := by norm_num only [agent12124]
  worldRadius := (2319007899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12124]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (33656053 / 25000000000 : ℝ)
  lowerTail := (1704676203 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8029632047 / 1000000000000 : ℝ)
  ledger := by
    have h : (119920183 / 100000000000 : ℚ) +
        (10650007053 / 1000000000000000000 : ℚ) / (2319007899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (33656053 / 25000000000 : ℚ) + (1704676203 / 1000000000000 : ℚ) ≤
        (8029632047 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((119920183 / 100000000000 : ℚ) +
        (10650007053 / 1000000000000000000 : ℚ) / (2319007899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (33656053 / 25000000000 : ℚ) + (1704676203 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8029632047 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12124]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12124 :
    2 * 160 < 12124 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999691 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12124 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12125 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12125. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12125 : WorldParameters where
  hiddenCharge := (599575429 / 500000000000 : ℝ)
  frame := (633972760679 / 1000000000000 : ℝ)
  moment := (5323853739 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12125 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750803159873 / 500000000000 : ℝ)
    root := (7514884811 / 1000000000000 : ℝ) }

noncomputable def scalar12125 : ScalarCertificate 12125 world12125 agent12125 where
  dimensionLo := 12125
  dimensionHi := 12125
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2319410799 / 1000000000000 : ℝ)
  frameLo := (633972760679 / 1000000000000 : ℝ)
  frameHi := (750803159873 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12125]
  agentFrame_pos := by norm_num only [agent12125]
  worldRadius := (2319410799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12125]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (168128913 / 125000000000 : ℝ)
  lowerTail := (340650981 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4012916777 / 500000000000 : ℝ)
  ledger := by
    have h : (599575429 / 500000000000 : ℚ) +
        (5323853739 / 500000000000000000 : ℚ) / (2319410799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (168128913 / 125000000000 : ℚ) + (340650981 / 200000000000 : ℚ) ≤
        (4012916777 / 500000000000 : ℚ) := by norm_num only
    have hc : (((599575429 / 500000000000 : ℚ) +
        (5323853739 / 500000000000000000 : ℚ) / (2319410799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (168128913 / 125000000000 : ℚ) + (340650981 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4012916777 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12125]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12125 :
    2 * 160 < 12125 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995457 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12125 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12126 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12126. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12126 : WorldParameters where
  hiddenCharge := (1199099901 / 1000000000000 : ℝ)
  frame := (316978770381 / 500000000000 : ℝ)
  moment := (2661352149 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12126 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501557046521 / 1000000000000 : ℝ)
    root := (7514207863 / 1000000000000 : ℝ) }

noncomputable def scalar12126 : ScalarCertificate 12126 world12126 agent12126 where
  dimensionLo := 12126
  dimensionHi := 12126
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2319813799 / 1000000000000 : ℝ)
  frameLo := (316978770381 / 500000000000 : ℝ)
  frameHi := (1501557046521 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12126]
  agentFrame_pos := by norm_num only [agent12126]
  worldRadius := (2319813799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12126]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1343821881 / 1000000000000 : ℝ)
  lowerTail := (425458787 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4011019311 / 500000000000 : ℝ)
  ledger := by
    have h : (1199099901 / 1000000000000 : ℚ) +
        (2661352149 / 250000000000000000 : ℚ) / (2319813799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1343821881 / 1000000000000 : ℚ) + (425458787 / 250000000000 : ℚ) ≤
        (4011019311 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1199099901 / 1000000000000 : ℚ) +
        (2661352149 / 250000000000000000 : ℚ) / (2319813799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1343821881 / 1000000000000 : ℚ) + (425458787 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4011019311 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12126]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12126 :
    2 * 160 < 12126 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999341 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12126 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12127 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12127. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12127 : WorldParameters where
  hiddenCharge := (1199048957 / 1000000000000 : ℝ)
  frame := (158485580857 / 250000000000 : ℝ)
  moment := (10643110407 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12127 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37537695221 / 25000000000 : ℝ)
    root := (1878382783 / 250000000000 : ℝ) }

noncomputable def scalar12127 : ScalarCertificate 12127 world12127 agent12127 where
  dimensionLo := 12127
  dimensionHi := 12127
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2320216599 / 1000000000000 : ℝ)
  frameLo := (158485580857 / 250000000000 : ℝ)
  frameHi := (37537695221 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12127]
  agentFrame_pos := by norm_num only [agent12127]
  worldRadius := (2320216599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12127]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1342613603 / 1000000000000 : ℝ)
  lowerTail := (106276041 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8018247239 / 1000000000000 : ℝ)
  ledger := by
    have h : (1199048957 / 1000000000000 : ℚ) +
        (10643110407 / 1000000000000000000 : ℚ) / (2320216599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1342613603 / 1000000000000 : ℚ) + (106276041 / 62500000000 : ℚ) ≤
        (8018247239 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1199048957 / 1000000000000 : ℚ) +
        (10643110407 / 1000000000000000000 : ℚ) / (2320216599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1342613603 / 1000000000000 : ℚ) + (106276041 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((8018247239 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12127]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12127 :
    2 * 160 < 12127 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998659 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12127 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12128 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12128. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12128 : WorldParameters where
  hiddenCharge := (299749507 / 250000000000 : ℝ)
  frame := (633927108677 / 1000000000000 : ℝ)
  moment := (665050807 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12128 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1173014527 / 781250000 : ℝ)
    root := (7512854617 / 1000000000000 : ℝ) }

noncomputable def scalar12128 : ScalarCertificate 12128 world12128 agent12128 where
  dimensionLo := 12128
  dimensionHi := 12128
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2320619599 / 1000000000000 : ℝ)
  frameLo := (633927108677 / 1000000000000 : ℝ)
  frameHi := (1173014527 / 781250000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12128]
  agentFrame_pos := by norm_num only [agent12128]
  worldRadius := (2320619599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12128]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (268281347 / 200000000000 : ℝ)
  lowerTail := (1698999729 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8014459287 / 1000000000000 : ℝ)
  ledger := by
    have h : (299749507 / 250000000000 : ℚ) +
        (665050807 / 62500000000000000 : ℚ) / (2320619599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (268281347 / 200000000000 : ℚ) + (1698999729 / 1000000000000 : ℚ) ≤
        (8014459287 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((299749507 / 250000000000 : ℚ) +
        (665050807 / 62500000000000000 : ℚ) / (2320619599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (268281347 / 200000000000 : ℚ) + (1698999729 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8014459287 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12128]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12128 :
    2 * 160 < 12128 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999043 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12128 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12129 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12129. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12129 : WorldParameters where
  hiddenCharge := (1198947113 / 1000000000000 : ℝ)
  frame := (158477974127 / 250000000000 : ℝ)
  moment := (1063851611 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12129 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501409409723 / 1000000000000 : ℝ)
    root := (7512178319 / 1000000000000 : ℝ) }

noncomputable def scalar12129 : ScalarCertificate 12129 world12129 agent12129 where
  dimensionLo := 12129
  dimensionHi := 12129
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2321022399 / 1000000000000 : ℝ)
  frameLo := (158477974127 / 250000000000 : ℝ)
  frameHi := (1501409409723 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12129]
  agentFrame_pos := by norm_num only [agent12129]
  worldRadius := (2321022399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12129]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1340200983 / 1000000000000 : ℝ)
  lowerTail := (53049501 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8010674819 / 1000000000000 : ℝ)
  ledger := by
    have h : (1198947113 / 1000000000000 : ℚ) +
        (1063851611 / 100000000000000000 : ℚ) / (2321022399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1340200983 / 1000000000000 : ℚ) + (53049501 / 31250000000 : ℚ) ≤
        (8010674819 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1198947113 / 1000000000000 : ℚ) +
        (1063851611 / 100000000000000000 : ℚ) / (2321022399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1340200983 / 1000000000000 : ℚ) + (53049501 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((8010674819 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12129]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12129 :
    2 * 160 < 12129 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994429 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12129 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12130 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12130. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12130 : WorldParameters where
  hiddenCharge := (299724053 / 250000000000 : ℝ)
  frame := (15847417173 / 25000000000 : ℝ)
  moment := (531811 / 50000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12130 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501360248247 / 1000000000000 : ℝ)
    root := (93893777 / 12500000000 : ℝ) }

noncomputable def scalar12130 : ScalarCertificate 12130 world12130 agent12130 where
  dimensionLo := 12130
  dimensionHi := 12130
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2321425399 / 1000000000000 : ℝ)
  frameLo := (15847417173 / 25000000000 : ℝ)
  frameHi := (1501360248247 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12130]
  agentFrame_pos := by norm_num only [agent12130]
  worldRadius := (2321425399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12130]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (669498289 / 500000000000 : ℝ)
  lowerTail := (1696169833 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8006893651 / 1000000000000 : ℝ)
  ledger := by
    have h : (299724053 / 250000000000 : ℚ) +
        (531811 / 50000000000000 : ℚ) / (2321425399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (669498289 / 500000000000 : ℚ) + (1696169833 / 1000000000000 : ℚ) ≤
        (8006893651 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((299724053 / 250000000000 : ℚ) +
        (531811 / 50000000000000 : ℚ) / (2321425399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (669498289 / 500000000000 : ℚ) + (1696169833 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8006893651 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12130]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12130 :
    2 * 160 < 12130 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999109 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12130 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12131 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12131. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12131 : WorldParameters where
  hiddenCharge := (47953813 / 40000000000 : ℝ)
  frame := (633881479913 / 1000000000000 : ℝ)
  moment := (5316962291 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12131 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750655561117 / 500000000000 : ℝ)
    root := (3755413147 / 500000000000 : ℝ) }

noncomputable def scalar12131 : ScalarCertificate 12131 world12131 agent12131 where
  dimensionLo := 12131
  dimensionHi := 12131
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2321828299 / 1000000000000 : ℝ)
  frameLo := (633881479913 / 1000000000000 : ℝ)
  frameHi := (750655561117 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12131]
  agentFrame_pos := by norm_num only [agent12131]
  worldRadius := (2321828299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12131]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (26755869 / 20000000000 : ℝ)
  lowerTail := (211844631 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8003116139 / 1000000000000 : ℝ)
  ledger := by
    have h : (47953813 / 40000000000 : ℚ) +
        (5316962291 / 500000000000000000 : ℚ) / (2321828299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (26755869 / 20000000000 : ℚ) + (211844631 / 125000000000 : ℚ) ≤
        (8003116139 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((47953813 / 40000000000 : ℚ) +
        (5316962291 / 500000000000000000 : ℚ) / (2321828299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (26755869 / 20000000000 : ℚ) + (211844631 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8003116139 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12131]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12131 :
    2 * 160 < 12131 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997309 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12131 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12132 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12132. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12132 : WorldParameters where
  hiddenCharge := (299698613 / 250000000000 : ℝ)
  frame := (316933137743 / 500000000000 : ℝ)
  moment := (10631629857 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12132 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501262019543 / 1000000000000 : ℝ)
    root := (1877537661 / 250000000000 : ℝ) }

noncomputable def scalar12132 : ScalarCertificate 12132 world12132 agent12132 where
  dimensionLo := 12132
  dimensionHi := 12132
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2322231199 / 1000000000000 : ℝ)
  frameLo := (316933137743 / 500000000000 : ℝ)
  frameHi := (1501262019543 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12132]
  agentFrame_pos := by norm_num only [agent12132]
  worldRadius := (2322231199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12132]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1336591567 / 1000000000000 : ℝ)
  lowerTail := (1693345637 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3999671021 / 500000000000 : ℝ)
  ledger := by
    have h : (299698613 / 250000000000 : ℚ) +
        (10631629857 / 1000000000000000000 : ℚ) / (2322231199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1336591567 / 1000000000000 : ℚ) + (1693345637 / 1000000000000 : ℚ) ≤
        (3999671021 / 500000000000 : ℚ) := by norm_num only
    have hc : (((299698613 / 250000000000 : ℚ) +
        (10631629857 / 1000000000000000000 : ℚ) / (2322231199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1336591567 / 1000000000000 : ℚ) + (1693345637 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3999671021 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12132]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12132 :
    2 * 160 < 12132 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (549999777 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12132 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12133 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12133. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12133 : WorldParameters where
  hiddenCharge := (1198743593 / 1000000000000 : ℝ)
  frame := (633851073637 / 1000000000000 : ℝ)
  moment := (10629335823 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12133 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501212946213 / 1000000000000 : ℝ)
    root := (750947521 / 100000000000 : ℝ) }

noncomputable def scalar12133 : ScalarCertificate 12133 world12133 agent12133 where
  dimensionLo := 12133
  dimensionHi := 12133
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2322634099 / 1000000000000 : ℝ)
  frameLo := (633851073637 / 1000000000000 : ℝ)
  frameHi := (1501212946213 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12133]
  agentFrame_pos := by norm_num only [agent12133]
  worldRadius := (2322634099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12133]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1335390953 / 1000000000000 : ℝ)
  lowerTail := (845967817 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7995571413 / 1000000000000 : ℝ)
  ledger := by
    have h : (1198743593 / 1000000000000 : ℚ) +
        (10629335823 / 1000000000000000000 : ℚ) / (2322634099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1335390953 / 1000000000000 : ℚ) + (845967817 / 500000000000 : ℚ) ≤
        (7995571413 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1198743593 / 1000000000000 : ℚ) +
        (10629335823 / 1000000000000000000 : ℚ) / (2322634099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1335390953 / 1000000000000 : ℚ) + (845967817 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7995571413 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12133]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12133 :
    2 * 160 < 12133 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994987 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12133 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12109 :
    (1199968108026066973987 / 1000000000000000000000000 : ℝ) ≤ world12109.hiddenCharge ∧
    (634216631266927700427099 / 1000000000000000000000000 : ℝ) ≤ world12109.frame ∧
    (534229205352539 / 50000000000000000000000 : ℝ) ≤ world12109.moment ∧
    (23474976648405310253917 / 15625000000000000000000 : ℝ) ≤ agent12109.frame ∧
    (1505149142068041642027 / 200000000000000000000000 : ℝ) ≤ agent12109.root ∧
    scalar12109.worldRadius ≤ (2312964699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (643813020582754010397 / 500000000000000000000000 : ℝ) ≤ agent12109.charge ∧
    (170569736971025388231 / 125000000000000000000000 : ℝ) ≤ scalar12109.upperTail ∧
    (1726165676218468426017 / 1000000000000000000000000 : ℝ) ≤ scalar12109.lowerTail ∧
    scalar12109.totalBudget ≤ (8087028735073692247107 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12109, agent12109, scalar12109] <;> simp only [true_and]

theorem source_rounding12110 :
    (1199916923299711163279 / 1000000000000000000000000 : ℝ) ≤ world12110.hiddenCharge ∧
    (317100684960026471313461 / 500000000000000000000000 : ℝ) ≤ world12110.frame ∧
    (10682274094383829 / 1000000000000000000000000 : ℝ) ≤ world12110.moment ∧
    (1502348775953259345360029 / 1000000000000000000000000 : ℝ) ≤ agent12110.frame ∧
    (3762532638342479641393 / 500000000000000000000000 : ℝ) ≤ agent12110.root ∧
    scalar12110.worldRadius ≤ (2313367599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (643646496720792280877 / 500000000000000000000000 : ℝ) ≤ agent12110.charge ∧
    (681663904079201988129 / 500000000000000000000000 : ℝ) ≤ scalar12110.upperTail ∧
    (862361521697152339989 / 500000000000000000000000 : ℝ) ≤ scalar12110.lowerTail ∧
    scalar12110.totalBudget ≤ (1616635515817743254443 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12110, agent12110, scalar12110] <;> simp only [true_and]

theorem source_rounding12111 :
    (599932876404129692661 / 500000000000000000000000 : ℝ) ≤ world12111.hiddenCharge ∧
    (634186111167799111744801 / 1000000000000000000000000 : ℝ) ≤ world12111.frame ∧
    (10679964779417281 / 1000000000000000000000000 : ℝ) ≤ world12111.moment ∧
    (187787385285740926897029 / 125000000000000000000000 : ℝ) ≤ agent12111.frame ∧
    (7524385061970099564931 / 1000000000000000000000000 : ℝ) ≤ agent12111.root ∧
    scalar12111.worldRadius ≤ (2313770399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1286960360168308186407 / 1000000000000000000000000 : ℝ) ≤ agent12111.charge ∧
    (681049484523324194597 / 500000000000000000000000 : ℝ) ≤ scalar12111.upperTail ∧
    (1723281793339275844717 / 1000000000000000000000000 : ℝ) ≤ scalar12111.lowerTail ∧
    scalar12111.totalBudget ≤ (8079330034796192844583 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12111, agent12111, scalar12111] <;> simp only [true_and]

theorem source_rounding12112 :
    (119981459654653364841 / 100000000000000000000000 : ℝ) ≤ world12112.hiddenCharge ∧
    (317085427504731616467953 / 500000000000000000000000 : ℝ) ≤ world12112.frame ∧
    (2669414040470201 / 250000000000000000000000 : ℝ) ≤ world12112.moment ∧
    (187781176542884273339039 / 125000000000000000000000 : ℝ) ≤ agent12112.frame ∧
    (7523705066050900900677 / 1000000000000000000000000 : ℝ) ≤ agent12112.root ∧
    scalar12112.worldRadius ≤ (2314173299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (80414258795510947089 / 62500000000000000000000 : ℝ) ≤ agent12112.charge ∧
    (272174297250221346441 / 200000000000000000000000 : ℝ) ≤ scalar12112.upperTail ∧
    (860921022141661285053 / 500000000000000000000000 : ℝ) ≤ scalar12112.lowerTail ∧
    scalar12112.totalBudget ≤ (2018871495734582912797 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12112, agent12112, scalar12112] <;> simp only [true_and]

theorem source_rounding12113 :
    (299940863627338569707 / 250000000000000000000000 : ℝ) ≤ world12113.hiddenCharge ∧
    (126831120288868475871289 / 200000000000000000000000 : ℝ) ≤ world12113.frame ∧
    (2135069648300807 / 200000000000000000000000 : ℝ) ≤ world12113.moment ∧
    (150219977217008608173247 / 100000000000000000000000 : ℝ) ≤ agent12113.frame ∧
    (3761512644391391931599 / 500000000000000000000000 : ℝ) ≤ agent12113.root ∧
    scalar12113.worldRadius ≤ (2314576099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1286296334504742836101 / 1000000000000000000000000 : ℝ) ≤ agent12113.charge ∧
    (1359645223857326265301 / 1000000000000000000000000 : ℝ) ≤ scalar12113.upperTail ∧
    (860201820968052565789 / 500000000000000000000000 : ℝ) ≤ scalar12113.lowerTail ∧
    scalar12113.totalBudget ≤ (252238921180248929841 / 31250000000000000000000 : ℝ) := by
  norm_num only [world12113, agent12113, scalar12113] <;> simp only [true_and]

theorem source_rounding12114 :
    (1199712326691548101321 / 1000000000000000000000000 : ℝ) ≤ world12114.hiddenCharge ∧
    (317070175235866968082169 / 500000000000000000000000 : ℝ) ≤ world12114.frame ∧
    (10673041018016907 / 1000000000000000000000000 : ℝ) ≤ world12114.moment ∧
    (1502150161746204875653067 / 1000000000000000000000000 : ℝ) ≤ agent12114.frame ∧
    (75223457300213175587 / 10000000000000000000000 : ℝ) ≤ agent12114.root ∧
    scalar12114.worldRadius ≤ (2314978999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (80372808805164230529 / 62500000000000000000000 : ℝ) ≤ agent12114.charge ∧
    (271684067895638481063 / 200000000000000000000000 : ℝ) ≤ scalar12114.upperTail ∧
    (107435423118010538411 / 62500000000000000000000 : ℝ) ≤ scalar12114.lowerTail ∧
    scalar12114.totalBudget ≤ (8067808514695280404537 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12114, agent12114, scalar12114] <;> simp only [true_and]

theorem source_rounding12115 :
    (1199661213087940259679 / 1000000000000000000000000 : ℝ) ≤ world12115.hiddenCharge ∧
    (634125102090935624865987 / 1000000000000000000000000 : ℝ) ≤ world12115.frame ∧
    (2667683622787329 / 250000000000000000000000 : ℝ) ≤ world12115.moment ∧
    (187762571873241369438651 / 125000000000000000000000 : ℝ) ≤ agent12115.frame ∧
    (3760833194811109715349 / 500000000000000000000000 : ℝ) ≤ agent12115.root ∧
    scalar12115.worldRadius ≤ (2315381899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (257126791849500643123 / 200000000000000000000000 : ℝ) ≤ agent12115.charge ∧
    (1357196726944708422017 / 1000000000000000000000000 : ℝ) ≤ scalar12115.upperTail ∧
    (858765650535323777001 / 500000000000000000000000 : ℝ) ≤ scalar12115.lowerTail ∧
    scalar12115.totalBudget ≤ (4031987517251444808487 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12115, agent12115, scalar12115] <;> simp only [true_and]

theorem source_rounding12116 :
    (1199610113693362389323 / 1000000000000000000000000 : ℝ) ≤ world12116.hiddenCharge ∧
    (317054928150622694212041 / 500000000000000000000000 : ℝ) ≤ world12116.frame ∧
    (5334214330315729 / 500000000000000000000000 : ℝ) ≤ world12116.moment ∧
    (300410204799674470757023 / 200000000000000000000000 : ℝ) ≤ agent12116.frame ∧
    (7520987267441355064577 / 1000000000000000000000000 : ℝ) ≤ agent12116.root ∧
    scalar12116.worldRadius ≤ (2315784799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1285303388986097948299 / 1000000000000000000000000 : ℝ) ≤ agent12116.charge ∧
    (1355974434540988517593 / 1000000000000000000000000 : ℝ) ≤ scalar12116.upperTail ∧
    (85804864961207914753 / 50000000000000000000000 : ℝ) ≤ scalar12116.lowerTail ∧
    scalar12116.totalBudget ≤ (4030072572462328012269 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12116, agent12116, scalar12116] <;> simp only [true_and]

theorem source_rounding12117 :
    (299889757125660771433 / 250000000000000000000000 : ℝ) ≤ world12117.hiddenCharge ∧
    (634094613101961351548453 / 1000000000000000000000000 : ℝ) ≤ world12117.frame ∧
    (5333061763096719 / 500000000000000000000000 : ℝ) ≤ world12117.moment ∧
    (300400299326718727439923 / 200000000000000000000000 : ℝ) ≤ agent12117.frame ∧
    (7520308363334737992461 / 1000000000000000000000000 : ℝ) ≤ agent12117.root ∧
    scalar12117.worldRadius ≤ (2316187699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1284973229486193421703 / 1000000000000000000000000 : ℝ) ≤ agent12117.charge ∧
    (169344176353677639347 / 125000000000000000000000 : ℝ) ≤ scalar12117.upperTail ∧
    (857332348639901630291 / 500000000000000000000000 : ℝ) ≤ scalar12117.lowerTail ∧
    scalar12117.totalBudget ≤ (32225274912659537997 / 4000000000000000000000 : ℝ) := by
  norm_num only [world12117, agent12117, scalar12117] <;> simp only [true_and]

theorem source_rounding12118 :
    (239901591502124030117 / 200000000000000000000000 : ℝ) ≤ world12118.hiddenCharge ∧
    (634079372492382023118111 / 1000000000000000000000000 : ℝ) ≤ world12118.frame ∧
    (2665954771891441 / 250000000000000000000000 : ℝ) ≤ world12118.moment ∧
    (1501951998935706474527423 / 1000000000000000000000000 : ℝ) ≤ agent12118.frame ∧
    (1503925920065021422291 / 200000000000000000000000 : ℝ) ≤ agent12118.root ∧
    scalar12118.worldRadius ≤ (2316590599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1284643480136622158447 / 1000000000000000000000000 : ℝ) ≤ agent12118.charge ∧
    (1353533619032120972593 / 1000000000000000000000000 : ℝ) ≤ scalar12118.upperTail ∧
    (1713233462002901956541 / 1000000000000000000000000 : ℝ) ≤ scalar12118.lowerTail ∧
    scalar12118.totalBudget ≤ (8052495714923606193979 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12118, agent12118, scalar12118] <;> simp only [true_and]

theorem source_rounding12119 :
    (1199456900712126986633 / 1000000000000000000000000 : ℝ) ≤ world12119.hiddenCharge ∧
    (634064134471806043270367 / 1000000000000000000000000 : ℝ) ≤ world12119.frame ∧
    (5330757672239403 / 500000000000000000000000 : ℝ) ≤ world12119.moment ∧
    (11733613522531882926853 / 7812500000000000000000 : ℝ) ≤ agent12119.frame ∧
    (7518951131951646326503 / 1000000000000000000000000 : ℝ) ≤ agent12119.root ∧
    scalar12119.worldRadius ≤ (2316993399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1284314140327265655783 / 1000000000000000000000000 : ℝ) ≤ agent12119.charge ∧
    (676157549321499094209 / 500000000000000000000000 : ℝ) ≤ scalar12119.upperTail ∧
    (1711803628059888001879 / 1000000000000000000000000 : ℝ) ≤ scalar12119.lowerTail ∧
    scalar12119.totalBudget ≤ (8048676347500566983369 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12119, agent12119, scalar12119] <;> simp only [true_and]

theorem source_rounding12120 :
    (1199405858102003477241 / 1000000000000000000000000 : ℝ) ≤ world12120.hiddenCharge ∧
    (79256112379941555801959 / 125000000000000000000000 : ℝ) ≤ world12120.frame ∧
    (10659212296663223 / 1000000000000000000000000 : ℝ) ≤ world12120.moment ∧
    (750926546229056544476893 / 500000000000000000000000 : ℝ) ≤ agent12120.frame ∧
    (7518272881221353707377 / 1000000000000000000000000 : ℝ) ≤ agent12120.root ∧
    scalar12120.worldRadius ≤ (2317396399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (641992604724526188493 / 500000000000000000000000 : ℝ) ≤ agent12120.charge ∧
    (1351098025519626456339 / 1000000000000000000000000 : ℝ) ≤ scalar12120.upperTail ∧
    (213796925764103648649 / 125000000000000000000000 : ℝ) ≤ scalar12120.lowerTail ∧
    scalar12120.totalBudget ≤ (1608972100171200648657 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12120, agent12120, scalar12120] <;> simp only [true_and]

theorem source_rounding12121 :
    (599677414837545272719 / 500000000000000000000000 : ℝ) ≤ world12121.hiddenCharge ∧
    (634033666194860354980363 / 1000000000000000000000000 : ℝ) ≤ world12121.frame ∧
    (5328454971924877 / 500000000000000000000000 : ℝ) ≤ world12121.moment ∧
    (300360735514827066870557 / 200000000000000000000000 : ℝ) ≤ agent12121.frame ∧
    (3758797423995416315171 / 500000000000000000000000 : ℝ) ≤ agent12121.root ∧
    scalar12121.worldRadius ≤ (2317799199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (256731337378791149383 / 200000000000000000000000 : ℝ) ≤ agent12121.charge ∧
    (1349882056556173582261 / 1000000000000000000000000 : ℝ) ≤ scalar12121.upperTail ∧
    (13351159321717154351 / 7812500000000000000000 : ℝ) ≤ scalar12121.lowerTail ∧
    scalar12121.totalBudget ≤ (2010262027516933495957 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12121, agent12121, scalar12121] <;> simp only [true_and]

theorem source_rounding12122 :
    (299825953856557878131 / 250000000000000000000000 : ℝ) ≤ world12122.hiddenCharge ∧
    (317009217968544682685197 / 500000000000000000000000 : ℝ) ≤ world12122.frame ∧
    (10654608285769267 / 1000000000000000000000000 : ℝ) ≤ world12122.moment ∧
    (1501754298338051649770061 / 1000000000000000000000000 : ℝ) ≤ agent12122.frame ∧
    (751691703211683344719 / 100000000000000000000000 : ℝ) ≤ agent12122.root ∧
    scalar12122.worldRadius ≤ (2318202199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1283328572054992151759 / 1000000000000000000000000 : ℝ) ≤ agent12122.charge ∧
    (1348667556277507790011 / 1000000000000000000000000 : ℝ) ≤ scalar12122.upperTail ∧
    (1707523021216759875789 / 1000000000000000000000000 : ℝ) ≤ scalar12122.lowerTail ∧
    scalar12122.totalBudget ≤ (8037239288393579454359 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12122, agent12122, scalar12122] <;> simp only [true_and]

theorem source_rounding12123 :
    (1199252815350273452737 / 1000000000000000000000000 : ℝ) ≤ world12123.hiddenCharge ∧
    (634003208265519157843023 / 1000000000000000000000000 : ℝ) ≤ world12123.frame ∧
    (2130461464430563 / 200000000000000000000000 : ℝ) ≤ world12123.moment ∧
    (1501704942603435837038989 / 1000000000000000000000000 : ℝ) ≤ agent12123.frame ∧
    (939529929182031661487 / 125000000000000000000000 : ℝ) ≤ agent12123.root ∧
    scalar12123.worldRadius ≤ (2318604999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (320750216081554735733 / 250000000000000000000000 : ℝ) ≤ agent12123.charge ∧
    (1347454157277779368361 / 1000000000000000000000000 : ℝ) ≤ scalar12123.upperTail ∧
    (1706098855227033786811 / 1000000000000000000000000 : ℝ) ≤ scalar12123.lowerTail ∧
    scalar12123.totalBudget ≤ (8033433915589659536143 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12123, agent12123, scalar12123] <;> simp only [true_and]

theorem source_rounding12124 :
    (149900228680257720841 / 125000000000000000000000 : ℝ) ≤ world12124.hiddenCharge ∧
    (633987983179449731231697 / 1000000000000000000000000 : ℝ) ≤ world12124.frame ∧
    (10650007052731417 / 1000000000000000000000000 : ℝ) ≤ world12124.moment ∧
    (46926738012902326381831 / 31250000000000000000000 : ℝ) ≤ agent12124.frame ∧
    (7515562051866135887553 / 1000000000000000000000000 : ℝ) ≤ agent12124.root ∧
    scalar12124.worldRadius ≤ (2319007899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1282673563102732445131 / 1000000000000000000000000 : ℝ) ≤ agent12124.charge ∧
    (21035033122837130153 / 15625000000000000000000 : ℝ) ≤ scalar12124.upperTail ∧
    (852338101086318717229 / 500000000000000000000000 : ℝ) ≤ scalar12124.lowerTail ∧
    scalar12124.totalBudget ≤ (8029632047506649018361 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12124, agent12124, scalar12124] <;> simp only [true_and]

theorem source_rounding12125 :
    (1199150857696448318743 / 1000000000000000000000000 : ℝ) ≤ world12125.hiddenCharge ∧
    (126794552135636274277611 / 200000000000000000000000 : ℝ) ≤ world12125.frame ∧
    (2661926869309097 / 250000000000000000000000 : ℝ) ≤ world12125.moment ∧
    (750803159872945347151731 / 500000000000000000000000 : ℝ) ≤ agent12125.frame ∧
    (7514884810482461462359 / 1000000000000000000000000 : ℝ) ≤ agent12125.root ∧
    scalar12125.worldRadius ≤ (2319410799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1282346667780665968531 / 1000000000000000000000000 : ℝ) ≤ agent12125.charge ∧
    (672515651862908162163 / 500000000000000000000000 : ℝ) ≤ scalar12125.upperTail ∧
    (17032549045226074203 / 10000000000000000000000 : ℝ) ≤ scalar12125.lowerTail ∧
    scalar12125.totalBudget ≤ (8025833554081330075491 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12125, agent12125, scalar12125] <;> simp only [true_and]

theorem source_rounding12126 :
    (1199099900108286008787 / 1000000000000000000000000 : ℝ) ≤ world12126.hiddenCharge ∧
    (633957540761014630878999 / 1000000000000000000000000 : ℝ) ≤ world12126.frame ∧
    (2661352148849779 / 250000000000000000000000 : ℝ) ≤ world12126.moment ∧
    (1501557046520338494061779 / 1000000000000000000000000 : ℝ) ≤ agent12126.frame ∧
    (7514207862620978220637 / 1000000000000000000000000 : ℝ) ≤ agent12126.root ∧
    scalar12126.worldRadius ≤ (2319813799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (320505044439296956279 / 250000000000000000000000 : ℝ) ≤ agent12126.charge ∧
    (1343821880821685011987 / 1000000000000000000000000 : ℝ) ≤ scalar12126.upperTail ∧
    (53182348364642304363 / 31250000000000000000000 : ℝ) ≤ scalar12126.lowerTail ∧
    scalar12126.totalBudget ≤ (2005509655710031199289 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12126, agent12126, scalar12126] <;> simp only [true_and]

theorem source_rounding12127 :
    (599524478336214387229 / 500000000000000000000000 : ℝ) ≤ world12127.hiddenCharge ∧
    (316971161713625101995367 / 500000000000000000000000 : ℝ) ≤ world12127.frame ∧
    (5321555203475533 / 500000000000000000000000 : ℝ) ≤ world12127.moment ∧
    (187688476104932486438601 / 125000000000000000000000 : ℝ) ≤ agent12127.frame ∧
    (3756765565700980533763 / 500000000000000000000000 : ℝ) ≤ agent12127.root ∧
    scalar12127.worldRadius ≤ (2320216599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (80105880776906209321 / 62500000000000000000000 : ℝ) ≤ agent12127.charge ∧
    (671306801467463547889 / 500000000000000000000000 : ℝ) ≤ scalar12127.upperTail ∧
    (1700416655670927281953 / 1000000000000000000000000 : ℝ) ≤ scalar12127.lowerTail ∧
    scalar12127.totalBudget ≤ (250570226249534240947 / 31250000000000000000000 : ℝ) := by
  norm_num only [world12127, agent12127, scalar12127] <;> simp only [true_and]

theorem source_rounding12128 :
    (119899802738373429847 / 100000000000000000000000 : ℝ) ≤ world12128.hiddenCharge ∧
    (158481777169047300142247 / 250000000000000000000000 : ℝ) ≤ world12128.frame ∧
    (10640812911623887 / 1000000000000000000000000 : ℝ) ≤ world12128.moment ∧
    (375364648639935710404689 / 250000000000000000000000 : ℝ) ≤ agent12128.frame ∧
    (469553413542689885029 / 62500000000000000000000 : ℝ) ≤ agent12128.root ∧
    scalar12128.worldRadius ≤ (2320619599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (16017105139997911521 / 12500000000000000000000 : ℝ) ≤ agent12128.charge ∧
    (134140673407054389813 / 100000000000000000000000 : ℝ) ≤ scalar12128.upperTail ∧
    (1698999728927982892439 / 1000000000000000000000000 : ℝ) ≤ scalar12128.lowerTail ∧
    scalar12128.totalBudget ≤ (8014459287729750619161 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12128, agent12128, scalar12128] <;> simp only [true_and]

theorem source_rounding12129 :
    (1198947112237062651759 / 1000000000000000000000000 : ℝ) ≤ world12129.hiddenCharge ∧
    (316955948253566456460913 / 500000000000000000000000 : ℝ) ≤ world12129.frame ∧
    (132981451364367 / 12500000000000000000000 : ℝ) ≤ world12129.moment ∧
    (1501409409722506592707103 / 1000000000000000000000000 : ℝ) ≤ agent12129.frame ∧
    (1878044579580495821283 / 250000000000000000000000 : ℝ) ≤ agent12129.root ∧
    scalar12129.worldRadius ≤ (2321022399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (256208626693089999871 / 200000000000000000000000 : ℝ) ≤ agent12129.charge ∧
    (1340200982630867557673 / 1000000000000000000000000 : ℝ) ≤ scalar12129.upperTail ∧
    (1697584031557890674223 / 1000000000000000000000000 : ℝ) ≤ scalar12129.lowerTail ∧
    scalar12129.totalBudget ≤ (4005337409871538851659 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12129, agent12129, scalar12129] <;> simp only [true_and]

theorem source_rounding12130 :
    (239779242245454988103 / 200000000000000000000000 : ℝ) ≤ world12130.hiddenCharge ∧
    (3961854293246142304237 / 6250000000000000000000 : ℝ) ≤ world12130.frame ∧
    (5318109999629669 / 500000000000000000000000 : ℝ) ≤ world12130.moment ∧
    (1501360248246818399435159 / 1000000000000000000000000 : ℝ) ≤ agent12130.frame ∧
    (3755751079767763348267 / 500000000000000000000000 : ℝ) ≤ agent12130.root ∧
    scalar12130.worldRadius ≤ (2321425399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (64035912931431957353 / 50000000000000000000000 : ℝ) ≤ agent12130.charge ∧
    (267799315500638203541 / 200000000000000000000000 : ℝ) ≤ scalar12130.upperTail ∧
    (1696169832416038316397 / 1000000000000000000000000 : ℝ) ≤ scalar12130.lowerTail ∧
    scalar12130.totalBudget ≤ (8006893651585504605627 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12130, agent12130, scalar12130] <;> simp only [true_and]

theorem source_rounding12131 :
    (599422662174617329449 / 500000000000000000000000 : ℝ) ≤ world12131.hiddenCharge ∧
    (19808796247257522060329 / 31250000000000000000000 : ℝ) ≤ world12131.frame ∧
    (10633924581685807 / 1000000000000000000000000 : ℝ) ≤ world12131.moment ∧
    (375327780558449026938201 / 250000000000000000000000 : ℝ) ≤ agent12131.frame ∧
    (93885328668500946043 / 12500000000000000000000 : ℝ) ≤ agent12131.root ∧
    scalar12131.worldRadius ≤ (2321828299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1280393786091714074857 / 1000000000000000000000000 : ℝ) ≤ agent12131.charge ∧
    (1337793449518110039651 / 1000000000000000000000000 : ℝ) ≤ scalar12131.upperTail ∧
    (13558056376139666069 / 8000000000000000000000 : ℝ) ≤ scalar12131.lowerTail ∧
    scalar12131.totalBudget ≤ (800311613983566603389 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12131, agent12131, scalar12131] <;> simp only [true_and]

theorem source_rounding12132 :
    (1198794451597810388089 / 1000000000000000000000000 : ℝ) ≤ world12132.hiddenCharge ∧
    (633866275485008794220171 / 1000000000000000000000000 : ℝ) ≤ world12132.frame ∧
    (10631629856160989 / 1000000000000000000000000 : ℝ) ≤ world12132.moment ∧
    (1501262019542252362238813 / 1000000000000000000000000 : ℝ) ≤ agent12132.frame ∧
    (938768830419585061203 / 125000000000000000000000 : ℝ) ≤ agent12132.root ∧
    scalar12132.worldRadius ≤ (2322231199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (128006971525801167891 / 100000000000000000000000 : ℝ) ≤ agent12132.charge ∧
    (1336591566978237946481 / 1000000000000000000000000 : ℝ) ≤ scalar12132.upperTail ∧
    (1693345636993284140217 / 1000000000000000000000000 : ℝ) ≤ scalar12132.lowerTail ∧
    scalar12132.totalBudget ≤ (7999342042997652784167 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12132, agent12132, scalar12132] <;> simp only [true_and]

theorem source_rounding12133 :
    (239748718593573808081 / 200000000000000000000000 : ℝ) ≤ world12133.hiddenCharge ∧
    (633851073636989246359023 / 1000000000000000000000000 : ℝ) ≤ world12133.frame ∧
    (5314667911208537 / 500000000000000000000000 : ℝ) ≤ world12133.moment ∧
    (750606473106247431032213 / 500000000000000000000000 : ℝ) ≤ agent12133.frame ∧
    (7509475209023695506213 / 1000000000000000000000000 : ℝ) ≤ agent12133.root ∧
    scalar12133.worldRadius ≤ (2322634099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1279746045531890086507 / 1000000000000000000000000 : ℝ) ≤ agent12133.charge ∧
    (267078190593200516639 / 200000000000000000000000 : ℝ) ≤ scalar12133.upperTail ∧
    (1691935633047089437703 / 1000000000000000000000000 : ℝ) ≤ scalar12133.lowerTail ∧
    scalar12133.totalBudget ≤ (7995571413595552859457 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12133, agent12133, scalar12133] <;> simp only [true_and]

noncomputable def paperAgent12109 : AgentParameters :=
  { agent12109 with charge := (321906511 / 250000000000 : ℝ) }

theorem agent_is_repriced12109 : agent12109 =
    BstLean.Part265.agentRepriced 12109 world12109 paperAgent12109 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12109, agent12109]

noncomputable def paperAgent12110 : AgentParameters :=
  { agent12110 with charge := (321823249 / 250000000000 : ℝ) }

theorem agent_is_repriced12110 : agent12110 =
    BstLean.Part265.agentRepriced 12110 world12110 paperAgent12110 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12110, agent12110]

noncomputable def paperAgent12111 : AgentParameters :=
  { agent12111 with charge := (1286960363 / 1000000000000 : ℝ) }

theorem agent_is_repriced12111 : agent12111 =
    BstLean.Part265.agentRepriced 12111 world12111 paperAgent12111 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12111, agent12111]

noncomputable def paperAgent12112 : AgentParameters :=
  { agent12112 with charge := (80414259 / 62500000000 : ℝ) }

theorem agent_is_repriced12112 : agent12112 =
    BstLean.Part265.agentRepriced 12112 world12112 paperAgent12112 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12112, agent12112]

noncomputable def paperAgent12113 : AgentParameters :=
  { agent12113 with charge := (643148169 / 500000000000 : ℝ) }

theorem agent_is_repriced12113 : agent12113 =
    BstLean.Part265.agentRepriced 12113 world12113 paperAgent12113 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12113, agent12113]

noncomputable def paperAgent12114 : AgentParameters :=
  { agent12114 with charge := (257192989 / 200000000000 : ℝ) }

theorem agent_is_repriced12114 : agent12114 =
    BstLean.Part265.agentRepriced 12114 world12114 paperAgent12114 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12114, agent12114]

noncomputable def paperAgent12115 : AgentParameters :=
  { agent12115 with charge := (642816981 / 500000000000 : ℝ) }

theorem agent_is_repriced12115 : agent12115 =
    BstLean.Part265.agentRepriced 12115 world12115 paperAgent12115 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12115, agent12115]

noncomputable def paperAgent12116 : AgentParameters :=
  { agent12116 with charge := (40165731 / 31250000000 : ℝ) }

theorem agent_is_repriced12116 : agent12116 =
    BstLean.Part265.agentRepriced 12116 world12116 paperAgent12116 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12116, agent12116]

noncomputable def paperAgent12117 : AgentParameters :=
  { agent12117 with charge := (1284973233 / 1000000000000 : ℝ) }

theorem agent_is_repriced12117 : agent12117 =
    BstLean.Part265.agentRepriced 12117 world12117 paperAgent12117 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12117, agent12117]

noncomputable def paperAgent12118 : AgentParameters :=
  { agent12118 with charge := (1284643483 / 1000000000000 : ℝ) }

theorem agent_is_repriced12118 : agent12118 =
    BstLean.Part265.agentRepriced 12118 world12118 paperAgent12118 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12118, agent12118]

noncomputable def paperAgent12119 : AgentParameters :=
  { agent12119 with charge := (40134817 / 31250000000 : ℝ) }

theorem agent_is_repriced12119 : agent12119 =
    BstLean.Part265.agentRepriced 12119 world12119 paperAgent12119 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12119, agent12119]

noncomputable def paperAgent12120 : AgentParameters :=
  { agent12120 with charge := (320996303 / 250000000000 : ℝ) }

theorem agent_is_repriced12120 : agent12120 =
    BstLean.Part265.agentRepriced 12120 world12120 paperAgent12120 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12120, agent12120]

noncomputable def paperAgent12121 : AgentParameters :=
  { agent12121 with charge := (128365669 / 100000000000 : ℝ) }

theorem agent_is_repriced12121 : agent12121 =
    BstLean.Part265.agentRepriced 12121 world12121 paperAgent12121 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12121, agent12121]

noncomputable def paperAgent12122 : AgentParameters :=
  { agent12122 with charge := (51333143 / 40000000000 : ℝ) }

theorem agent_is_repriced12122 : agent12122 =
    BstLean.Part265.agentRepriced 12122 world12122 paperAgent12122 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12122, agent12122]

noncomputable def paperAgent12123 : AgentParameters :=
  { agent12123 with charge := (320750217 / 250000000000 : ℝ) }

theorem agent_is_repriced12123 : agent12123 =
    BstLean.Part265.agentRepriced 12123 world12123 paperAgent12123 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12123, agent12123]

noncomputable def paperAgent12124 : AgentParameters :=
  { agent12124 with charge := (641336783 / 500000000000 : ℝ) }

theorem agent_is_repriced12124 : agent12124 =
    BstLean.Part265.agentRepriced 12124 world12124 paperAgent12124 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12124, agent12124]

noncomputable def paperAgent12125 : AgentParameters :=
  { agent12125 with charge := (1282346671 / 1000000000000 : ℝ) }

theorem agent_is_repriced12125 : agent12125 =
    BstLean.Part265.agentRepriced 12125 world12125 paperAgent12125 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12125, agent12125]

noncomputable def paperAgent12126 : AgentParameters :=
  { agent12126 with charge := (1282020181 / 1000000000000 : ℝ) }

theorem agent_is_repriced12126 : agent12126 =
    BstLean.Part265.agentRepriced 12126 world12126 paperAgent12126 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12126, agent12126]

noncomputable def paperAgent12127 : AgentParameters :=
  { agent12127 with charge := (80105881 / 62500000000 : ℝ) }

theorem agent_is_repriced12127 : agent12127 =
    BstLean.Part265.agentRepriced 12127 world12127 paperAgent12127 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12127, agent12127]

noncomputable def paperAgent12128 : AgentParameters :=
  { agent12128 with charge := (256273683 / 200000000000 : ℝ) }

theorem agent_is_repriced12128 : agent12128 =
    BstLean.Part265.agentRepriced 12128 world12128 paperAgent12128 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12128, agent12128]

noncomputable def paperAgent12129 : AgentParameters :=
  { agent12129 with charge := (1281043137 / 1000000000000 : ℝ) }

theorem agent_is_repriced12129 : agent12129 =
    BstLean.Part265.agentRepriced 12129 world12129 paperAgent12129 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12129, agent12129]

noncomputable def paperAgent12130 : AgentParameters :=
  { agent12130 with charge := (640359131 / 500000000000 : ℝ) }

theorem agent_is_repriced12130 : agent12130 =
    BstLean.Part265.agentRepriced 12130 world12130 paperAgent12130 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12130, agent12130]

noncomputable def paperAgent12131 : AgentParameters :=
  { agent12131 with charge := (1280393789 / 1000000000000 : ℝ) }

theorem agent_is_repriced12131 : agent12131 =
    BstLean.Part265.agentRepriced 12131 world12131 paperAgent12131 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12131, agent12131]

noncomputable def paperAgent12132 : AgentParameters :=
  { agent12132 with charge := (640034859 / 500000000000 : ℝ) }

theorem agent_is_repriced12132 : agent12132 =
    BstLean.Part265.agentRepriced 12132 world12132 paperAgent12132 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12132, agent12132]

noncomputable def paperAgent12133 : AgentParameters :=
  { agent12133 with charge := (1279746049 / 1000000000000 : ℝ) }

theorem agent_is_repriced12133 : agent12133 =
    BstLean.Part265.agentRepriced 12133 world12133 paperAgent12133 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12133, agent12133]

end BstLean.Part281
