import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 11959 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11959. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11959 : WorldParameters where
  hiddenCharge := (301952513 / 250000000000 : ℝ)
  frame := (318267813311 / 500000000000 : ℝ)
  moment := (441075463 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11959 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735760449053 / 500000000000 : ℝ)
    root := (7235008049 / 1000000000000 : ℝ) }

noncomputable def scalar11959 : ScalarCertificate 11959 world11959 agent11959 where
  dimensionLo := 11959
  dimensionHi := 11959
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2413887599 / 1000000000000 : ℝ)
  frameLo := (318267813311 / 500000000000 : ℝ)
  frameHi := (735760449053 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11959]
  agentFrame_pos := by norm_num only [agent11959]
  worldRadius := (2413887599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11959]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (608978167 / 500000000000 : ℝ)
  lowerTail := (195234347 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (479958807 / 62500000000 : ℝ)
  ledger := by
    have h : (301952513 / 250000000000 : ℚ) +
        (441075463 / 40000000000000000 : ℚ) / (2413887599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (608978167 / 500000000000 : ℚ) + (195234347 / 125000000000 : ℚ) ≤
        (479958807 / 62500000000 : ℚ) := by norm_num only
    have hc : (((301952513 / 250000000000 : ℚ) +
        (441075463 / 40000000000000000 : ℚ) / (2413887599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (608978167 / 500000000000 : ℚ) + (195234347 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((479958807 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11959]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11959 :
    2 * 160 < 11959 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (343749981 / 31250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11959 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11960 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11960. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11960 : WorldParameters where
  hiddenCharge := (9435599 / 7812500000 : ℝ)
  frame := (636519967967 / 1000000000000 : ℝ)
  moment := (2204894181 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11960 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367868998931 / 250000000000 : ℝ)
    root := (1808585547 / 250000000000 : ℝ) }

noncomputable def scalar11960 : ScalarCertificate 11960 world11960 agent11960 where
  dimensionLo := 11960
  dimensionHi := 11960
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2414302099 / 1000000000000 : ℝ)
  frameLo := (636519967967 / 1000000000000 : ℝ)
  frameHi := (367868998931 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11960]
  agentFrame_pos := by norm_num only [agent11960]
  worldRadius := (2414302099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11960]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (608432359 / 500000000000 : ℝ)
  lowerTail := (156057957 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1535167291 / 200000000000 : ℝ)
  ledger := by
    have h : (9435599 / 7812500000 : ℚ) +
        (2204894181 / 200000000000000000 : ℚ) / (2414302099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (608432359 / 500000000000 : ℚ) + (156057957 / 100000000000 : ℚ) ≤
        (1535167291 / 200000000000 : ℚ) := by norm_num only
    have hc : (((9435599 / 7812500000 : ℚ) +
        (2204894181 / 200000000000000000 : ℚ) / (2414302099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (608432359 / 500000000000 : ℚ) + (156057957 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1535167291 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11960]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11960 :
    2 * 160 < 11960 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996029 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11960 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11961 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11961. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11961 : WorldParameters where
  hiddenCharge := (1207703307 / 1000000000000 : ℝ)
  frame := (39781519501 / 62500000000 : ℝ)
  moment := (5511027987 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11961 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471431111369 / 1000000000000 : ℝ)
    root := (3616838279 / 500000000000 : ℝ) }

noncomputable def scalar11961 : ScalarCertificate 11961 world11961 agent11961 where
  dimensionLo := 11961
  dimensionHi := 11961
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2414716699 / 1000000000000 : ℝ)
  frameLo := (39781519501 / 62500000000 : ℝ)
  frameHi := (1471431111369 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11961]
  agentFrame_pos := by norm_num only [agent11961]
  worldRadius := (2414716699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11961]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (607887151 / 500000000000 : ℝ)
  lowerTail := (779642851 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7672335143 / 1000000000000 : ℝ)
  ledger := by
    have h : (1207703307 / 1000000000000 : ℚ) +
        (5511027987 / 500000000000000000 : ℚ) / (2414716699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (607887151 / 500000000000 : ℚ) + (779642851 / 500000000000 : ℚ) ≤
        (7672335143 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1207703307 / 1000000000000 : ℚ) +
        (5511027987 / 500000000000000000 : ℚ) / (2414716699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (607887151 / 500000000000 : ℚ) + (779642851 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7672335143 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11961]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11961 :
    2 * 160 < 11961 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (219999951 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11961 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11962 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11962. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11962 : WorldParameters where
  hiddenCharge := (1207649957 / 1000000000000 : ℝ)
  frame := (318244329383 / 500000000000 : ℝ)
  moment := (11019641783 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11962 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471386250977 / 1000000000000 : ℝ)
    root := (7233011081 / 1000000000000 : ℝ) }

noncomputable def scalar11962 : ScalarCertificate 11962 world11962 agent11962 where
  dimensionLo := 11962
  dimensionHi := 11962
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2415131399 / 1000000000000 : ℝ)
  frameLo := (318244329383 / 500000000000 : ℝ)
  frameHi := (1471386250977 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11962]
  agentFrame_pos := by norm_num only [agent11962]
  worldRadius := (2415131399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11962]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1214685051 / 1000000000000 : ℝ)
  lowerTail := (778996571 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1917209227 / 250000000000 : ℝ)
  ledger := by
    have h : (1207649957 / 1000000000000 : ℚ) +
        (11019641783 / 1000000000000000000 : ℚ) / (2415131399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1214685051 / 1000000000000 : ℚ) + (778996571 / 500000000000 : ℚ) ≤
        (1917209227 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1207649957 / 1000000000000 : ℚ) +
        (11019641783 / 1000000000000000000 : ℚ) / (2415131399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1214685051 / 1000000000000 : ℚ) + (778996571 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1917209227 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11962]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11962 :
    2 * 160 < 11962 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999007 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11962 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11963 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11963. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11963 : WorldParameters where
  hiddenCharge := (603798311 / 500000000000 : ℝ)
  frame := (636473008219 / 1000000000000 : ℝ)
  moment := (1101722833 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11963 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183917676817 / 125000000000 : ℝ)
    root := (1446469183 / 200000000000 : ℝ) }

noncomputable def scalar11963 : ScalarCertificate 11963 world11963 agent11963 where
  dimensionLo := 11963
  dimensionHi := 11963
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2415545899 / 1000000000000 : ℝ)
  frameLo := (636473008219 / 1000000000000 : ℝ)
  frameHi := (183917676817 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11963]
  agentFrame_pos := by norm_num only [agent11963]
  worldRadius := (2415545899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11963]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (606798431 / 500000000000 : ℝ)
  lowerTail := (1556701753 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3832670989 / 500000000000 : ℝ)
  ledger := by
    have h : (603798311 / 500000000000 : ℚ) +
        (1101722833 / 100000000000000000 : ℚ) / (2415545899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (606798431 / 500000000000 : ℚ) + (1556701753 / 1000000000000 : ℚ) ≤
        (3832670989 / 500000000000 : ℚ) := by norm_num only
    have hc : (((603798311 / 500000000000 : ℚ) +
        (1101722833 / 100000000000000000 : ℚ) / (2415545899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (606798431 / 500000000000 : ℚ) + (1556701753 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3832670989 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11963]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11963 :
    2 * 160 < 11963 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499837 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11963 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11964 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11964. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11964 : WorldParameters where
  hiddenCharge := (603771651 / 500000000000 : ℝ)
  frame := (159114340093 / 250000000000 : ℝ)
  moment := (86053247 / 7812500000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11964 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471296602033 / 1000000000000 : ℝ)
    root := (361584049 / 50000000000 : ℝ) }

noncomputable def scalar11964 : ScalarCertificate 11964 world11964 agent11964 where
  dimensionLo := 11964
  dimensionHi := 11964
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2415960499 / 1000000000000 : ℝ)
  frameLo := (159114340093 / 250000000000 : ℝ)
  frameHi := (1471296602033 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11964]
  agentFrame_pos := by norm_num only [agent11964]
  worldRadius := (2415960499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11964]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1212509891 / 1000000000000 : ℝ)
  lowerTail := (155541173 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1532370047 / 200000000000 : ℝ)
  ledger := by
    have h : (603771651 / 500000000000 : ℚ) +
        (86053247 / 7812500000000000 : ℚ) / (2415960499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1212509891 / 1000000000000 : ℚ) + (155541173 / 100000000000 : ℚ) ≤
        (1532370047 / 200000000000 : ℚ) := by norm_num only
    have hc : (((603771651 / 500000000000 : ℚ) +
        (86053247 / 7812500000000000 : ℚ) / (2415960499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1212509891 / 1000000000000 : ℚ) + (155541173 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1532370047 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11964]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11964 :
    2 * 160 < 11964 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999457 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11964 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11965 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11965. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11965 : WorldParameters where
  hiddenCharge := (1207489997 / 1000000000000 : ℝ)
  frame := (25457668609 / 40000000000 : ℝ)
  moment := (11012403639 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11965 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735625903751 / 500000000000 : ℝ)
    root := (1807754069 / 250000000000 : ℝ) }

noncomputable def scalar11965 : ScalarCertificate 11965 world11965 agent11965 where
  dimensionLo := 11965
  dimensionHi := 11965
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2416375099 / 1000000000000 : ℝ)
  frameLo := (25457668609 / 40000000000 : ℝ)
  frameHi := (735625903751 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11965]
  agentFrame_pos := by norm_num only [agent11965]
  worldRadius := (2416375099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11965]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (605712021 / 500000000000 : ℝ)
  lowerTail := (310824591 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7658361621 / 1000000000000 : ℝ)
  ledger := by
    have h : (1207489997 / 1000000000000 : ℚ) +
        (11012403639 / 1000000000000000000 : ℚ) / (2416375099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (605712021 / 500000000000 : ℚ) + (310824591 / 200000000000 : ℚ) ≤
        (7658361621 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1207489997 / 1000000000000 : ℚ) +
        (11012403639 / 1000000000000000000 : ℚ) / (2416375099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (605712021 / 500000000000 : ℚ) + (310824591 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7658361621 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11965]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11965 :
    2 * 160 < 11965 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998699 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11965 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11966 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11966. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11966 : WorldParameters where
  hiddenCharge := (301859177 / 250000000000 : ℝ)
  frame := (318213036389 / 500000000000 : ℝ)
  moment := (11009992401 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11966 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91950440177 / 62500000000 : ℝ)
    root := (7230351803 / 1000000000000 : ℝ) }

noncomputable def scalar11966 : ScalarCertificate 11966 world11966 agent11966 where
  dimensionLo := 11966
  dimensionHi := 11966
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2416789599 / 1000000000000 : ℝ)
  frameLo := (318213036389 / 500000000000 : ℝ)
  frameHi := (91950440177 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11966]
  agentFrame_pos := by norm_num only [agent11966]
  worldRadius := (2416789599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11966]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (121033929 / 100000000000 : ℝ)
  lowerTail := (776417701 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7654876239 / 1000000000000 : ℝ)
  ledger := by
    have h : (301859177 / 250000000000 : ℚ) +
        (11009992401 / 1000000000000000000 : ℚ) / (2416789599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (121033929 / 100000000000 : ℚ) + (776417701 / 500000000000 : ℚ) ≤
        (7654876239 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((301859177 / 250000000000 : ℚ) +
        (11009992401 / 1000000000000000000 : ℚ) / (2416789599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (121033929 / 100000000000 : ℚ) + (776417701 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7654876239 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11966]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11966 :
    2 * 160 < 11966 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999331 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11966 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11967 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11967. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11967 : WorldParameters where
  hiddenCharge := (1207383433 / 1000000000000 : ℝ)
  frame := (636410433029 / 1000000000000 : ℝ)
  moment := (11007581899 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11967 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91947627143 / 62500000000 : ℝ)
    root := (7229687561 / 1000000000000 : ℝ) }

noncomputable def scalar11967 : ScalarCertificate 11967 world11967 agent11967 where
  dimensionLo := 11967
  dimensionHi := 11967
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2417204699 / 1000000000000 : ℝ)
  frameLo := (636410433029 / 1000000000000 : ℝ)
  frameHi := (91947627143 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11967]
  agentFrame_pos := by norm_num only [agent11967]
  worldRadius := (2417204699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11967]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1209255097 / 1000000000000 : ℝ)
  lowerTail := (12121471 / 7812500000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7651391677 / 1000000000000 : ℝ)
  ledger := by
    have h : (1207383433 / 1000000000000 : ℚ) +
        (11007581899 / 1000000000000000000 : ℚ) / (2417204699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1209255097 / 1000000000000 : ℚ) + (12121471 / 7812500000 : ℚ) ≤
        (7651391677 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1207383433 / 1000000000000 : ℚ) +
        (11007581899 / 1000000000000000000 : ℚ) / (2417204699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1209255097 / 1000000000000 : ℚ) + (12121471 / 7812500000 : ℚ) : ℚ) : ℝ) ≤
        ((7651391677 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11967]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11967 :
    2 * 160 < 11967 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999571 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11967 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11968 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11968. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11968 : WorldParameters where
  hiddenCharge := (1207330173 / 1000000000000 : ℝ)
  frame := (318197397989 / 500000000000 : ℝ)
  moment := (1375646517 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11968 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471116960397 / 1000000000000 : ℝ)
    root := (7229023549 / 1000000000000 : ℝ) }

noncomputable def scalar11968 : ScalarCertificate 11968 world11968 agent11968 where
  dimensionLo := 11968
  dimensionHi := 11968
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2417619799 / 1000000000000 : ℝ)
  frameLo := (318197397989 / 500000000000 : ℝ)
  frameHi := (1471116960397 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11968]
  agentFrame_pos := by norm_num only [agent11968]
  worldRadius := (2417619799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11968]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1208171709 / 1000000000000 : ℝ)
  lowerTail := (1550262001 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3823954753 / 500000000000 : ℝ)
  ledger := by
    have h : (1207330173 / 1000000000000 : ℚ) +
        (1375646517 / 125000000000000000 : ℚ) / (2417619799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1208171709 / 1000000000000 : ℚ) + (1550262001 / 1000000000000 : ℚ) ≤
        (3823954753 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1207330173 / 1000000000000 : ℚ) +
        (1375646517 / 125000000000000000 : ℚ) / (2417619799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1208171709 / 1000000000000 : ℚ) + (1550262001 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3823954753 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11968]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11968 :
    2 * 160 < 11968 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999553 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11968 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11969 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11969. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11969 : WorldParameters where
  hiddenCharge := (9431851 / 7812500000 : ℝ)
  frame := (5091033293 / 8000000000 : ℝ)
  moment := (11002763109 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11969 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471071916357 / 1000000000000 : ℝ)
    root := (903544971 / 125000000000 : ℝ) }

noncomputable def scalar11969 : ScalarCertificate 11969 world11969 agent11969 where
  dimensionLo := 11969
  dimensionHi := 11969
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2418034899 / 1000000000000 : ℝ)
  frameLo := (5091033293 / 8000000000 : ℝ)
  frameHi := (1471071916357 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11969]
  agentFrame_pos := by norm_num only [agent11969]
  worldRadius := (2418034899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11969]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (603544743 / 500000000000 : ℝ)
  lowerTail := (1548977019 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7644430561 / 1000000000000 : ℝ)
  ledger := by
    have h : (9431851 / 7812500000 : ℚ) +
        (11002763109 / 1000000000000000000 : ℚ) / (2418034899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (603544743 / 500000000000 : ℚ) + (1548977019 / 1000000000000 : ℚ) ≤
        (7644430561 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((9431851 / 7812500000 : ℚ) +
        (11002763109 / 1000000000000000000 : ℚ) / (2418034899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (603544743 / 500000000000 : ℚ) + (1548977019 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7644430561 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11969]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11969 :
    2 * 160 < 11969 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996571 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11969 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11970 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11970. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11970 : WorldParameters where
  hiddenCharge := (603611849 / 500000000000 : ℝ)
  frame := (39772720623 / 62500000000 : ℝ)
  moment := (5500177409 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11970 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294205378051 / 200000000000 : ℝ)
    root := (3613848109 / 500000000000 : ℝ) }

noncomputable def scalar11970 : ScalarCertificate 11970 world11970 agent11970 where
  dimensionLo := 11970
  dimensionHi := 11970
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2418450099 / 1000000000000 : ℝ)
  frameLo := (39772720623 / 62500000000 : ℝ)
  frameHi := (294205378051 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11970]
  agentFrame_pos := by norm_num only [agent11970]
  worldRadius := (2418450099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11970]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1206008451 / 1000000000000 : ℝ)
  lowerTail := (386923341 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7640954733 / 1000000000000 : ℝ)
  ledger := by
    have h : (603611849 / 500000000000 : ℚ) +
        (5500177409 / 500000000000000000 : ℚ) / (2418450099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1206008451 / 1000000000000 : ℚ) + (386923341 / 250000000000 : ℚ) ≤
        (7640954733 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((603611849 / 500000000000 : ℚ) +
        (5500177409 / 500000000000000000 : ℚ) / (2418450099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1206008451 / 1000000000000 : ℚ) + (386923341 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7640954733 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11970]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11970 :
    2 * 160 < 11970 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999307 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11970 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11971 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11971. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11971 : WorldParameters where
  hiddenCharge := (1207170483 / 1000000000000 : ℝ)
  frame := (318173950503 / 500000000000 : ℝ)
  moment := (85921463 / 7812500000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11971 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183872736747 / 125000000000 : ℝ)
    root := (7227032897 / 1000000000000 : ℝ) }

noncomputable def scalar11971 : ScalarCertificate 11971 world11971 agent11971 where
  dimensionLo := 11971
  dimensionHi := 11971
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2418865099 / 1000000000000 : ℝ)
  frameLo := (318173950503 / 500000000000 : ℝ)
  frameHi := (183872736747 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11971]
  agentFrame_pos := by norm_num only [agent11971]
  worldRadius := (2418865099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11971]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (240985687 / 200000000000 : ℝ)
  lowerTail := (773205421 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7637482123 / 1000000000000 : ℝ)
  ledger := by
    have h : (1207170483 / 1000000000000 : ℚ) +
        (85921463 / 7812500000000000 : ℚ) / (2418865099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240985687 / 200000000000 : ℚ) + (773205421 / 500000000000 : ℚ) ≤
        (7637482123 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1207170483 / 1000000000000 : ℚ) +
        (85921463 / 7812500000000000 : ℚ) / (2418865099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240985687 / 200000000000 : ℚ) + (773205421 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7637482123 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11971]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11971 :
    2 * 160 < 11971 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999501 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11971 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11972 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11972. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11972 : WorldParameters where
  hiddenCharge := (301779321 / 250000000000 : ℝ)
  frame := (31816613737 / 50000000000 : ℝ)
  moment := (5497770223 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11972 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183867114451 / 125000000000 : ℝ)
    root := (7226369807 / 1000000000000 : ℝ) }

noncomputable def scalar11972 : ScalarCertificate 11972 world11972 agent11972 where
  dimensionLo := 11972
  dimensionHi := 11972
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2419280299 / 1000000000000 : ℝ)
  frameLo := (31816613737 / 50000000000 : ℝ)
  frameHi := (183867114451 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11972]
  agentFrame_pos := by norm_num only [agent11972]
  worldRadius := (2419280299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11972]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (300962419 / 250000000000 : ℝ)
  lowerTail := (6035663 / 3906250000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (61072101 / 8000000000 : ℝ)
  ledger := by
    have h : (301779321 / 250000000000 : ℚ) +
        (5497770223 / 500000000000000000 : ℚ) / (2419280299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (300962419 / 250000000000 : ℚ) + (6035663 / 3906250000 : ℚ) ≤
        (61072101 / 8000000000 : ℚ) := by norm_num only
    have hc : (((301779321 / 250000000000 : ℚ) +
        (5497770223 / 500000000000000000 : ℚ) / (2419280299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (300962419 / 250000000000 : ℚ) + (6035663 / 3906250000 : ℚ) : ℚ) : ℝ) ≤
        ((61072101 / 8000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11972]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11972 :
    2 * 160 < 11972 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998369 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11972 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11973 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11973. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11973 : WorldParameters where
  hiddenCharge := (1207064099 / 1000000000000 : ℝ)
  frame := (636316651167 / 1000000000000 : ℝ)
  moment := (2748283591 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11973 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470891967037 / 1000000000000 : ℝ)
    root := (1806426717 / 250000000000 : ℝ) }

noncomputable def scalar11973 : ScalarCertificate 11973 world11973 agent11973 where
  dimensionLo := 11973
  dimensionHi := 11973
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2419695499 / 1000000000000 : ℝ)
  frameLo := (636316651167 / 1000000000000 : ℝ)
  frameHi := (1470891967037 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11973]
  agentFrame_pos := by norm_num only [agent11973]
  worldRadius := (2419695499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11973]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (60138601 / 50000000000 : ℝ)
  lowerTail := (1543849853 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7630546221 / 1000000000000 : ℝ)
  ledger := by
    have h : (1207064099 / 1000000000000 : ℚ) +
        (2748283591 / 250000000000000000 : ℚ) / (2419695499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (60138601 / 50000000000 : ℚ) + (1543849853 / 1000000000000 : ℚ) ≤
        (7630546221 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1207064099 / 1000000000000 : ℚ) +
        (2748283591 / 250000000000000000 : ℚ) / (2419695499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (60138601 / 50000000000 : ℚ) + (1543849853 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7630546221 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11973]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11973 :
    2 * 160 < 11973 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998657 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11973 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11974 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11974. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11974 : WorldParameters where
  hiddenCharge := (1207010929 / 1000000000000 : ℝ)
  frame := (39768814393 / 62500000000 : ℝ)
  moment := (10990729017 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11974 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29416940727 / 20000000000 : ℝ)
    root := (7225044237 / 1000000000000 : ℝ) }

noncomputable def scalar11974 : ScalarCertificate 11974 world11974 agent11974 where
  dimensionLo := 11974
  dimensionHi := 11974
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2420110599 / 1000000000000 : ℝ)
  frameLo := (39768814393 / 62500000000 : ℝ)
  frameHi := (29416940727 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11974]
  agentFrame_pos := by norm_num only [agent11974]
  worldRadius := (2420110599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11974]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (60084773 / 50000000000 : ℝ)
  lowerTail := (1542571191 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7627083037 / 1000000000000 : ℝ)
  ledger := by
    have h : (1207010929 / 1000000000000 : ℚ) +
        (10990729017 / 1000000000000000000 : ℚ) / (2420110599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (60084773 / 50000000000 : ℚ) + (1542571191 / 1000000000000 : ℚ) ≤
        (7627083037 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1207010929 / 1000000000000 : ℚ) +
        (10990729017 / 1000000000000000000 : ℚ) / (2420110599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (60084773 / 50000000000 : ℚ) + (1542571191 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7627083037 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11974]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11974 :
    2 * 160 < 11974 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996487 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11974 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11975 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11975. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11975 : WorldParameters where
  hiddenCharge := (603478887 / 500000000000 : ℝ)
  frame := (318142706051 / 500000000000 : ℝ)
  moment := (5494162203 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11975 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367700532371 / 250000000000 : ℝ)
    root := (1806095459 / 250000000000 : ℝ) }

noncomputable def scalar11975 : ScalarCertificate 11975 world11975 agent11975 where
  dimensionLo := 11975
  dimensionHi := 11975
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2420525699 / 1000000000000 : ℝ)
  frameLo := (318142706051 / 500000000000 : ℝ)
  frameHi := (367700532371 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11975]
  agentFrame_pos := by norm_num only [agent11975]
  worldRadius := (2420525699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11975]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (600310017 / 500000000000 : ℝ)
  lowerTail := (770646897 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1524724601 / 200000000000 : ℝ)
  ledger := by
    have h : (603478887 / 500000000000 : ℚ) +
        (5494162203 / 500000000000000000 : ℚ) / (2420525699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (600310017 / 500000000000 : ℚ) + (770646897 / 500000000000 : ℚ) ≤
        (1524724601 / 200000000000 : ℚ) := by norm_num only
    have hc : (((603478887 / 500000000000 : ℚ) +
        (5494162203 / 500000000000000000 : ℚ) / (2420525699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (600310017 / 500000000000 : ℚ) + (770646897 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1524724601 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11975]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11975 :
    2 * 160 < 11975 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998051 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11975 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11976 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11976. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11976 : WorldParameters where
  hiddenCharge := (603452317 / 500000000000 : ℝ)
  frame := (2485428893 / 3906250000 : ℝ)
  moment := (10985920529 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11976 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183844655803 / 125000000000 : ℝ)
    root := (451482479 / 62500000000 : ℝ) }

noncomputable def scalar11976 : ScalarCertificate 11976 world11976 agent11976 where
  dimensionLo := 11976
  dimensionHi := 11976
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2420940699 / 1000000000000 : ℝ)
  frameLo := (2485428893 / 3906250000 : ℝ)
  frameHi := (183844655803 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11976]
  agentFrame_pos := by norm_num only [agent11976]
  worldRadius := (2420940699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11976]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (299886417 / 250000000000 : ℝ)
  lowerTail := (770008789 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7620166123 / 1000000000000 : ℝ)
  ledger := by
    have h : (603452317 / 500000000000 : ℚ) +
        (10985920529 / 1000000000000000000 : ℚ) / (2420940699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (299886417 / 250000000000 : ℚ) + (770008789 / 500000000000 : ℚ) ≤
        (7620166123 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((603452317 / 500000000000 : ℚ) +
        (10985920529 / 1000000000000000000 : ℚ) / (2420940699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (299886417 / 250000000000 : ℚ) + (770008789 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7620166123 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11976]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11976 :
    2 * 160 < 11976 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999287 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11976 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11977 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11977. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11977 : WorldParameters where
  hiddenCharge := (1206851509 / 1000000000000 : ℝ)
  frame := (127250836761 / 200000000000 : ℝ)
  moment := (10983517387 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11977 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470712393107 / 1000000000000 : ℝ)
    root := (3611528861 / 500000000000 : ℝ) }

noncomputable def scalar11977 : ScalarCertificate 11977 world11977 agent11977 where
  dimensionLo := 11977
  dimensionHi := 11977
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2421355899 / 1000000000000 : ℝ)
  frameLo := (127250836761 / 200000000000 : ℝ)
  frameHi := (1470712393107 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11977]
  agentFrame_pos := by norm_num only [agent11977]
  worldRadius := (2421355899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11977]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1198472597 / 1000000000000 : ℝ)
  lowerTail := (1538742821 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7616712437 / 1000000000000 : ℝ)
  ledger := by
    have h : (1206851509 / 1000000000000 : ℚ) +
        (10983517387 / 1000000000000000000 : ℚ) / (2421355899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1198472597 / 1000000000000 : ℚ) + (1538742821 / 1000000000000 : ℚ) ≤
        (7616712437 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1206851509 / 1000000000000 : ℚ) +
        (10983517387 / 1000000000000000000 : ℚ) / (2421355899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1198472597 / 1000000000000 : ℚ) + (1538742821 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7616712437 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11977]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11977 :
    2 * 160 < 11977 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999429 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11977 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11978 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11978. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11978 : WorldParameters where
  hiddenCharge := (603399199 / 500000000000 : ℝ)
  frame := (636238573693 / 1000000000000 : ℝ)
  moment := (549055749 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11978 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470667557621 / 1000000000000 : ℝ)
    root := (7222396009 / 1000000000000 : ℝ) }

noncomputable def scalar11978 : ScalarCertificate 11978 world11978 agent11978 where
  dimensionLo := 11978
  dimensionHi := 11978
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2421770999 / 1000000000000 : ℝ)
  frameLo := (636238573693 / 1000000000000 : ℝ)
  frameHi := (1470667557621 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11978]
  agentFrame_pos := by norm_num only [agent11978]
  worldRadius := (2421770999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11978]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1197400561 / 1000000000000 : ℝ)
  lowerTail := (1537469213 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (95165773 / 12500000000 : ℝ)
  ledger := by
    have h : (603399199 / 500000000000 : ℚ) +
        (549055749 / 50000000000000000 : ℚ) / (2421770999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1197400561 / 1000000000000 : ℚ) + (1537469213 / 1000000000000 : ℚ) ≤
        (95165773 / 12500000000 : ℚ) := by norm_num only
    have hc : (((603399199 / 500000000000 : ℚ) +
        (549055749 / 50000000000000000 : ℚ) / (2421770999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1197400561 / 1000000000000 : ℚ) + (1537469213 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((95165773 / 12500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11978]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11978 :
    2 * 160 < 11978 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994777 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11978 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11979 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11979. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11979 : WorldParameters where
  hiddenCharge := (1206745303 / 1000000000000 : ℝ)
  frame := (63622296627 / 100000000000 : ℝ)
  moment := (5489356653 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11979 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470622745903 / 1000000000000 : ℝ)
    root := (1805433631 / 250000000000 : ℝ) }

noncomputable def scalar11979 : ScalarCertificate 11979 world11979 agent11979 where
  dimensionLo := 11979
  dimensionHi := 11979
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2422186099 / 1000000000000 : ℝ)
  frameLo := (63622296627 / 100000000000 : ℝ)
  frameHi := (1470622745903 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11979]
  agentFrame_pos := by norm_num only [agent11979]
  worldRadius := (2422186099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11979]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (598164827 / 500000000000 : ℝ)
  lowerTail := (6000769 / 3906250000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7609814383 / 1000000000000 : ℝ)
  ledger := by
    have h : (1206745303 / 1000000000000 : ℚ) +
        (5489356653 / 500000000000000000 : ℚ) / (2422186099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (598164827 / 500000000000 : ℚ) + (6000769 / 3906250000 : ℚ) ≤
        (7609814383 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1206745303 / 1000000000000 : ℚ) +
        (5489356653 / 500000000000000000 : ℚ) / (2422186099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (598164827 / 500000000000 : ℚ) + (6000769 / 3906250000 : ℚ) : ℚ) : ℝ) ≤
        ((7609814383 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11979]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11979 :
    2 * 160 < 11979 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998711 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11979 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11980 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11980. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11980 : WorldParameters where
  hiddenCharge := (1206692223 / 1000000000000 : ℝ)
  frame := (1242592503 / 1953125000 : ℝ)
  moment := (5488156183 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11980 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470577957939 / 1000000000000 : ℝ)
    root := (722107319 / 100000000000 : ℝ) }

noncomputable def scalar11980 : ScalarCertificate 11980 world11980 agent11980 where
  dimensionLo := 11980
  dimensionHi := 11980
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2422601299 / 1000000000000 : ℝ)
  frameLo := (1242592503 / 1953125000 : ℝ)
  frameHi := (1470577957939 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11980]
  agentFrame_pos := by norm_num only [agent11980]
  worldRadius := (2422601299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11980]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (74703743 / 62500000000 : ℝ)
  lowerTail := (1534925797 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1521273989 / 200000000000 : ℝ)
  ledger := by
    have h : (1206692223 / 1000000000000 : ℚ) +
        (5488156183 / 500000000000000000 : ℚ) / (2422601299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74703743 / 62500000000 : ℚ) + (1534925797 / 1000000000000 : ℚ) ≤
        (1521273989 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1206692223 / 1000000000000 : ℚ) +
        (5488156183 / 500000000000000000 : ℚ) / (2422601299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74703743 / 62500000000 : ℚ) + (1534925797 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1521273989 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11980]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11980 :
    2 * 160 < 11980 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994461 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11980 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11981 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11981. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11981 : WorldParameters where
  hiddenCharge := (603319579 / 500000000000 : ℝ)
  frame := (636191759491 / 1000000000000 : ℝ)
  moment := (68586951 / 6250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11981 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183816648471 / 125000000000 : ℝ)
    root := (7220412163 / 1000000000000 : ℝ) }

noncomputable def scalar11981 : ScalarCertificate 11981 world11981 agent11981 where
  dimensionLo := 11981
  dimensionHi := 11981
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2423016399 / 1000000000000 : ℝ)
  frameLo := (636191759491 / 1000000000000 : ℝ)
  frameHi := (183816648471 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11981]
  agentFrame_pos := by norm_num only [agent11981]
  worldRadius := (2423016399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11981]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1194191209 / 1000000000000 : ℝ)
  lowerTail := (766827967 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7602928703 / 1000000000000 : ℝ)
  ledger := by
    have h : (603319579 / 500000000000 : ℚ) +
        (68586951 / 6250000000000000 : ℚ) / (2423016399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1194191209 / 1000000000000 : ℚ) + (766827967 / 500000000000 : ℚ) ≤
        (7602928703 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((603319579 / 500000000000 : ℚ) +
        (68586951 / 6250000000000000 : ℚ) / (2423016399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1194191209 / 1000000000000 : ℚ) + (766827967 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7602928703 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11981]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11981 :
    2 * 160 < 11981 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999481 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11981 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11982 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11982. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11982 : WorldParameters where
  hiddenCharge := (1206586107 / 1000000000000 : ℝ)
  frame := (636176160133 / 1000000000000 : ℝ)
  moment := (5485756343 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11982 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470488447271 / 1000000000000 : ℝ)
    root := (1443950273 / 200000000000 : ℝ) }

noncomputable def scalar11982 : ScalarCertificate 11982 world11982 agent11982 where
  dimensionLo := 11982
  dimensionHi := 11982
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2423431499 / 1000000000000 : ℝ)
  frameLo := (636176160133 / 1000000000000 : ℝ)
  frameHi := (1470488447271 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11982]
  agentFrame_pos := by norm_num only [agent11982]
  worldRadius := (2423431499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11982]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (298280919 / 250000000000 : ℝ)
  lowerTail := (383096839 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (94993633 / 12500000000 : ℝ)
  ledger := by
    have h : (1206586107 / 1000000000000 : ℚ) +
        (5485756343 / 500000000000000000 : ℚ) / (2423431499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (298280919 / 250000000000 : ℚ) + (383096839 / 250000000000 : ℚ) ≤
        (94993633 / 12500000000 : ℚ) := by norm_num only
    have hc : (((1206586107 / 1000000000000 : ℚ) +
        (5485756343 / 500000000000000000 : ℚ) / (2423431499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (298280919 / 250000000000 : ℚ) + (383096839 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((94993633 / 12500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11982]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11982 :
    2 * 160 < 11982 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998107 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11982 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11983 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11983. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11983 : WorldParameters where
  hiddenCharge := (75408317 / 62500000000 : ℝ)
  frame := (318080281731 / 500000000000 : ℝ)
  moment := (5484556973 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11983 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470443730489 / 1000000000000 : ℝ)
    root := (1443818159 / 200000000000 : ℝ) }

noncomputable def scalar11983 : ScalarCertificate 11983 world11983 agent11983 where
  dimensionLo := 11983
  dimensionHi := 11983
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2423846599 / 1000000000000 : ℝ)
  frameLo := (318080281731 / 500000000000 : ℝ)
  frameHi := (1470443730489 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11983]
  agentFrame_pos := by norm_num only [agent11983]
  worldRadius := (2423846599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11983]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (238411453 / 200000000000 : ℝ)
  lowerTail := (47847501 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7596055701 / 1000000000000 : ℝ)
  ledger := by
    have h : (75408317 / 62500000000 : ℚ) +
        (5484556973 / 500000000000000000 : ℚ) / (2423846599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (238411453 / 200000000000 : ℚ) + (47847501 / 31250000000 : ℚ) ≤
        (7596055701 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((75408317 / 62500000000 : ℚ) +
        (5484556973 / 500000000000000000 : ℚ) / (2423846599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (238411453 / 200000000000 : ℚ) + (47847501 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((7596055701 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11983]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11983 :
    2 * 160 < 11983 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999619 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11983 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding11959 :
    (120781005144273524761 / 100000000000000000000000 : ℝ) ≤ world11959.hiddenCharge ∧
    (159133906655397276248269 / 250000000000000000000000 : ℝ) ≤ world11959.frame ∧
    (441075463 / 40000000000000000 : ℝ) ≤ world11959.moment ∧
    (1471520898105035204921451 / 1000000000000000000000000 : ℝ) ≤ agent11959.frame ∧
    (7235008048362462268263 / 1000000000000000000000000 : ℝ) ≤ agent11959.root ∧
    scalar11959.worldRadius ≤ (2413887599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (253393835855724059339 / 200000000000000000000000 : ℝ) ≤ agent11959.charge ∧
    (76122270838600596237 / 62500000000000000000000 : ℝ) ≤ scalar11959.upperTail ∧
    (195234346970747746943 / 125000000000000000000000 : ℝ) ≤ scalar11959.lowerTail ∧
    scalar11959.totalBudget ≤ (7679340912586449131841 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11959, agent11959, scalar11959] <;> simp only [true_and]

theorem source_rounding11960 :
    (603878335727381799801 / 500000000000000000000000 : ℝ) ≤ world11960.hiddenCharge ∧
    (318259983983394774208919 / 500000000000000000000000 : ℝ) ≤ world11960.frame ∧
    (2204894181 / 200000000000000000 : ℝ) ≤ world11960.moment ∧
    (1471475995723924921663049 / 1000000000000000000000000 : ℝ) ≤ agent11960.frame ∧
    (3617171093555913847241 / 500000000000000000000000 : ℝ) ≤ agent11960.root ∧
    scalar11960.worldRadius ≤ (2414302099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (31667546702163107899 / 25000000000000000000000 : ℝ) ≤ agent11960.charge ∧
    (608432358526992960329 / 500000000000000000000000 : ℝ) ≤ scalar11960.upperTail ∧
    (1560579569072890443999 / 1000000000000000000000000 : ℝ) ≤ scalar11960.lowerTail ∧
    scalar11960.totalBudget ≤ (19189591139726545261 / 2500000000000000000000 : ℝ) := by
  norm_num only [world11960, agent11960, scalar11960] <;> simp only [true_and]

theorem source_rounding11961 :
    (603851653252888841063 / 500000000000000000000000 : ℝ) ≤ world11961.hiddenCharge ∧
    (318252156007547971748347 / 500000000000000000000000 : ℝ) ≤ world11961.frame ∧
    (5511027987 / 500000000000000000 : ℝ) ≤ world11961.moment ∧
    (29428622227362694445713 / 20000000000000000000000 : ℝ) ≤ agent11961.frame ∧
    (1446735311526103327167 / 200000000000000000000000 : ℝ) ≤ agent11961.root ∧
    scalar11961.worldRadius ≤ (2414716699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (253286964353951279443 / 200000000000000000000000 : ℝ) ≤ agent11961.charge ∧
    (1215774301081928398729 / 1000000000000000000000000 : ℝ) ≤ scalar11961.upperTail ∧
    (1559285701524503697321 / 1000000000000000000000000 : ℝ) ≤ scalar11961.lowerTail ∧
    scalar11961.totalBudget ≤ (7672335143988653812161 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11961, agent11961, scalar11961] <;> simp only [true_and]

theorem source_rounding11962 :
    (1207649956590234397191 / 1000000000000000000000000 : ℝ) ≤ world11962.hiddenCharge ∧
    (636488658765764832751023 / 1000000000000000000000000 : ℝ) ≤ world11962.frame ∧
    (11019641783 / 1000000000000000000 : ℝ) ≤ world11962.moment ∧
    (1471386250976651733559989 / 1000000000000000000000000 : ℝ) ≤ agent11962.frame ∧
    (3616505540435092925543 / 500000000000000000000000 : ℝ) ≤ agent11962.root ∧
    scalar11962.worldRadius ≤ (2415131399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1266168040031350825751 / 1000000000000000000000000 : ℝ) ≤ agent11962.charge ∧
    (242937010138302718531 / 200000000000000000000000 : ℝ) ≤ scalar11962.upperTail ∧
    (1557993141018904211671 / 1000000000000000000000000 : ℝ) ≤ scalar11962.lowerTail ∧
    scalar11962.totalBudget ≤ (7668836908724076621389 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11962, agent11962, scalar11962] <;> simp only [true_and]

theorem source_rounding11963 :
    (603798310851295896159 / 500000000000000000000000 : ℝ) ≤ world11963.hiddenCharge ∧
    (636473008218052858465399 / 1000000000000000000000000 : ℝ) ≤ world11963.frame ∧
    (1101722833 / 100000000000000000 : ℝ) ≤ world11963.moment ∧
    (1471341414535910293012061 / 1000000000000000000000000 : ℝ) ≤ agent11963.frame ∧
    (7232345914472561104817 / 1000000000000000000000000 : ℝ) ≤ agent11963.root ∧
    scalar11963.worldRadius ≤ (2415545899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1265901522574715183089 / 1000000000000000000000000 : ℝ) ≤ agent11963.charge ∧
    (121359686103035487479 / 100000000000000000000000 : ℝ) ≤ scalar11963.upperTail ∧
    (311340350589975017861 / 200000000000000000000000 : ℝ) ≤ scalar11963.lowerTail ∧
    scalar11963.totalBudget ≤ (1533068395680399099083 / 200000000000000000000000 : ℝ) := by
  norm_num only [world11963, agent11963, scalar11963] <;> simp only [true_and]

theorem source_rounding11964 :
    (1207543301837311992359 / 1000000000000000000000000 : ℝ) ≤ world11964.hiddenCharge ∧
    (318228680185608551926733 / 500000000000000000000000 : ℝ) ≤ world11964.frame ∧
    (86053247 / 7812500000000000 : ℝ) ≤ world11964.moment ∧
    (1471296602032361472362367 / 1000000000000000000000000 : ℝ) ≤ agent11964.frame ∧
    (7231680979372936039033 / 1000000000000000000000000 : ℝ) ≤ agent11964.root ∧
    scalar11964.worldRadius ≤ (2415960499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (632817634551814911171 / 500000000000000000000000 : ℝ) ≤ agent11964.charge ∧
    (242501978000591912519 / 200000000000000000000000 : ℝ) ≤ scalar11964.upperTail ∧
    (1555411729416352821973 / 1000000000000000000000000 : ℝ) ≤ scalar11964.lowerTail ∧
    scalar11964.totalBudget ≤ (3830925117699920205349 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11964, agent11964, scalar11964] <;> simp only [true_and]

theorem source_rounding11965 :
    (603744998494429865067 / 500000000000000000000000 : ℝ) ≤ world11965.hiddenCharge ∧
    (3182208576122573596077 / 5000000000000000000000 : ℝ) ≤ world11965.frame ∧
    (11012403639 / 1000000000000000000 : ℝ) ≤ world11965.moment ∧
    (735625903750735792502677 / 500000000000000000000000 : ℝ) ≤ agent11965.frame ∧
    (7231016275414551651703 / 1000000000000000000000000 : ℝ) ≤ agent11965.root ∧
    scalar11965.worldRadius ≤ (2416375099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (632684639661123672201 / 500000000000000000000000 : ℝ) ≤ agent11965.charge ∧
    (302856010489136390233 / 250000000000000000000000 : ℝ) ≤ scalar11965.upperTail ∧
    (1554122954339521295107 / 1000000000000000000000000 : ℝ) ≤ scalar11965.lowerTail ∧
    scalar11965.totalBudget ≤ (3829180810915723969181 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11965, agent11965, scalar11965] <;> simp only [true_and]

theorem source_rounding11966 :
    (301859176787924488601 / 250000000000000000000000 : ℝ) ≤ world11966.hiddenCharge ∧
    (127285214555440667340127 / 200000000000000000000000 : ℝ) ≤ world11966.frame ∧
    (11009992401 / 1000000000000000000 : ℝ) ≤ world11966.moment ∧
    (367801760707997214385297 / 250000000000000000000000 : ℝ) ≤ agent11966.frame ∧
    (7230351802440822048019 / 1000000000000000000000000 : ℝ) ≤ agent11966.root ∧
    scalar11966.worldRadius ≤ (2416789599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (316275888233773018739 / 250000000000000000000000 : ℝ) ≤ agent11966.charge ∧
    (1210339289021038158333 / 1000000000000000000000000 : ℝ) ≤ scalar11966.upperTail ∧
    (155283540159326766437 / 100000000000000000000000 : ℝ) ≤ scalar11966.lowerTail ∧
    scalar11966.totalBudget ≤ (7654876239459054965857 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11966, agent11966, scalar11966] <;> simp only [true_and]

theorem source_rounding11967 :
    (241476686464059908229 / 200000000000000000000000 : ℝ) ≤ world11967.hiddenCharge ∧
    (318205216514270405224729 / 500000000000000000000000 : ℝ) ≤ world11967.frame ∧
    (11007581899 / 1000000000000000000 : ℝ) ≤ world11967.moment ∧
    (1471162034287602085005251 / 1000000000000000000000000 : ℝ) ≤ agent11967.frame ∧
    (1445937512059066840603 / 200000000000000000000000 : ℝ) ≤ agent11967.root ∧
    scalar11967.worldRadius ≤ (2417204699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (632419044823529771151 / 500000000000000000000000 : ℝ) ≤ agent11967.charge ∧
    (1209255096121691057857 / 1000000000000000000000000 : ℝ) ≤ scalar11967.upperTail ∧
    (48485883978804039041 / 31250000000000000000000 : ℝ) ≤ scalar11967.lowerTail ∧
    scalar11967.totalBudget ≤ (1912847919296180505061 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11967, agent11967, scalar11967] <;> simp only [true_and]

theorem source_rounding11968 :
    (150916271561141764453 / 125000000000000000000000 : ℝ) ≤ world11968.hiddenCharge ∧
    (159098698994446299334843 / 250000000000000000000000 : ℝ) ≤ world11968.frame ∧
    (1375646517 / 125000000000000000 : ℝ) ≤ world11968.moment ∧
    (1471116960396701455157791 / 1000000000000000000000000 : ℝ) ≤ agent11968.frame ∧
    (90362794360273096557 / 12500000000000000000000 : ℝ) ≤ agent11968.root ∧
    scalar11968.worldRadius ≤ (2417619799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1264572889163415955997 / 1000000000000000000000000 : ℝ) ≤ agent11968.charge ∧
    (1208171708629464211807 / 1000000000000000000000000 : ℝ) ≤ scalar11968.upperTail ∧
    (1550262000797712591451 / 1000000000000000000000000 : ℝ) ≤ scalar11968.lowerTail ∧
    scalar11968.totalBudget ≤ (7647909506449148968679 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11968, agent11968, scalar11968] <;> simp only [true_and]

theorem source_rounding11969 :
    (6036384638263376859 / 5000000000000000000000 : ℝ) ≤ world11969.hiddenCharge ∧
    (636379161624194981940903 / 1000000000000000000000000 : ℝ) ≤ world11969.frame ∧
    (11002763109 / 1000000000000000000 : ℝ) ≤ world11969.moment ∧
    (735535958178430010594053 / 500000000000000000000000 : ℝ) ≤ agent11969.frame ∧
    (722835976786429461669 / 100000000000000000000000 : ℝ) ≤ agent11969.root ∧
    scalar11969.worldRadius ≤ (2418034899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (316076987797449421581 / 250000000000000000000000 : ℝ) ≤ agent11969.charge ∧
    (603544742520695841331 / 500000000000000000000000 : ℝ) ≤ scalar11969.upperTail ∧
    (774488509249178127647 / 500000000000000000000000 : ℝ) ≤ scalar11969.lowerTail ∧
    scalar11969.totalBudget ≤ (7644430561272553207677 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11969, agent11969, scalar11969] <;> simp only [true_and]

theorem source_rounding11970 :
    (37725740556418783349 / 31250000000000000000000 : ℝ) ≤ world11970.hiddenCharge ∧
    (636363529967028676689119 / 1000000000000000000000000 : ℝ) ≤ world11970.frame ∧
    (5500177409 / 500000000000000000 : ℝ) ≤ world11970.moment ∧
    (367756722563608980207981 / 250000000000000000000000 : ℝ) ≤ agent11970.frame ∧
    (1445539243453355808661 / 200000000000000000000000 : ℝ) ≤ agent11970.root ∧
    scalar11970.worldRadius ≤ (2418450099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (632021637716105372281 / 500000000000000000000000 : ℝ) ≤ agent11970.charge ∧
    (1206008450357678814151 / 1000000000000000000000000 : ℝ) ≤ scalar11970.upperTail ∧
    (1547693363530641343383 / 1000000000000000000000000 : ℝ) ≤ scalar11970.lowerTail ∧
    scalar11970.totalBudget ≤ (7640954733291975260701 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11970, agent11970, scalar11970] <;> simp only [true_and]

theorem source_rounding11971 :
    (1207170482941788637881 / 1000000000000000000000000 : ℝ) ≤ world11971.hiddenCharge ∧
    (31817395050277269891361 / 50000000000000000000000 : ℝ) ≤ world11971.frame ∧
    (85921463 / 7812500000000000 : ℝ) ≤ world11971.moment ∧
    (183872736746951102301199 / 125000000000000000000000 : ℝ) ≤ agent11971.frame ∧
    (7227032896873577092227 / 1000000000000000000000000 : ℝ) ≤ agent11971.root ∧
    scalar11971.worldRadius ≤ (2418865099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1263778861597030264077 / 1000000000000000000000000 : ℝ) ≤ agent11971.charge ∧
    (602464217083746957361 / 500000000000000000000000 : ℝ) ≤ scalar11971.upperTail ∧
    (1546410841346772236671 / 1000000000000000000000000 : ℝ) ≤ scalar11971.lowerTail ∧
    scalar11971.totalBudget ≤ (954685265492628705479 / 125000000000000000000000 : ℝ) := by
  norm_num only [world11971, agent11971, scalar11971] <;> simp only [true_and]

theorem source_rounding11972 :
    (603558641528159790947 / 500000000000000000000000 : ℝ) ≤ world11972.hiddenCharge ∧
    (318166137369502142653889 / 500000000000000000000000 : ℝ) ≤ world11972.frame ∧
    (5497770223 / 500000000000000000 : ℝ) ≤ world11972.moment ∧
    (735468457803911182434193 / 500000000000000000000000 : ℝ) ≤ agent11972.frame ∧
    (3613184903264568269801 / 500000000000000000000000 : ℝ) ≤ agent11972.root ∧
    scalar11972.worldRadius ≤ (2419280299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (78969669336937498889 / 62500000000000000000000 : ℝ) ≤ agent11972.charge ∧
    (150481209415815674903 / 125000000000000000000000 : ℝ) ≤ scalar11972.upperTail ∧
    (1545129727703825981619 / 1000000000000000000000000 : ℝ) ≤ scalar11972.lowerTail ∧
    scalar11972.totalBudget ≤ (95425157820208178113 / 12500000000000000000000 : ℝ) := by
  norm_num only [world11972, agent11972, scalar11972] <;> simp only [true_and]

theorem source_rounding11973 :
    (48282563925739178153 / 40000000000000000000000 : ℝ) ≤ world11973.hiddenCharge ∧
    (318158325583332438372139 / 500000000000000000000000 : ℝ) ≤ world11973.frame ∧
    (2748283591 / 250000000000000000 : ℝ) ≤ world11973.moment ∧
    (147089196703623762850071 / 100000000000000000000000 : ℝ) ≤ agent11973.frame ∧
    (1806426716842641728151 / 250000000000000000000000 : ℝ) ≤ agent11973.root ∧
    scalar11973.worldRadius ≤ (2419695499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1263250818521231723063 / 1000000000000000000000000 : ℝ) ≤ agent11973.charge ∧
    (601386009700155149213 / 500000000000000000000000 : ℝ) ≤ scalar11973.upperTail ∧
    (154384985234748395163 / 100000000000000000000000 : ℝ) ≤ scalar11973.lowerTail ∧
    scalar11973.totalBudget ≤ (1907636555448896798987 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11973, agent11973, scalar11973] <;> simp only [true_and]

theorem source_rounding11974 :
    (150876366024719185811 / 125000000000000000000000 : ℝ) ≤ world11974.hiddenCharge ∧
    (636301030287786935551383 / 1000000000000000000000000 : ℝ) ≤ world11974.frame ∧
    (10990729017 / 1000000000000000000 : ℝ) ≤ world11974.moment ∧
    (735423518174691232400419 / 500000000000000000000000 : ℝ) ≤ agent11974.frame ∧
    (1806261059168579781571 / 250000000000000000000000 : ℝ) ≤ agent11974.root ∧
    scalar11974.worldRadius ≤ (2420110599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (15787339858690061011 / 12500000000000000000000 : ℝ) ≤ agent11974.charge ∧
    (1201695459726959205607 / 1000000000000000000000000 : ℝ) ≤ scalar11974.upperTail ∧
    (1542571190105222284653 / 1000000000000000000000000 : ℝ) ≤ scalar11974.lowerTail ∧
    scalar11974.totalBudget ≤ (7627083037468169402059 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11974, agent11974, scalar11974] <;> simp only [true_and]

theorem source_rounding11975 :
    (1206957773213630967633 / 1000000000000000000000000 : ℝ) ≤ world11975.hiddenCharge ∧
    (636285412101630543577173 / 1000000000000000000000000 : ℝ) ≤ world11975.frame ∧
    (5494162203 / 500000000000000000 : ℝ) ≤ world11975.moment ∧
    (1470802129483025554750283 / 1000000000000000000000000 : ℝ) ≤ agent11975.frame ∧
    (3612190917780599039707 / 500000000000000000000000 : ℝ) ≤ agent11975.root ∧
    scalar11975.worldRadius ≤ (2420525699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (631361909810382952257 / 500000000000000000000000 : ℝ) ≤ agent11975.charge ∧
    (300155008298487849693 / 250000000000000000000000 : ℝ) ≤ scalar11975.upperTail ∧
    (38532344836569398221 / 25000000000000000000000 : ℝ) ≤ scalar11975.lowerTail ∧
    scalar11975.totalBudget ≤ (7623623005794587891629 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11975, agent11975, scalar11975] <;> simp only [true_and]

theorem source_rounding11976 :
    (301726158296401308701 / 250000000000000000000000 : ℝ) ≤ world11976.hiddenCharge ∧
    (318134898303727984081909 / 500000000000000000000000 : ℝ) ≤ world11976.frame ∧
    (10985920529 / 1000000000000000000 : ℝ) ≤ world11976.moment ∧
    (1470757246423789697389289 / 1000000000000000000000000 : ℝ) ≤ agent11976.frame ∧
    (1805929915969083988849 / 250000000000000000000000 : ℝ) ≤ agent11976.root ∧
    scalar11976.worldRadius ≤ (2420940699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1262460711006127782497 / 1000000000000000000000000 : ℝ) ≤ agent11976.charge ∧
    (1199545667453938820949 / 1000000000000000000000000 : ℝ) ≤ scalar11976.upperTail ∧
    (48125549283919504333 / 31250000000000000000000 : ℝ) ≤ scalar11976.lowerTail ∧
    scalar11976.totalBudget ≤ (3810083061504808754003 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11976, agent11976, scalar11976] <;> simp only [true_and]

theorem source_rounding11977 :
    (1206851508108166392013 / 1000000000000000000000000 : ℝ) ≤ world11977.hiddenCharge ∧
    (636254183804523918070803 / 1000000000000000000000000 : ℝ) ≤ world11977.frame ∧
    (10983517387 / 1000000000000000000 : ℝ) ≤ world11977.moment ∧
    (73535619655308242688343 / 50000000000000000000000 : ℝ) ≤ agent11977.frame ∧
    (3611528860732517726649 / 500000000000000000000000 : ℝ) ≤ agent11977.root ∧
    scalar11977.worldRadius ≤ (2421355899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1262197862559869528997 / 1000000000000000000000000 : ℝ) ≤ agent11977.charge ∧
    (1198472596336885979699 / 1000000000000000000000000 : ℝ) ≤ scalar11977.upperTail ∧
    (769371410387245018247 / 500000000000000000000000 : ℝ) ≤ scalar11977.lowerTail ∧
    scalar11977.totalBudget ≤ (7616712437582698185963 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11977, agent11977, scalar11977] <;> simp only [true_and]

theorem source_rounding11978 :
    (4827193591903257667 / 4000000000000000000000 : ℝ) ≤ world11978.hiddenCharge ∧
    (636238573692095246824279 / 1000000000000000000000000 : ℝ) ≤ world11978.frame ∧
    (549055749 / 50000000000000000 : ℝ) ≤ world11978.moment ∧
    (367666889405210866180081 / 250000000000000000000000 : ℝ) ≤ agent11978.frame ∧
    (451399750510798097149 / 62500000000000000000000 : ℝ) ≤ agent11978.root ∧
    scalar11978.worldRadius ≤ (2421770999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (630967636995467835281 / 500000000000000000000000 : ℝ) ≤ agent11978.charge ∧
    (598700280468573947547 / 500000000000000000000000 : ℝ) ≤ scalar11978.upperTail ∧
    (1537469212147719640051 / 1000000000000000000000000 : ℝ) ≤ scalar11978.lowerTail ∧
    scalar11978.totalBudget ≤ (3806630920116479325493 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11978, agent11978, scalar11978] <;> simp only [true_and]

theorem source_rounding11979 :
    (1206745302783047506887 / 1000000000000000000000000 : ℝ) ≤ world11979.hiddenCharge ∧
    (12724459325388622442183 / 20000000000000000000000 : ℝ) ≤ world11979.frame ∧
    (5489356653 / 500000000000000000 : ℝ) ≤ world11979.moment ∧
    (1470622745902610405196913 / 1000000000000000000000000 : ℝ) ≤ agent11979.frame ∧
    (7221734523845181288991 / 1000000000000000000000000 : ℝ) ≤ agent11979.root ∧
    scalar11979.worldRadius ≤ (2422186099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (315418236252158933417 / 250000000000000000000000 : ℝ) ≤ agent11979.charge ∧
    (598164826585348125301 / 500000000000000000000000 : ℝ) ≤ scalar11979.upperTail ∧
    (38404921582142493281 / 25000000000000000000000 : ℝ) ≤ scalar11979.lowerTail ∧
    scalar11979.totalBudget ≤ (304392575339850459073 / 40000000000000000000000 : ℝ) := by
  norm_num only [world11979, agent11979, scalar11979] <;> simp only [true_and]

theorem source_rounding11980 :
    (241338444504872999357 / 200000000000000000000000 : ℝ) ≤ world11980.hiddenCharge ∧
    (636207361535792980845403 / 1000000000000000000000000 : ℝ) ≤ world11980.frame ∧
    (5488156183 / 500000000000000000 : ℝ) ≤ world11980.moment ∧
    (367644489484538555255171 / 250000000000000000000000 : ℝ) ≤ agent11980.frame ∧
    (7221073189737060189711 / 1000000000000000000000000 : ℝ) ≤ agent11980.root ∧
    scalar11980.worldRadius ≤ (2422601299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (126141087532264373307 / 100000000000000000000000 : ℝ) ≤ agent11980.charge ∧
    (119525988753856616253 / 100000000000000000000000 : ℝ) ≤ scalar11980.upperTail ∧
    (95932862306604548099 / 62500000000000000000000 : ℝ) ≤ scalar11980.lowerTail ∧
    scalar11980.totalBudget ≤ (760636994560779526997 / 100000000000000000000000 : ℝ) := by
  norm_num only [world11980, agent11980, scalar11980] <;> simp only [true_and]

theorem source_rounding11981 :
    (1206639157194274623271 / 1000000000000000000000000 : ℝ) ≤ world11981.hiddenCharge ∧
    (318095879745221266903369 / 500000000000000000000000 : ℝ) ≤ world11981.frame ∧
    (68586951 / 6250000000000000 : ℝ) ≤ world11981.moment ∧
    (183816648470921973444553 / 125000000000000000000000 : ℝ) ≤ agent11981.frame ∧
    (3610206081446518014699 / 500000000000000000000000 : ℝ) ≤ agent11981.root ∧
    scalar11981.worldRadius ≤ (2423016399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1261149064642997660949 / 1000000000000000000000000 : ℝ) ≤ agent11981.charge ∧
    (597095604344406575787 / 500000000000000000000000 : ℝ) ≤ scalar11981.upperTail ∧
    (1533655933652198149591 / 1000000000000000000000000 : ℝ) ≤ scalar11981.lowerTail ∧
    scalar11981.totalBudget ≤ (7602928703214749189337 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11981, agent11981, scalar11981] <;> simp only [true_and]

theorem source_rounding11982 :
    (241317221357456178629 / 200000000000000000000000 : ℝ) ≤ world11982.hiddenCharge ∧
    (636176160132641848674243 / 1000000000000000000000000 : ℝ) ≤ world11982.frame ∧
    (5485756343 / 500000000000000000 : ℝ) ≤ world11982.moment ∧
    (735244223635432891263567 / 500000000000000000000000 : ℝ) ≤ agent11982.frame ∧
    (7219751364551630814817 / 1000000000000000000000000 : ℝ) ≤ agent11982.root ∧
    scalar11982.worldRadius ≤ (2423431499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (630443756340049488431 / 500000000000000000000000 : ℝ) ≤ agent11982.charge ∧
    (29828091890387377213 / 25000000000000000000000 : ℝ) ≤ scalar11982.upperTail ∧
    (766193677693475819501 / 500000000000000000000000 : ℝ) ≤ scalar11982.lowerTail ∧
    scalar11982.totalBudget ≤ (1899872660013996048131 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11982, agent11982, scalar11982] <;> simp only [true_and]

theorem source_rounding11983 :
    (301633267824473088179 / 250000000000000000000000 : ℝ) ≤ world11983.hiddenCharge ∧
    (636160563461653134430167 / 1000000000000000000000000 : ℝ) ≤ world11983.frame ∧
    (5484556973 / 500000000000000000 : ℝ) ≤ world11983.moment ∧
    (735221865244148176095621 / 500000000000000000000000 : ℝ) ≤ agent11983.frame ∧
    (7219090794559165451143 / 1000000000000000000000000 : ℝ) ≤ agent11983.root ∧
    scalar11983.worldRadius ≤ (2423846599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (630313109572356049241 / 500000000000000000000000 : ℝ) ≤ agent11983.charge ∧
    (1192057264699724303373 / 1000000000000000000000000 : ℝ) ≤ scalar11983.upperTail ∧
    (765560015541618360151 / 500000000000000000000000 : ℝ) ≤ scalar11983.lowerTail ∧
    scalar11983.totalBudget ≤ (7596055701253856713099 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11983, agent11983, scalar11983] <;> simp only [true_and]

noncomputable def paperAgent11959 : AgentParameters :=
  { agent11959 with charge := (1266969183 / 1000000000000 : ℝ) }

theorem agent_is_repriced11959 : agent11959 =
    BstLean.Part265.agentRepriced 11959 world11959 paperAgent11959 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11959, agent11959]

noncomputable def paperAgent11960 : AgentParameters :=
  { agent11960 with charge := (79168867 / 62500000000 : ℝ) }

theorem agent_is_repriced11960 : agent11960 =
    BstLean.Part265.agentRepriced 11960 world11960 paperAgent11960 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11960, agent11960]

noncomputable def paperAgent11961 : AgentParameters :=
  { agent11961 with charge := (50657393 / 40000000000 : ℝ) }

theorem agent_is_repriced11961 : agent11961 =
    BstLean.Part265.agentRepriced 11961 world11961 paperAgent11961 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11961, agent11961]

noncomputable def paperAgent11962 : AgentParameters :=
  { agent11962 with charge := (1266168043 / 1000000000000 : ℝ) }

theorem agent_is_repriced11962 : agent11962 =
    BstLean.Part265.agentRepriced 11962 world11962 paperAgent11962 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11962, agent11962]

noncomputable def paperAgent11963 : AgentParameters :=
  { agent11963 with charge := (632950763 / 500000000000 : ℝ) }

theorem agent_is_repriced11963 : agent11963 =
    BstLean.Part265.agentRepriced 11963 world11963 paperAgent11963 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11963, agent11963]

noncomputable def paperAgent11964 : AgentParameters :=
  { agent11964 with charge := (158204409 / 125000000000 : ℝ) }

theorem agent_is_repriced11964 : agent11964 =
    BstLean.Part265.agentRepriced 11964 world11964 paperAgent11964 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11964, agent11964]

noncomputable def paperAgent11965 : AgentParameters :=
  { agent11965 with charge := (632684641 / 500000000000 : ℝ) }

theorem agent_is_repriced11965 : agent11965 =
    BstLean.Part265.agentRepriced 11965 world11965 paperAgent11965 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11965, agent11965]

noncomputable def paperAgent11966 : AgentParameters :=
  { agent11966 with charge := (316275889 / 250000000000 : ℝ) }

theorem agent_is_repriced11966 : agent11966 =
    BstLean.Part265.agentRepriced 11966 world11966 paperAgent11966 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11966, agent11966]

noncomputable def paperAgent11967 : AgentParameters :=
  { agent11967 with charge := (1264838093 / 1000000000000 : ℝ) }

theorem agent_is_repriced11967 : agent11967 =
    BstLean.Part265.agentRepriced 11967 world11967 paperAgent11967 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11967, agent11967]

noncomputable def paperAgent11968 : AgentParameters :=
  { agent11968 with charge := (1264572893 / 1000000000000 : ℝ) }

theorem agent_is_repriced11968 : agent11968 =
    BstLean.Part265.agentRepriced 11968 world11968 paperAgent11968 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11968, agent11968]

noncomputable def paperAgent11969 : AgentParameters :=
  { agent11969 with charge := (252861591 / 200000000000 : ℝ) }

theorem agent_is_repriced11969 : agent11969 =
    BstLean.Part265.agentRepriced 11969 world11969 paperAgent11969 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11969, agent11969]

noncomputable def paperAgent11970 : AgentParameters :=
  { agent11970 with charge := (1264043279 / 1000000000000 : ℝ) }

theorem agent_is_repriced11970 : agent11970 =
    BstLean.Part265.agentRepriced 11970 world11970 paperAgent11970 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11970, agent11970]

noncomputable def paperAgent11971 : AgentParameters :=
  { agent11971 with charge := (252755773 / 200000000000 : ℝ) }

theorem agent_is_repriced11971 : agent11971 =
    BstLean.Part265.agentRepriced 11971 world11971 paperAgent11971 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11971, agent11971]

noncomputable def paperAgent11972 : AgentParameters :=
  { agent11972 with charge := (157939339 / 125000000000 : ℝ) }

theorem agent_is_repriced11972 : agent11972 =
    BstLean.Part265.agentRepriced 11972 world11972 paperAgent11972 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11972, agent11972]

noncomputable def paperAgent11973 : AgentParameters :=
  { agent11973 with charge := (631625411 / 500000000000 : ℝ) }

theorem agent_is_repriced11973 : agent11973 =
    BstLean.Part265.agentRepriced 11973 world11973 paperAgent11973 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11973, agent11973]

noncomputable def paperAgent11974 : AgentParameters :=
  { agent11974 with charge := (157873399 / 125000000000 : ℝ) }

theorem agent_is_repriced11974 : agent11974 =
    BstLean.Part265.agentRepriced 11974 world11974 paperAgent11974 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11974, agent11974]

noncomputable def paperAgent11975 : AgentParameters :=
  { agent11975 with charge := (1262723823 / 1000000000000 : ℝ) }

theorem agent_is_repriced11975 : agent11975 =
    BstLean.Part265.agentRepriced 11975 world11975 paperAgent11975 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11975, agent11975]

noncomputable def paperAgent11976 : AgentParameters :=
  { agent11976 with charge := (631230357 / 500000000000 : ℝ) }

theorem agent_is_repriced11976 : agent11976 =
    BstLean.Part265.agentRepriced 11976 world11976 paperAgent11976 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11976, agent11976]

noncomputable def paperAgent11977 : AgentParameters :=
  { agent11977 with charge := (252439573 / 200000000000 : ℝ) }

theorem agent_is_repriced11977 : agent11977 =
    BstLean.Part265.agentRepriced 11977 world11977 paperAgent11977 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11977, agent11977]

noncomputable def paperAgent11978 : AgentParameters :=
  { agent11978 with charge := (630967639 / 500000000000 : ℝ) }

theorem agent_is_repriced11978 : agent11978 =
    BstLean.Part265.agentRepriced 11978 world11978 paperAgent11978 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11978, agent11978]

noncomputable def paperAgent11979 : AgentParameters :=
  { agent11979 with charge := (315418237 / 250000000000 : ℝ) }

theorem agent_is_repriced11979 : agent11979 =
    BstLean.Part265.agentRepriced 11979 world11979 paperAgent11979 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11979, agent11979]

noncomputable def paperAgent11980 : AgentParameters :=
  { agent11980 with charge := (1261410879 / 1000000000000 : ℝ) }

theorem agent_is_repriced11980 : agent11980 =
    BstLean.Part265.agentRepriced 11980 world11980 paperAgent11980 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11980, agent11980]

noncomputable def paperAgent11981 : AgentParameters :=
  { agent11981 with charge := (315287267 / 250000000000 : ℝ) }

theorem agent_is_repriced11981 : agent11981 =
    BstLean.Part265.agentRepriced 11981 world11981 paperAgent11981 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11981, agent11981]

noncomputable def paperAgent11982 : AgentParameters :=
  { agent11982 with charge := (315221879 / 250000000000 : ℝ) }

theorem agent_is_repriced11982 : agent11982 =
    BstLean.Part265.agentRepriced 11982 world11982 paperAgent11982 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11982, agent11982]

noncomputable def paperAgent11983 : AgentParameters :=
  { agent11983 with charge := (1260626223 / 1000000000000 : ℝ) }

theorem agent_is_repriced11983 : agent11983 =
    BstLean.Part265.agentRepriced 11983 world11983 paperAgent11983 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11983, agent11983]

end BstLean.Part281
